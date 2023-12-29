#!/usr/bin/env python3

import os.path

import time
from datetime import timedelta
import logging
import argparse
import requests
from requests.adapters import HTTPAdapter, Retry
import xml.etree.ElementTree
import copy
import threading
import math
import re

from termcolor import colored

logging.VERBOSE = (logging.INFO + logging.DEBUG) // 2

logger = logging.getLogger('dash-proxy')

ns = {'mpd':'urn:mpeg:dash:schema:mpd:2011'}


class Formatter(logging.Formatter):
    def __init__(self, fmt=None, datefmt=None):
        super(Formatter, self).__init__(fmt, datefmt)

    def format(self, record):
        color = None
        if record.levelno == logging.ERROR:
            color = 'red'
        if record.levelno == logging.INFO:
            color = 'green'
        if record.levelno == logging.WARNING:
            color = 'yellow'
        if color:
            return colored(record.msg, color)
        else:
            return record.msg


ch = logging.StreamHandler()
ch.setLevel(logging.DEBUG)
formatter = Formatter()
ch.setFormatter(formatter)
logger.addHandler(ch)

def baseUrl(url):
    # remove query first - parameters can contain '/' too
    idx = url.rfind('?')
    if idx >= 0:
        url = url[:idx]

    idx = url.rfind('/')
    if idx >= 0:
        return url[:idx+1]
    else:
        return url

def ISO8601DurationSeconds(duration: str) -> float:
    a_float = '([0-9]+(\.[0-9]+)?)'
    maybe = lambda suffix: f'({a_float}{suffix})?'
    # reject [Y]ears and [M]onths because their time varies (also assume no leap seconds)
    pattern = f'P{maybe("D")}T{maybe("H")}{maybe("M")}{maybe("S")}'
    match = re.match(pattern, duration)
    if not match:
        raise RuntimeError(f'Invalid duration: {duration}')
    (d, h, m, s) = match.group(2,5,8,11)
    s = float(s or '0')
    s += 60 * float(m or '0')
    s += 60 * 60 * float(h or '0')
    s += 24 * 60 * 60 * float(d or '0')
    return s

class RepAddr(object):
    def __init__(self, period_idx, adaptation_set_idx, representation_idx):
        self.period_idx = period_idx
        self.adaptation_set_idx = adaptation_set_idx
        self.representation_idx = representation_idx

    def __str__(self):
        return 'Representation (period=%d adaptation-set=%d representation=%d)' % (self.period_idx, self.adaptation_set_idx, self.representation_idx)


class MpdLocator(object):
    def __init__(self, mpd):
        self.mpd = mpd

    def representation(self, rep_addr):
        return self.adaptation_set(rep_addr).findall('mpd:Representation', ns)[rep_addr.representation_idx]

    def segment_template(self, rep_addr):
        rep_st = self.representation(rep_addr).find('mpd:SegmentTemplate', ns)
        if rep_st is not None:
            return rep_st
        else:
            return self.adaptation_set(rep_addr).find('mpd:SegmentTemplate', ns)

    def segment_timeline(self, rep_addr):
        return self.segment_template(rep_addr).find('mpd:SegmentTimeline', ns)

    def adaptation_set(self, rep_addr):
        return self.period(rep_addr).findall('mpd:AdaptationSet', ns)[rep_addr.adaptation_set_idx]

    def periods(self):
        return self.mpd.findall('mpd:Period', ns)

    def period(self, rep_addr):
        return self.periods()[rep_addr.period_idx]

    def period_start(self, rep_addr):
        start = 0.0
        # 3.10.2.2.3. Period Information
        period = self.period(rep_addr)
        if 'start' in period.attrib:
            # - If the attribute @start is present in the Period, then PSwc[i] is the value of this attribute
            #   minus the value of @start of the first Period.
            if rep_addr.period_idx != 0:
                start = ISO8601DurationSeconds(period.attrib.get('start'))
                first_start = self.period_start(RepAddr(0, 0, 0))
                start -= first_start
            else:
                # The above quote implies that PSwc[i] is relative to @start of 1st Period
                # so for i=0 it will always be 0.0 _by definition_ (@start - @start == 0).
                start = 0.0
        else:
            previous_rep_addr = RepAddr(rep_addr.period_idx - 1) if rep_addr.period_idx != 0 else None
            previous_period = self.period(previous_rep_addr) if previous_rep_addr else None
            # - If the @start attribute is absent, but the previous Period element contains a @duration attribute ...
            if previous_period and 'duration' in previous_duration.attrib:
                previous_duration = ISO8601DurationSeconds(previous_duration.attrib.get('duration'))
                previous_start = self.period_start(previous_rep_addr)
                # ... then the start time of the Period is the sum of the start time of the previous
                # Period PSwc[i] and the value of the attribute @duration of the previous Period.
                start = previous_start + previous_duration
            else:
                # And if there is neither @start nor previous @duration then what? Malformed MPD?
                pass
        return start

    def period_end(self, rep_addr):
        end = 0.0
        period_count = len(self.periods())
        # 3.10.2.2.3. Period Information
        # If the Period is the last one in the MPD, the time PEwc[i] is obtained as
        if rep_addr.period_idx == period_count - 1:
            if 'mediaPresentationDuration' in self.mpd.attrib:
                # the Media Presentation Duration MPDur, with MPDur the value of MPD@mediaPresentationDuration if present
                end = ISO8601DurationSeconds(self.mpd.attrib.get('mediaPresentationDuration'))
            else:
                # or the sum of PSwc[i] of the last Period and the value of Period@duration of the last Period.
                period = self.period(rep_addr)
                start = self.period_start(rep_addr)
                duration = ISO8601DurationSeconds(period.attrib.get('duration')) # implicitly required to be present
                end = start + duration
        else:
            # the time PEwc[i] is obtained as the Period start time of the next Period, i.e. PEwc[i] = PSwc[i+1].
            end = self.period_start(RepAddr(rep_addr.period_idx + 1))
        return end

class HasLogger(object):
    def verbose(self, msg):
        self.logger.log(logging.VERBOSE, msg)

    def info(self, msg):
        self.logger.log(logging.INFO, msg)

    def debug(self, msg):
        self.logger.log(logging.DEBUG, msg)

    def warning(self, msg):
        self.logger.log(logging.WARNING, msg)

    def error(self, msg):
        self.logger.log(logging.ERROR, msg)

class DashProxy(HasLogger):
    retry_interval = 10

    def __init__(self, mpd, output_dir, download, save_mpds=False, bandwidth_limit=0):
        self.logger = logger

        self.mpd = mpd
        self.output_dir = output_dir
        self.download = download
        self.save_mpds = save_mpds
        self.i_refresh = 0
        self.bandwidth_limit = bandwidth_limit

        self.downloaders = {}

    def run(self):
        logger.log(logging.INFO, 'Running dash proxy for stream %s. Output goes in %s' % (self.mpd, self.output_dir))
        self.refresh_mpd()

    def refresh_mpd(self, after=0, error_cnt=0):
        self.i_refresh += 1
        if after>0:
            time.sleep(after)

        r = requests.get(self.mpd)
        if r.status_code < 200 or r.status_code >= 300:
            error_cnt += 1
            logger.log(logging.WARNING, 'Cannot GET the MPD. Server returned %s. Retrying after %ds' % (r.status_code, self.retry_interval))
            if error_cnt < 10:
                self.refresh_mpd(after=self.retry_interval, error_cnt=error_cnt)
            else:
                logger.log(logging.WARNING, 'Tried %d times. Giving up.' % error_cnt)

        xml.etree.ElementTree.register_namespace('', ns['mpd'])
        mpd = xml.etree.ElementTree.fromstring(r.text)
        # save original
        content = xml.etree.ElementTree.tostring(mpd, encoding="utf-8").decode("utf-8")
        os.makedirs(self.output_dir, exist_ok=True)
        with open(self.output_dir + '/manifest.mpd.orig', 'w') as f:
            f.write(content)

        self.handle_mpd(mpd)

    def get_base_url(self, mpd):
        base_url = baseUrl(self.mpd)
        location = mpd.find('mpd:Location', ns)
        if location is not None:
            base_url = baseUrl(location.text)
        baseUrlNode = mpd.find('mpd:BaseUrl', ns)
        if baseUrlNode:
            if baseUrlNode.text.startswith('http://') or baseUrlNode.text.startswith('https://'):
                base_url = baseUrl(baseUrlNode.text)
            else:
                base_url = base_url + baseUrlNode.text
        return base_url

    def handle_mpd(self, mpd):
        original_mpd = copy.deepcopy(mpd)

        periods = original_mpd.findall('mpd:Period', ns)
        logger.log(logging.INFO, 'mpd=%s' % (periods,))
        logger.log(logging.VERBOSE, 'Found %d periods choosing the 1st one' % (len(periods),))
        period = periods[0]
        for as_idx, adaptation_set in enumerate( period.findall('mpd:AdaptationSet', ns) ):
            ep = adaptation_set.find('mpd:EssentialProperty', ns)
            if ep is not None and ep.attrib.get('schemeIdUri') == 'http://dashif.org/guidelines/trickmode' and ep.attrib.get('value') == '1':
                period.remove(adaptation_set)
            else:
                max_rep_idx = 0
                max_representation = None
                
                for rep_idx, representation in enumerate( adaptation_set.findall('mpd:Representation', ns) ):
                    max_representation = representation
                    max_rep_idx = rep_idx


                    self.verbose('Found representation with id %s' % (max_representation.attrib.get('id', 'UKN'),))
                    rep_addr = RepAddr(0, as_idx, max_rep_idx)
                    #self.ensure_downloader(mpd, rep_addr)
                    thread = threading.Thread(target=self.ensure_downloader, args=(mpd,rep_addr))
                    thread.start()

        self.write_output_mpd(original_mpd)

        minimum_update_period = mpd.attrib.get('minimumUpdatePeriod', '')
        if minimum_update_period:
            # TODO parse minimum_update_period
            self.refresh_mpd(after=10)
        else:
            self.info('VOD MPD. Nothing more to do. Waiting for downloads to finish...')

    def ensure_downloader(self, mpd, rep_addr):
        if rep_addr in self.downloaders:
            self.verbose('A downloader for %s already started' % (rep_addr,))
        else:
            self.info('Starting a downloader for %s' % (rep_addr,))
            downloader = DashDownloader(self, rep_addr)
            self.downloaders[rep_addr] = downloader
            downloader.handle_mpd(mpd, self.get_base_url(mpd))

    def write_output_mpd(self, mpd):
        self.info('Writing the update MPD file')
        content = xml.etree.ElementTree.tostring(mpd, encoding="utf-8").decode("utf-8")
        dest = os.path.join(self.output_dir, 'manifest.mpd')
        os.makedirs(self.output_dir, exist_ok=True)

        with open(dest, 'wt') as f:
            f.write(content)

        if self.save_mpds:
            dest = os.path.join(self.output_dir, 'manifest.{}.mpd'.format(self.i_refresh))
            with open(dest, 'wt') as f:
                f.write(content)


class DashDownloader(HasLogger):
    def __init__(self, proxy, rep_addr):
        self.logger = logger
        self.proxy = proxy
        self.rep_addr = rep_addr
        self.mpd_base_url = ''

        self.initialization_downloaded = False

        self.requests = requests.Session()
        retries = Retry(total=15, backoff_factor=0.1, status_forcelist=[429, 500, 502, 503, 504])
        self.requests.mount('https://', HTTPAdapter(max_retries=retries))

    def handle_mpd(self, mpd, base_url):
        self.mpd_base_url = base_url
        self.mpd = MpdLocator(mpd)

        rep = self.mpd.representation(self.rep_addr)
        segment_template = self.mpd.segment_template(self.rep_addr)
        segment_timeline = self.mpd.segment_timeline(self.rep_addr)

        initialization_template = segment_template.attrib.get('initialization', '')
        if initialization_template and not self.initialization_downloaded:
            self.initialization_downloaded = True
            self.download_template(initialization_template, rep)

        if segment_timeline:
            segments = copy.deepcopy(segment_timeline.findall('mpd:S', ns))
        else:
            # Let's create artificial <SegmentTimeline> with a single <S> to keep further processing unified.
            d = int(segment_template.attrib.get('duration','0'))
            PSwc = self.mpd.period_start(self.rep_addr)
            PEwc = self.mpd.period_end(self.rep_addr)
            # 3.10.2.2.4. Representation Information
            # If the SegmentTemplate@duration is present and the SegmentTemplate.SegmentTimeline is not present, then
            # - NS=1, (so we create 1-element array here)
            # - ts the value of the @timescale attribute
            ts = int(segment_template.attrib.get('timescale','1'))
            S = xml.etree.ElementTree.Element('{urn:mpeg:dash:schema:mpd:2011}S', attrib={
                # t[s] is 0
                't':'0',
                # the d[s] is the value of @duration attribute
                'd': str(d),
                # r[s] is the ceil of (PEwc[i] - PSwc[i] - t[s]/ts)*ts/d[s])
                #                                          ^^^^^^^ this bit can be ignored because t[s] is 0
                'r': str(math.ceil((PEwc - PSwc) * ts / d))
            })
            # self.verbose("There is no timeline, created artificial one: <S %s>" % (" ".join([f'{k}="{v}"' for k,v in S.attrib.items()])))
            segments = [S]
            # new empty <SegmentTimeline> needed below
            segment_timeline = xml.etree.ElementTree.Element('{urn:mpeg:dash:schema:mpd:2011}SegmentTimeline')

        idx = 0
        total=0
        for segment in segments:
            duration = int( segment.attrib.get('d', '0') )
            repeat = int( segment.attrib.get('r', '0') )
            idx = idx + 1
            total += duration * (repeat + 1)
            for _ in range(0, repeat):
                elem = xml.etree.ElementTree.Element('{urn:mpeg:dash:schema:mpd:2011}S', attrib={'d':str(duration)})
                segment_timeline.insert(idx, elem)
                self.verbose('appending a new elem')
                idx = idx + 1

        media_template = segment_template.attrib.get('media', '')
        timescale = int(segment_template.attrib.get('timescale','1'))
        startNumber = int(segment_template.attrib.get('startNumber','0'))
        next_time = 0
        total_info = '/' + str(timedelta(seconds=round(total / timescale))) + ' '
        for index, segment in enumerate(segment_timeline.findall('mpd:S', ns)):
            current_time = int(segment.attrib.get('t', '-1'))
            if current_time == -1:
                segment.attrib['t'] = str(next_time)
            else:
                next_time = current_time
            next_time += int(segment.attrib.get('d', '0'))
            self.download_template(media_template, rep, segment, info=str(timedelta(seconds=round(next_time / timescale))) + total_info, index=index + startNumber)

    def download_template(self, template, representation=None, segment=None, info='', index=None):
        dest = self.render_template(template, representation, segment, index)
        dest_url = self.full_url(dest)
        dest = dest.split('?')[0]
        dest = os.path.join(self.proxy.output_dir, dest)
        if os.path.isfile(dest):
            self.verbose('%sskipping %s already exists' % (info, dest))
        else:
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            self.info('%srequesting %s from %s' % (info, dest, dest_url))
            try:
                with self.requests.get(dest_url, stream=True) as r:
                    r.raise_for_status()
                    if r.status_code >= 200 and r.status_code < 300:
                        with open(dest, 'xb') as f:
                            for chunk in r.iter_content(chunk_size=8196): 
                                f.write(chunk)
                    else:
                        self.error('cannot download %s server returned %d' % (dest_url, r.status_code))
            except Exception as e:
                self.error(e)

    def render_template(self, template, representation=None, segment=None, index=None):
        template = template.replace('$RepresentationID$', '{representation_id}')
        template = template.replace('$Number$', '{number}')
        template = re.sub('\$Number%([0-9]*)d\$', '{number:\\1d}', template)
        template = template.replace('$Time$', '{time}')

        args = {}
        if representation is not None:
            args['representation_id'] = representation.attrib.get('id', '')
        if segment is not None:
            args['time'] = segment.attrib.get('t', '')
        if index is not None:
            args['number'] = index

        template = template.format(**args)
        return template

    def full_url(self, dest):
        return self.mpd_base_url + dest # TODO remove hardcoded arrd

def run(args):
    logger.setLevel(logging.VERBOSE if args.v else logging.INFO)
    proxy = DashProxy(mpd=args.mpd,
                  output_dir=args.o,
                  download=args.d,
                  save_mpds=args.save_individual_mpds,
                  bandwidth_limit=args.b)
    return proxy.run()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mpd")
    parser.add_argument("-v", action="store_true")
    parser.add_argument("-d", action="store_true")
    parser.add_argument("-o", default='.')
    parser.add_argument("-b", default=0)
    parser.add_argument("--save-individual-mpds", action="store_true")
    args = parser.parse_args()

    run(args)

if __name__ == '__main__':
    main()
