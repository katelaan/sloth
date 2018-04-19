import copy
import collections
from time import time
from datetime import timedelta
# TODO: Use timeit.default_timer for platform-independent timing? Or use a CPU clock timer? (Does the later work properly with the C++ subprocess? Have to try)

from . import utils

class TimingException(utils.SlothException):
    """Root exception for the timing module.

    All exceptions thrown by this module should be subclasses of this exception.
    """

class UndefinedMetaAccess(TimingException):
    """Raised upon access of event attribute that has not been set"""

class EventType:
    num_events = 9
    Start, StartSolver, StartSmt, EndSmt, EndSolver, Sat, Unsat, Error, Mark = range(num_events)

class Event:
    """Represents a single timed event in the event log.

    When logging an event through log.add, the timestamp attribute is
    automatically set to the current time.
    """

    def __init__(self, timestamp, event_type, **kwargs):
        self.timestamp = timestamp
        self.event_type = event_type
        self.kwargs = kwargs

    def __repr__(self):
        kws = ', '.join(['{} = {}'.format(*i) for i in self.kwargs.items()])
        if kws: kws = ', '+kws
        return 'Event({}, {}{})'.format(self.timestamp, self.event_type, kws)

    def __getattr__(self, name):
        try:
            return self.kwargs[name]
        except KeyError:
            raise UndefinedMetaAccess('Access of undefined event attribute ' + name)


class EventLog:
    """Represents a backlog of timed events."""

    def __init__(self):
        self.events = collections.deque()

    def __call__(self, event_type, **kwargs):
        self.events.append(
            Event(time(), event_type, **kwargs)
        )

    def __iter__(self):
        events = collections.deque(self.events)
        while events:
            assert(events[0].event_type == EventType.Start)
            res = [events.popleft()]
            while events and events[0].event_type != EventType.Start:
                res.append(events.popleft())
            yield res

log = EventLog()


def process_events(f):
    for event in log:
        yield f(event)

def _time_if_type(event, type_):
    if event.event_type == type_:
        return event.timestamp
    else:
        return None

def eval_stats(ls):
    assert(ls[0].event_type == EventType.Start)
    start = ls[0]
    status = '?'
    mark = ''
    work_list = ls[1:]
    num_calls = 0
    start_time = start.timestamp
    end_time = None
    smt_time = 0
    print(start.benchmark)
    while len(work_list) >= 4:
        times = [_time_if_type(event, type_)
                 for event, type_ in zip(
                         work_list[:4],
                         [EventType.StartSolver, EventType.StartSmt,
                          EventType.EndSmt, EventType.EndSolver]
                 )]
        if not any(t is None for t in times):
            num_calls += 1
            smt_call_time = times[2] - times[1]
            print('SMT call took {}'.format(smt_call_time))
            smt_time += smt_call_time
            end_time = times[3]
        work_list = work_list[4:]
    while work_list:
        if work_list[0].event_type == EventType.Error:
            status = 'ERR'
        elif work_list[0].event_type == EventType.Sat:
            status = 'SAT'
        elif work_list[0].event_type == EventType.Unsat:
            status = 'UNSAT'
        elif work_list[0].event_type == EventType.Mark:
            mark = work_list[0].mark
        work_list = work_list[1:]

    if end_time is None:
        total_time = 'n/a'
    else:
        total_time = '{:10.4f}'.format(end_time - start_time)
    if smt_time == 0:
        smt_time = 'n/a'
    else:
        smt_time = '{:8.4f}'.format(smt_time)

    return [start.benchmark,
            start.encoder,
            total_time,
            smt_time,
            '{:10d}'.format(num_calls),
            '{:>6}'.format(status),
            mark]

def print_solver_stats():
    print(solver_stats())

def solver_stats():
    stats = list(process_events(eval_stats))
    headings = ['Benchmark', 'Encoder', 'Total time', 'Smt time', '#Smt calls', 'Status', 'Failed']
    if utils.seq_exists(lambda e : e[-1] != '', stats):
        last = len(headings)
    else:
        last = -1

    maxlens = [len(h) for h in headings]
    for stat in stats:
        for i,s in enumerate(stat):
            maxlens[i] = max(maxlens[i], len(s))
    maxlens = maxlens[:last]
    #return str(timedelta(seconds=elapsed))
    field_formats = ['{:'+str(l)+'}' for l in maxlens]
    format_string = ' | '.join(field_formats)

    lines = []
    lines.append(format_string.format(*headings))
    for stat in stats:
        lines.append(format_string.format(*stat))
    return '\n'.join(lines)
