import traceback
import inspect

def print_info(obj):
    print("{} : {}".format(obj, obj.__class__))

def print_stack(with_context = True, skip_first = True, num_frames = 100):
    first = 2 if skip_first else 1
    last = min(len(inspect.stack()), num_frames+first)

    for f in inspect.stack()[first:last]:
        print("{1}:{2} {3}".format(*f))
        if with_context:
            stripped = ["  "+s.lstrip() for s in f[4]]
            print("".join(stripped)[0:-1])


def print_stack_trace():
    """Print the current stack trace"""
    for line in traceback.format_stack():
        print(line.strip())
