import logging

import __main__ as main
from .. import config

DEBUG = logging.DEBUG
INFO = logging.INFO
WARN = logging.WARN
ERROR = logging.ERROR

if hasattr(main, '__file__'):
    # Use normal logging
    def set_level(lvl):
        # TODO: Add source file/line number again? Since we're now always calling the log functions from this module, it's no longer possible to use logging's own capabilities for that
        #logging.basicConfig(format='%(asctime)s [%(filename)s:%(lineno)d]: %(message)s', level=lvl)
        logging.basicConfig(format='%(asctime)s: %(message)s', level=lvl)
        # TODO: The following call shouldn't be necessary, but at least in doctest, for some reason basicConfig doesn't affect the root logger's effective log level
        logging.getLogger("").setLevel(lvl)
        #print("Set log level to {}".format(logging.getLogger("").getEffectiveLevel()))

    def debug(*args):
        logging.debug(*args)
    def info(*args):
        logging.info(*args)
    def warn(*args):
        logging.warn(*args)
    def error(*args):
        logging.error(*args)

    def debug_logging_enabled():
        """Return true iff debug logging is enabled for the root logger"""
        return logging.getLogger("").isEnabledFor(DEBUG)
else:
    level = logging.INFO

    # Interactive mode => Print instead
    def set_level(lvl):
        global level
        level = lvl

    def print_if(lvl, *args):
        if lvl >= level:
            print(", ".join(args))

    def debug(*args):
        print_if(DEBUG, *args)
    def info(*args):
        print_if(INFO, *args)
    def warn(*args):
        print_if(WARN, *args)
    def error(*args):
        print_if(ERROR, *args)

    def debug_logging_enabled():
        return level <= logging.DEBUG

# Set default log level
set_level(config.DEFAULT_LOG_LEVEL)
