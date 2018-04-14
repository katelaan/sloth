import sys

assert sys.version_info >= (3, 5), 'sloth requires python >= 3.5'

from .api import *

if backend is None:
    # API initialization wasn't executed or otherwise failed.
    # Because normal operation depends on having an active backend,
    # we abort immediately.
    from .utils import utils
    raise utils.SlothException('Backend initialization failed')
