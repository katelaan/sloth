from ..utils import utils

class SmtEncodingException(utils.SlothException):
    """Root exception for the SMT Encoder"""

class SortMixException(SmtEncodingException):
    """Raised when the separating conjunction is applied to arguments of different sorts"""

class PureSpatialMixException(SmtEncodingException):
    """Raised when pure and spatial formulas are mixed below disjunction or negation."""

class UndefinedStructException(SmtEncodingException):
    """Exception raised when the un-encoded input refers to a data structure that
    is not defined."""

debug_encoding_enabled = True
