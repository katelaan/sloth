class ResultState:
    """Encapsulates the result of running z3.

    Contains fields `s` (reference to the :class:`z3.Solver`),
    `model` (the z3 Model),
    `encoding` (the input to z3)
    """

    def __init__(self, s, model, encoding):
        self.s = s
        self.model = model
        self.encoding = encoding

    def is_success(self):
        return self.model is not None

class EncoderState(object):
    """For bookkeeping reasons, :class:`SlAst` objects have evolving
internal state.

    This class defines the states through which :class:`SlAst`
    objects can go.`

    """
    Initial, PreprocFinished, UnfoldingComputed, EncodingAssigned = range(4)
