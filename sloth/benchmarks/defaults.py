from ..backend import backends, struct

predef_structs = struct.make_predef_structs(backends.QuantifiedBackend)
predef_lambda_structs = struct.make_predef_structs(backends.LambdaBackend)
list_struct, dlist_struct, tree_struct, prtree_struct = predef_lambda_structs
