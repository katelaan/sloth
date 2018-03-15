from ..backend import backends, symbols

predef_structs = symbols.make_predef_structs(backends.QuantifiedBackend)
list_struct, dlist_struct, tree_struct, prtree_struct = predef_structs
predef_lambda_structs = symbols.make_predef_structs(backends.LambdaBackend)
