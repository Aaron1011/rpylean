from rpython.rlib.parsing.ebnfparse import parse_ebnf, make_parse_function
import py

from rpylean import RPYLEAN_DIR

grammar = py.path.local(RPYLEAN_DIR).join("grammar.txt").read("rt")
try:
    regexs, rules, ToAST = parse_ebnf(grammar)
    _parse = make_parse_function(regexs, rules, eof=True)
except Exception as e:
    print "Caught:"
    print e.nice_error_message()
    print e
