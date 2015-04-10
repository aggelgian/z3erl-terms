#!/usr/bin/env python
# -*- coding: utf-8 -*-

from z3 import *

T = Datatype('Term')
TL = Datatype('TList')
IL = Datatype('IList')
# Term
T.declare('int', ('ival', IntSort()))
T.declare('real', ('rval', RealSort()))
T.declare('lst', ('lval', TL))
T.declare('tpl', ('tval', TL))
T.declare('atm', ('aval', IL))
# TermList
TL.declare('nil')
TL.declare('cons', ('hd', T), ('tl', TL))
# IntList
IL.declare('anil')
IL.declare('acons', ('ahd', IntSort()), ('atl', IL))
# Return Datatypes
T, TL, IL = CreateDatatypes(T, TL, IL)
