#!/usr/bin/env python
# -*- coding: utf-8 -*-

from z3 import *

T = Datatype('Term')
TL = Datatype('TList')
IL = Datatype('IList')
BvL = Datatype('BvList')
# Term
T.declare('nil')
T.declare('int', ('ival', IntSort()))
T.declare('flt', ('fval', RealSort()))
T.declare('lst', ('hd', T), ('tl', T))
T.declare('tpl', ('tval', TL))
T.declare('atm', ('aval', IL))
T.declare('bit', ('bval', BvL))
# TermList
TL.declare('tnil')
TL.declare('tcons', ('thd', T), ('ttl', TL))
# IntList
IL.declare('inil')
IL.declare('icons', ('ihd', IntSort()), ('itl', IL))
# BitVectorList
BvL.declare('vnil')
BvL.declare('vcons', ('vhd', BitVecSort(1)), ('vtl', BvL))
# Return Datatypes
T, TL, IL, BvL = CreateDatatypes(T, TL, IL, BvL)
