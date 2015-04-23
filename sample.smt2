; http://rise4fun.com/Z3/OS5S

(declare-datatypes () ((BaseTerm (nil)
                                 (int (ival Int))
                                 (flt (fval Real))
                                 (lst (hd BaseTerm) (tl BaseTerm))
                                 (tpl (tval BaseTermList))
                                 (atm (aval IntList))
                                 (bin (bval BitList)))
                        (BaseTermList (tnil)
                                      (tcons (thd BaseTerm) (ttl BaseTermList)))
                        (IntList (inil)
                                 (icons (ihd Int) (itl IntList)))
                        (BitList (bnil) (bcons (bhd (_ BitVec 1)) (btl BitList)))))
                        
(declare-datatypes () ((FunTerm (fun1 (f1val (Array BaseTerm BaseTerm))))))
(declare-datatypes () ((Term (base (btval BaseTerm))
                             (mmap (mval (Array BaseTerm BaseTerm)))
                             (func (fnval FunTerm)))))
                             
(declare-const x1 Term)
(declare-const x2 Term)

(declare-const a2 (Array BaseTerm BaseTerm))
(assert (= (select a2 (atm (icons 111 (icons 107 inil)))) (atm (icons 111 (icons 107 inil)))))
(assert (= (select a2 (flt 3.1400000000)) (tpl tnil)))
(assert (= (select a2 (int 2)) (int 2)))
(assert (= (select a2 (int 1)) (int 1)))
(assert (= x1 (mmap a2)))
(assert (is-func x2))
(assert (= (select (f1val (fnval x2)) (int 42)) (atm (icons 111 (icons 107 inil)))))

(check-sat)
(get-model)
