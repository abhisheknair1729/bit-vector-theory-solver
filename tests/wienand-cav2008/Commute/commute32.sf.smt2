(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun var2 () (_ BitVec 32))
(declare-fun var3 () (_ BitVec 32))
(declare-fun var4 () (_ BitVec 32))
(declare-fun var8 () (_ BitVec 96))
(declare-fun var10 () (_ BitVec 96))
(declare-fun var12 () (_ BitVec 96))
(declare-fun var14 () (_ BitVec 96))
(declare-fun var16 () (_ BitVec 96))
(declare-fun var20 () (_ BitVec 96))
(declare-fun var28 () (_ BitVec 96))
(declare-fun var29 () (_ BitVec 1))
(declare-fun var30 () (_ BitVec 1))
(declare-fun var31 () (_ BitVec 1))
(declare-fun property () (_ BitVec 1))
(declare-fun Fresh__0 () (_ BitVec 1))
(declare-fun Fresh__1 () (_ BitVec 1))
(assert (= var8 (concat (_ bv0 64) var4)))
(assert (= var10 (concat (_ bv0 64) var3)))
(assert (= var12 (concat (_ bv0 64) var2)))
(assert (= var14 (bvmul var10 var12)))
(assert (= var16 (bvmul var8 var14)))
(assert (= var20 (bvmul var8 var10)))
(assert (= var28 (bvmul var12 var20)))
(assert (= (= Fresh__0 (_ bv1 1)) (= var16 var28)))
(assert (= var29 Fresh__0))
(assert (= var30 (bvnot (_ bv1 1))))
(assert (= var31 (bvor var29 var30)))
(assert (= property ((_ extract 0 0) var31)))
(assert (= (= Fresh__1 (_ bv1 1)) (= property (_ bv0 1))))
(assert (= (_ bv1 1) Fresh__1))
(check-sat)
(exit)
