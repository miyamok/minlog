;; 2020-12-19.  mtr.scm.  Metric spaces and and their completions.

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (libload "rea.scm")
;; (set! COMMENT-FLAG #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Metric spaces
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; d will be used for the metric
(remove-var-name "d")

(add-pvar-name "X" (make-arity (py "alpha")))
(add-var-name "u" (py "alpha"))
(add-var-name "d" (py "alpha=>alpha=>rea"))

(add-ids
 (list (list "Mtr" (make-arity (py "alpha=>alpha=>rea"))))
 '("allnc u(X^ u -> d u u===0) ->
    allnc u,u0(X^ u -> X^ u0 -> d u u0===d u0 u) ->
    allnc u,u0,u1(X^ u -> X^ u0 -> X^ u1 -> d u u1<<=(d u u0)+(d u0 u1)) ->
    Mtr d"
   "MtrIntro"))

;; (pp "MtrIntro")

;; allnc d(
;;  allnc u(X^ u -> d u u===0) -> 
;;  allnc u,u0(X^ u -> X^ u0 -> d u u0===d u0 u) -> 
;;  allnc u,u0,u1(X^ u -> X^ u0 -> X^ u1 -> d u u1<<=d u u0+d u0 u1) -> 
;;  (Mtr (cterm (u^) X^ u^))d)

;; Properties of metric spaces.

;; MtrReal
(set-goal "allnc d(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
 allnc u1,u2(X^ u1 -> X^ u2 -> Real(d u1 u2)))")
(assume "d" "dSym" "u1" "u2" "Xu1" "Xu2")
(inst-with-to "dSym" (pt "u1") (pt "u2") "Xu1" "Xu2" "EqHyp")
(realproof)
;; Proof finished.
;; (cdp)
(save "MtrReal")

;; MtrNNeg
(set-goal "allnc d(
 allnc u(X^ u -> d u u===0) ->
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) -> 
 allnc u1,u2(X^ u1 -> X^ u2 -> 0<<=d u1 u2))")
(assume "d" "dZero" "dSym" "dTriang" "u1" "u2" "Xu1" "Xu2")
(assert "Real(d u1 u2)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu2")
(assume "Rdu1u2")
(assert "Real(d u2 u1)")
(use "MtrReal")
(use "dSym")
(use "Xu2")
(use "Xu1")
(assume "Rdu2u1")
(assert "0<<=(RealPlus 1 1)*d u1 u2")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealOneTimes")
(use "RealLeTrans" (pt "d u1 u2+d u2 u1"))
(simpreal (pf "0===d u1 u1"))
(use "dTriang")
(use "Xu1")
(use "Xu2")
(use "Xu1")
(use "RealEqSym")
(use "dZero")
(use "Xu1")
;; ?^24:d u1 u2+d u2 u1<<=d u1 u2+d u1 u2
(use "RealLeMonPlus")
(use "RealLeRefl")
(use "Rdu1u2")
(simpreal "dSym")
(use "RealLeRefl")
(use "Rdu1u2")
(use "Xu1")
(use "Xu2")
(autoreal)
;; ?^15:0<<=RealPlus 1 1*d u1 u2 -> 0<<=d u1 u2
(assume "0<=2d")
(use "RealLeTrans" (pt "(1#2)*(2*d u1 u2)"))
(simpreal (pf "0===RealTimes(1#2)0"))
(use "RealLeMonTimes")
(use "RatNNegToRealNNeg")
(use "Truth")
(use "0<=2d")
(use "RealEqRefl")
(use "RealRat")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "MtrNNeg")

;; MtrUB
(set-goal "allnc d(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3+ ~(d u2 u3)<<=d u1 u2))")
(assume "d" "dSym" "dTriang" "u1" "u2" "u3" "Xu1" "Xu2" "Xu3")
(assert "Real(d u1 u2)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu2")
(assume "Rdu1u2")
(assert "Real(d u2 u3)")
(use "MtrReal")
(use "dSym")
(use "Xu2")
(use "Xu3")
(assume "Rdu2u3")
;; ?^14:d u1 u3+ ~(d u2 u3)<<=d u1 u2
(use "RealLeTrans" (pt "d u1 u2+d u2 u3+ ~(d u2 u3)"))
(use "RealLeMonPlus")
(use "dTriang")
(use "Xu1")
(use "Xu2")
(use "Xu3")
(use "RealLeRefl")
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "MtrUB")

;;  MtrUBAbsL
(set-goal "allnc d(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> 
                abs(d u1 u3+ ~(d u2 u3))<<=d u1 u2))")
(assume "d" "dSym" "dTriang" "u1" "u2" "u3" "Xu1" "Xu2" "Xu3")
(assert "Real(d u1 u2)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu2")
(assume "Rdu1u2")
(assert "Real(d u2 u3)")
(use "MtrReal")
(use "dSym")
(use "Xu2")
(use "Xu3")
(assume "Rdu2u3")
(assert "Real(d u1 u3)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu3")
(assume "Rdu1u3")
(use "RealLeAbs")
;; 21,22
;; ?^21:d u1 u3+ ~(d u2 u3)<<=d u1 u2
(use "MtrUB")
(use "dSym")
(use "dTriang")
(use "Xu1")
(use "Xu2")
(use "Xu3")
;; ?^22:~(d u1 u3+ ~(d u2 u3))<<=d u1 u2
(assert "Real(d u2 u1)")
(use "MtrReal")
(use "dSym")
(use "Xu2")
(use "Xu1")
(assume "Rdu2u1")
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
(simpreal "RealPlusComm")
(simpreal (pf "d u1 u2===d u2 u1"))
(use "MtrUB")
(use "dSym")
(use "dTriang")
(use "Xu2")
(use "Xu1")
(use "Xu3")
(use "dSym")
(use "Xu1")
(use "Xu2")
(autoreal)
;; Proof finished.
;; (cdp)
(save "MtrUBAbsL")

;; MtrUBAbsR
(set-goal "allnc d(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> 
                abs(d u1 u2+ ~(d u1 u3))<<=d u2 u3))")
(assume "d" "dSym" "dTriang" "u1" "u2" "u3" "Xu1" "Xu2" "Xu3")
(assert "Real(d u1 u2)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu2")
(assume "Rdu1u2")
(assert "Real(d u2 u3)")
(use "MtrReal")
(use "dSym")
(use "Xu2")
(use "Xu3")
(assume "Rdu2u3")
(assert "Real(d u1 u3)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu3")
(assume "Rdu1u3")
(assert "Real(d u2 u1)")
(use "MtrReal")
(use "dSym")
(use "Xu2")
(use "Xu1")
(assume "Rdu2u1")
(simpreal (pf "d u1 u2===d u2 u1"))
(simpreal (pf "d u1 u3===d u3 u1"))
(use "MtrUBAbsL")
(use "dSym")
(use "dTriang")
(use "Xu2")
(use "Xu3")
(use "Xu1")
(use "dSym")
(use "Xu1")
(use "Xu3")
(use "dSym")
(use "Xu1")
(use "Xu2")
;; Proof finished.
;; (cdp)
(save "MtrUBAbsR")

;;  MtrLB
(set-goal "allnc d(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) -> 
  allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u2<<=d u1 u3+ d u2 u3))")
(assume "d" "dSym" "dTriang" "u1" "u2" "u3" "Xu1" "Xu2" "Xu3")
(assert "Real(d u1 u2)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu2")
(assume "Rdu1u2")
(assert "Real(d u1 u3)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu3")
(assume "Rdu1u3")
(simpreal (pf "d u2 u3===d u3 u2"))
(use "dTriang")
(use "Xu1")
(use "Xu3")
(use "Xu2")
(use "dSym")
(use "Xu2")
(use "Xu3")
;; Proof finished.
;; (cdp)
(save "MtrLB")

;; MtrUBAbsQuad
(set-goal "allnc d(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) -> 
 allnc u1,u2,u3,u4(X^ u1 -> X^ u2 -> X^ u3 -> X^ u4 -> 
  abs(d u1 u4+ ~(d u2 u3))<<=d u1 u2+d u3 u4))")
(assume "d" "dSym" "dTriang" "u1" "u2" "u3" "u4" "Xu1" "Xu2" "Xu3" "Xu4")
(assert "Real(d u1 u2)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu2")
(assume "Rdu1u2")
(assert "Real(d u1 u4)")
(use "MtrReal")
(use "dSym")
(use "Xu1")
(use "Xu4")
(assume "Rdu1u4")
(assert "Real(d u2 u3)")
(use "MtrReal")
(use "dSym")
(use "Xu2")
(use "Xu3")
(assume "Rdu2u3")
(assert "Real(d u3 u4)")
(use "MtrReal")
(use "dSym")
(use "Xu3")
(use "Xu4")
(assume "Rdu3u4")
(assert "Real(d u2 u4)")
(use "MtrReal")
(use "dSym")
(use "Xu2")
(use "Xu4")
(assume "Rdu2u4")
(use "RealLeTrans" (pt "abs(d u1 u4+ ~(d u2 u4))+abs(d u2 u4+ ~(d u2 u3))"))
(use "RealLeAbsMinus")
(autoreal)
(use "RealLeMonPlus")
(use "MtrUBAbsL")
(use "dSym")
(use "dTriang")
(use "Xu1")
(use "Xu2")
(use "Xu4")
;; ?^39:abs(d u2 u4+ ~(d u2 u3))<<=d u3 u4
(simpreal (pf "d u3 u4===d u4 u3"))
(use "MtrUBAbsR")
(use "dSym")
(use "dTriang")
(use "Xu2")
(use "Xu4")
(use "Xu3")
(use "dSym")
(use "Xu3")
(use "Xu4")
;; Proof finished.
;; (cdp)
(save "MtrUBAbsQuad")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Completion of a metric space
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-var-name "us" (py "nat=>alpha"))
(add-var-name "w" (py "(nat=>alpha)yprod(pos=>nat)"))

(add-ids
 (list (list "MCauchy" (make-arity (py "alpha=>alpha=>rea")
                                   (py "nat=>alpha") (py "pos=>nat"))))
 '("allnc d,us,M(
    allnc p,n,m(M p<=n -> M p<=m -> d(us n)(us m)<<=(1#2**p)) ->
    MCauchy d us M)" "MCauchyIntro"))

;; MCauchyElim
(set-goal "allnc d,us,M(
 MCauchy d us M -> allnc p,n,m(M p<=n -> M p<=m -> d(us n)(us m)<<=(1#2**p)))")
(assume "d" "us""M")
(elim)
(search)
;; Proof finished.
;; (cdp)
(save "MCauchyElim")

;; MCauchyToRCauchy
(set-goal "allnc d,us1,M1,us2,M2,M(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) ->
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
 allnc n X^(us1 n) -> allnc n X^(us2 n) ->
 allnc p M p=M1(PosS p)max M2(PosS p) ->
 MCauchy d us1 M1 -> MCauchy d us2 M2 ->
 RCauchy([n]d(us1 n)(us2 n))M)")
(assume "d" "us1" "M1" "us2" "M2" "M" "dSym" "dTriang" "Xus1" "Xus2"
	"MDef" "Cus1M1" "Cus2M2")
(intro 0)
(ng #t)
(assume "p" "n" "m" "nBd" "mBd")

(assert "allnc n,m Real(d(us1 n)(us2 m))")
(assume "n1" "m1")
(use "MtrReal")
(use "dSym")
(use "Xus1")
(use "Xus2")
(assume "Rus12")

(use "RealLeTrans" (pt "abs(d(us1 n)(us2 n)+ ~(d(us1 n)(us2 m)))+
                        abs(d(us1 n)(us2 m)+ ~(d(us1 m)(us2 m)))"))
(use "RealLeAbsMinus")
(autoreal)
;; ?^14:abs(d(us1 n)(us2 n)+ ~(d(us1 n)(us2 m)))+
;;      abs(d(us1 n)(us2 m)+ ~(d(us1 m)(us2 m)))<<=
;;      (1#2**p)
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 19,20
;; ?^19:abs(d(us1 n)(us2 n)+ ~(d(us1 n)(us2 m)))<<=(1#2**PosS p)
(use "RealLeTrans" (pt "d(us2 n)(us2 m)"))
(use "MtrUBAbsR")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus2")
(use "Xus2")
;; ?^22:d(us2 n)(us2 m)<<=(1#2**PosS p)
(use "MCauchyElim" (pt "M2"))
(use "Cus2M2")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(simp "<-" "MDef")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(simp "<-" "MDef")
(use "mBd")
;; ?^20:abs(d(us1 n)(us2 m)+ ~(d(us1 m)(us2 m)))<<=(1#2**PosS p)
(use "RealLeTrans" (pt "d(us1 n)(us1 m)"))
(use "MtrUBAbsL")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus1")
(use "Xus2")
;; ?^38:d(us1 n)(us1 m)<<=(1#2**PosS p)
(use "MCauchyElim" (pt "M1"))
(use "Cus1M1")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(simp "<-" "MDef")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(simp "<-" "MDef")
(use "mBd")
;; Proof finished.
;; (cdp)
(save "MCauchyToRCauchy")

;; MCauchyToRCauchy1L
(set-goal "allnc d,us,M,u(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) ->
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
 allnc n X^(us n) -> X^ u ->
 MCauchy d us M ->
 RCauchy([n]d(us n)u)M)")
(assume "d" "us" "M" "u" "dSym" "dTriang" "Xus" "Xu" "CusM")
(intro 0)
(ng #t)
(assume "p" "n" "m" "nBd" "mBd")

(assert "allnc n Real(d(us n)u)")
(assume "n1")
(use "MtrReal")
(use "dSym")
(use "Xus")
(use "Xu")
(assume "Rusu")
;; ?^12:abs(d(us n)u+ ~(d(us m)u))<<=(1#2**p)

(use "RealLeTrans" (pt "d(us n)(us m)"))
(use "MtrUBAbsL")
(use "dSym")
(use "dTriang")
(use "Xus")
(use "Xus")
(use "Xu")
;; ?^14:d(us n)(us m)<<=(1#2**p)
(use "MCauchyElim" (pt "M"))
(use "CusM")
(use "nBd")
(use "mBd")
;; Proof finished.
;; (cdp)
(save "MCauchyToRCauchy1L")

;; MCauchyToRCauchy1R
(set-goal "allnc d,us,M,u(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) ->
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
 allnc n X^(us n) -> X^ u ->
 MCauchy d us M ->
 RCauchy([n]d u(us n))M)")
(assume "d" "us" "M" "u" "dSym" "dTriang" "Xus" "Xu" "CusM")
(intro 0)
(ng #t)
(assume "p" "n" "m" "nBd" "mBd")

(assert "allnc n Real(d u(us n))")
(assume "n1")
(use "MtrReal")
(use "dSym")
(use "Xu")
(use "Xus")
(assume "Rusu")
;; ?^12:abs(d u(us n)+ ~(d u(us m)))<<=(1#2**p)

(use "RealLeTrans" (pt "d(us n)(us m)"))
(use "MtrUBAbsR")
(use "dSym")
(use "dTriang")
(use "Xu")
(use "Xus")
(use "Xus")
;; ?^14:d(us n)(us m)<<=(1#2**p)
(use "MCauchyElim" (pt "M"))
(use "CusM")
(use "nBd")
(use "mBd")
;; Proof finished.
;; (cdp)
(save "MCauchyToRCauchy1R")

;; Parallel to Real we introduce MCpl

(add-ids
 (list (list "MCpl" (make-arity (py "alpha=>alpha=>rea")
			        (py "(nat=>alpha)yprod(pos=>nat)"))))
 '("allnc d,w(
   allnc n X^(lft w n) ->  MCauchy d(lft w)(rht w) -> Mon(rht w) -> MCpl d w)"
   "MCplIntro"))

;; (pp "MCplIntro")

;; allnc d,w(
;;  allnc n X^(lft w n) -> 
;;  MCauchy d(lft w)(rht w) -> Mon(rht w) -> (MCpl (cterm (u^) X^ u^))d w)

;; MCplToX
(set-goal "allnc d,w((MCpl (cterm (u^) X^ u^))d w -> allnc n X^(lft w n))")
(assume "d" "w" "Mw")
(elim "Mw")
(search)
;; Proof finished.
;; (cdp)
(save "MCplToX")

;; MCplToMCauchy
(set-goal "allnc d,w((MCpl (cterm (u^) X^ u^))d w -> MCauchy d(lft w)(rht w))")
(assume "d" "w" "Mw")
(elim "Mw")
(search)
;; Proof finished.
;; (cdp)
(save "MCplToMCauchy")

;; MCplToMon
(set-goal "allnc d,w((MCpl (cterm (u^) X^ u^))d w -> Mon(rht w))")
(assume "d" "w" "Mw")
(elim "Mw")
(search)
;; Proof finished.
;; (cdp)
(save "MCplToMon")

;; The following variants will be useful, because their heads will be
;; more often of the form of a given goal.

;; MCplPairToX
(set-goal "allnc d,us,M(
 (MCpl (cterm (u^) X^ u^))d(us pair M) -> allnc n X^(us n))")
(assume "d" "us" "M" "Mw")
(use-with "MCplToX"  (pt "d") (pt "us pair M") "Mw")
;; Proof finished.
;; (cdp)
(save "MCplPairToX")

;; MCplPairToMCauchy
(set-goal "allnc d,us,M(
 (MCpl (cterm (u^) X^ u^))d(us pair M) -> MCauchy d us M)")
(assume "d" "us" "M" "Mw")
(use-with "MCplToMCauchy" (pt "d") (pt "us pair M") "Mw")
;; Proof finished.
;; (cdp)
(save "MCplPairToMCauchy")

;; MCplPairToMon
(set-goal "allnc d,us,M((MCpl (cterm (u^) X^ u^))d(us pair M) -> Mon M)")
(assume "d" "us" "M" "Mw")
(use-with "MCplToMon" (pt "d") (pt "us pair M") "Mw")
;; Proof finished.
;; (cdp)
(save "MCplPairToMon")

;; To make MCpl into a metric space we need  a distance function.

(add-program-constant
 "MCplDist" (py "(alpha=>alpha=>rea)=>(nat=>alpha)yprod(pos=>nat)=>
                                      (nat=>alpha)yprod(pos=>nat)=>rea"))

(add-computation-rules
 "(MCplDist alpha)d(us1 pair M1)(us2 pair M2)"
 "RealLim([n]d(us1 n)(us2 n))([p]M1(PosS p)max M2(PosS p))")

;; MCplDistTotal
(set-totality-goal "MCplDist")
(fold-alltotal)
(assume "d")
(fold-alltotal)
(cases)
(assume "us1" "M1")
(fold-alltotal)
(cases)
(assume "us2" "M2")
(ng #t)
(use "ReaTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RealMCplDist
(set-goal "allnc d,w1,w2(
 allnc u(X^ u -> d u u===0) -> 
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) ->
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
 (MCpl (cterm (u^) X^ u^))d w1 ->
 (MCpl (cterm (u^) X^ u^))d w2 ->
 Real((MCplDist alpha)d w1 w2))")
(assume "d")
(cases)
(assume "us1" "N1")
(cases)
(assume "us2" "N2" "dRefl" "dSym" "dTriang" "Mw1" "Mw2")
(inst-with-to "MCplPairToX" (pt "d") (pt "us1") (pt "N1") "Mw1" "Xus1")
(inst-with-to "MCplPairToX" (pt "d") (pt "us2") (pt "N2") "Mw2" "Xus2")

(simp "MCplDist0CompRule")
;; ?^11:Real(RealLim([n]d(us1 n)(us2 n))([p]N1(PosS p)max N2(PosS p)))
(use "RealLimReal")
;; 12-14
(ng #t)
(assume "n")
(assert "d(us1 n)(us2 n)===d(us2 n)(us1 n)")
(use "dSym")
(use "Xus1")
(use "Xus2")
(assume "dSymInst")
(realproof)
;; 13
(ng #t)
(assume "p" "n" "m" "nBd" "mBd")
;; ?^23:abs(d(us1 n)(us2 n)+ ~(d(us1 m)(us2 m)))<<=(1#2**p)
(use "RealLeTrans" (pt "d(us1 n)(us1 m)+d(us2 m)(us2 n)"))
(use "MtrUBAbsQuad")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus1")
(use "Xus2")
(use "Xus2")
;; ?^25:d(us1 n)(us1 m)+d(us2 m)(us2 n)<<=(1#2**p)
(assert "Real(d(us2 m)(us2 n))")
(use "MtrReal")
(use "dSym")
(use "Xus2")
(use "Xus2")
(assume "R2m2n")
(assert "Real(d(us1 n)(us1 m))")
(use "MtrReal")
(use "dSym")
(use "Xus1")
(use "Xus1")
(assume "R1n1m")
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 45,46
;; ?^45:d(us1 n)(us1 m)<<=(1#2**PosS p)
(use "MCauchyElim" (pt "N1"))
(use "MCplPairToMCauchy")
(use "Mw1")
(use "NatLeTrans" (pt "N1(PosS p)max N2(PosS p)"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "N1(PosS p)max N2(PosS p)"))
(use "NatMaxUB1")
(use "mBd")
;; ?^46:d(us2 m)(us2 n)<<=(1#2**PosS p)
(use "MCauchyElim" (pt "N2"))
(use "MCplPairToMCauchy")
(use "Mw2")
(use "NatLeTrans" (pt "N1(PosS p)max N2(PosS p)"))
(use "NatMaxUB2")
(use "mBd")
(use "NatLeTrans" (pt "N1(PosS p)max N2(PosS p)"))
(use "NatMaxUB2")
(use "nBd")
;; 14
(ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
;; ?^65:N1(PosS p)<=N1(PosS q)
(inst-with-to "MCplPairToMon" (pt "d") (pt "us1") (pt "N1") "Mw1" "MonN1")
(use "MonElim")
(use "MonN1")
(use "p<=q")
;; ?^66:N2(PosS p)<=N2(PosS q)
(inst-with-to "MCplPairToMon" (pt "d") (pt "us2") (pt "N2") "Mw2" "MonN2")
(use "MonElim")
(use "MonN2")
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "RealMCplDist")

;; We prove that MCpl with distance MCplDist is a metric space.
;; This requires some preparations.

;; MCplLimCauchy
(set-goal "allnc d,us1,M1,us2,M2(
  allnc u(X^ u -> d u u===0) ->
  allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
  allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
  allnc n X^(us1 n) ->
  allnc n X^(us2 n) ->
  allnc p,n,m(M1 p<=n -> M1 p<=m -> d(us1 n)(us1 m)<<=(1#2**p)) ->
  allnc p,n,m(M2 p<=n -> M2 p<=m -> d(us2 n)(us2 m)<<=(1#2**p)) ->
  allnc p,n,m(M1(PosS p)max M2(PosS p)<=n ->
              M1(PosS p)max M2(PosS p)<=m ->
              abs(d(us1 n)(us2 n)+ ~(d(us1 m)(us2 m)))<<=(1#2**p)))")
(assume "d" "us1" "M1" "us2" "M2" "dRefl" "dSym" "dTriang"
	"Xus1" "Xus2" "us1Bd" "us2Bd" "p" "n" "m" "nBd" "mBd")

(assert "allnc n,m Real(d(us1 n)(us2 m))")
(assume "n1" "m1")
(use "MtrReal")
(use "dSym")
(use "Xus1")
(use "Xus2")
(assume "Rus12")

(use "RealLeTrans" (pt "abs(d(us1 n)(us2 n)+ ~(d(us1 n)(us2 m)))+
                        abs(d(us1 n)(us2 m)+ ~(d(us1 m)(us2 m)))"))
(use "RealLeAbsMinus")
(autoreal)
;; ?^11:abs(d(us1 n)(us2 n)+ ~(d(us1 n)(us2 m)))+
;;      abs(d(us1 n)(us2 m)+ ~(d(us1 m)(us2 m)))<<=
;;      (1#2**p)
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 16,17
;; ?^16:abs(d(us1 n)(us2 n)+ ~(d(us1 n)(us2 m)))<<=(1#2**PosS p)
(use "RealLeTrans" (pt "d(us2 n)(us2 m)"))
(use "MtrUBAbsR")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus2")
(use "Xus2")
;; ?^19:d(us2 n)(us2 m)<<=(1#2**PosS p)
(use "us2Bd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "mBd")
;; ?^17:abs(d(us1 n)(us2 m)+ ~(d(us1 m)(us2 m)))<<=(1#2**PosS p)
(use "RealLeTrans" (pt "d(us1 n)(us1 m)"))
(use "MtrUBAbsL")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus1")
(use "Xus2")
;; ?^32:d(us1 n)(us1 m)<<=(1#2**PosS p)
(use "us1Bd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "mBd")
;; Proof finished.
;; (cdp)
(save "MCplLimCauchy")

;; MCplxsCs
(set-goal "allnc d,us1,M1,us2,M2,xs,M(
  allnc u(X^ u -> d u u===0) ->
  allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
  allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
  allnc n X^(us1 n) -> 
  allnc n X^(us2 n) -> 
  MCauchy d us1 M1 -> 
  MCauchy d us2 M2 -> 
  allnc n xs n eqd d(us1 n)(us2 n) -> 
  allnc p M p=M1(PosS p)max M2(PosS p) -> 
  allnc p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)))")
(assume "d" "us1" "M1" "us2" "M2" "xs" "M" "dRefl" "dSym" "dTriang"
	"Xus1" "Xus2" "us1Cs" "us2Cs" "xsDef" "MDef" "p" "n" "m" "nBd" "mBd")
(simp "xsDef")
(simp "xsDef")
(use "MCplLimCauchy" (pt "M1") (pt "M2"))
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus2")
(use "MCauchyElim")
(use "us1Cs")
(use "MCauchyElim")
(use "us2Cs")
(simp "<-" "MDef")
(use "nBd")
(simp "<-" "MDef")
(use "mBd")
;; Proof finished.
;; (cdp)
(save "MCplxsCs")

;; MCplRefl
(set-goal "allnc d,w(
  allnc u(X^ u -> d u u===0) ->
  allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
  allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
  (MCpl (cterm (u^) X^ u^))d w -> 
  (MCplDist alpha)d w w===0)")
(assume "d")
(cases)
(assume "us" "M" "dRefl" "dSym" "dTriang" "Mw")

(inst-with-to "MCplPairToX" (pt "d") (pt "us") (pt "M") "Mw" "Xus")
(inst-with-to "MCplPairToMCauchy" (pt "d") (pt "us") (pt "M") "Mw" "CusM")
(inst-with-to "MCplPairToMon" (pt "d") (pt "us") (pt "M") "Mw" "MonM")

(simp "MCplDist0CompRule")
;; ?^11:RealLim([n]d(us n)(us n))([p]M(PosS p)max M(PosS p))===0
(simpreal (pf "RealLim([n]d(us n)(us n))([p]M(PosS p)max M(PosS p))===
               RealLim([n](0#1))([p]Zero)"))
(use "RealLimConst")
(realproof)
(intro 0)
(strip)
(use "Truth")
;; ?^13:RealLim([n]d(us n)(us n))([p]M(PosS p)max M(PosS p))===
;;      RealLim([n]0)([p]Zero)
(use "RealLimCompat")
;; 18-22
(ng #t)
;; ?^23:allnc p,n,m(
;;       M(PosS p)<=n -> 
;;       M(PosS p)<=m -> abs(d(us n)(us n)+ ~(d(us m)(us m)))<<=(1#2**p))
(assume "p" "n" "m" "nBd" "mBd")

(assert "allnc n,m Real(d(us n)(us m))")
(assume "n1" "m1")
(use "MtrReal")
(use "dSym")
(use "Xus")
(use "Xus")
(assume "Rus")

(use "RealLeTrans" (pt "abs(d(us n)(us n)+ ~(d(us n)(us m)))+
                        abs(d(us n)(us m)+ ~(d(us m)(us m)))"))
(use "RealLeAbsMinus")
(autoreal)
;; ?^33:abs(d(us n)(us n)+ ~(d(us n)(us m)))+
;;      abs(d(us n)(us m)+ ~(d(us m)(us m)))<<=
;;      (1#2**p)
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 38,39
;; ?^38:abs(d(us n)(us n)+ ~(d(us n)(us m)))<<=(1#2**PosS p)

(use-with "RCauchyElim" (pt "[m]d(us n)(us m)") (pt "M")
	  "?" (pt "PosS p") (pt "n") (pt "m") "?" "?")
;; 40-42
(use "MCauchyToRCauchy1R")
(use "dSym")
(use "dTriang")
(use "Xus")
(use "Xus")
(use "CusM")
(use "nBd")
(use "mBd") 
;; ?^39:abs(d(us n)(us m)+ ~(d(us m)(us m)))<<=(1#2**PosS p)
(use-with "RCauchyElim" (pt "[n]d(us n)(us m)") (pt "M")
	  "?" (pt "PosS p") (pt "n") (pt "m") "?" "?")
;; 48-50
(use "MCauchyToRCauchy1L")
(use "dSym")
(use "dTriang")
(use "Xus")
(use "Xus")
(use "CusM")
(use "nBd")
(use "mBd")

;; ?^19:allnc p,q(
;;       p<=q -> 
;;       ([p0]M(PosS p0)max M(PosS p0))p<=([p0]M(PosS p0)max M(PosS p0))q)
(ng #t)
;; ?^67:allnc p,q(p<=q -> M(PosS p)<=M(PosS q))
(assume "p" "q" "p<=q")
(use "MonElim")
(use "MonM")
(use "p<=q")

;; ?^20:allnc p,n,m(
;;       ([p0]Zero)p<=n -> 
;;       ([p0]Zero)p<=m -> abs(([n0]0)n+ ~(([n0]0)m))<<=(1#2**p))
(ng #t)
;; ?^60:allnc p,n,m(T -> T -> 0<<=(1#2**p))
(assume "p" "n" "m" "Useless1" "Useless2")
(use "RatLeToRealLe")
(use "Truth")

;; ?^21:allnc p,q(p<=q -> ([p0]Zero)p<=([p0]Zero)q)
(strip)
(use "Truth")

;; ?^22:allnc n ([n0]d(us n0)(us n0))n===([n0]0)n
(ng #t)
;; ?^75:allnc n d(us n)(us n)===0
(assume "n")
(use "dRefl")
(use "Xus")
;; Proof finished.
;; (cdp)
(save "MCplRefl")

;; MCplSym
(set-goal "allnc d,w1,w2(
  allnc u(X^ u -> d u u===0) ->
  allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
  allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
  (MCpl (cterm (u^) X^ u^))d w1 -> 
  (MCpl (cterm (u^) X^ u^))d w2 ->
  (MCplDist alpha)d w1 w2===(MCplDist alpha)d w2 w1)")
(assume "d")
(cases)
(assume "us1" "M1")
(cases)
(assume "us2" "M2" "dRefl" "dSym" "dTriang" "Mw1" "Mw2")

(inst-with-to "MCplPairToX" (pt "d") (pt "us1") (pt "M1") "Mw1" "Xus1")
(inst-with-to "MCplPairToX" (pt "d") (pt "us2") (pt "M2") "Mw2" "Xus2")

(inst-with-to "MCplPairToMCauchy" (pt "d") (pt "us1") (pt "M1") "Mw1" "Cus1M1")
(inst-with-to "MCplPairToMCauchy" (pt "d") (pt "us2") (pt "M2") "Mw2" "Cus2M2")

(inst-with-to "MCplPairToMon" (pt "d") (pt "us1") (pt "M1") "Mw1" "MonM1")
(inst-with-to "MCplPairToMon" (pt "d") (pt "us2") (pt "M2") "Mw2" "MonM2")

(simp "MCplDist0CompRule")
(simp "MCplDist0CompRule")
(use "RealLimCompat")
;; 21-25
(ng #t)
(use "MCplLimCauchy")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus2")
(use "MCauchyElim")
(use "Cus1M1")
(use "MCauchyElim")
(use "Cus2M2")
;; 22
(ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
(use "MonElim")
(use "MonM1")
(use "p<=q")
(use "MonElim")
(use "MonM2")
(use "p<=q")
;; 23
(ng #t)
(use "MCplLimCauchy")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus2")
(use "Xus1")
(use "MCauchyElim")
(use "Cus2M2")
(use "MCauchyElim")
(use "Cus1M1")
;; 24
(ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
(use "MonElim")
(use "MonM2")
(use "p<=q")
(use "MonElim")
(use "MonM1")
(use "p<=q")
;; 25
(ng #t)
(assume "n")
(use "dSym")
(use "Xus1")
(use "Xus2")
;; Proof finished.
;; (cdp)
(save "MCplSym")

;; MCplTriang
(set-goal "allnc d,w1,w2,w3(
  allnc u(X^ u -> d u u===0) ->
  allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
  allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
  (MCpl (cterm (u^) X^ u^))d w1 -> 
  (MCpl (cterm (u^) X^ u^))d w2 -> 
  (MCpl (cterm (u^) X^ u^))d w3 -> 
  (MCplDist alpha)d w1 w3<<=(MCplDist alpha)d w1 w2+(MCplDist alpha)d w2 w3)")
(assume "d")
(cases)
(assume "us1" "M1")
(cases)
(assume "us2" "M2")
(cases)
(assume "us3" "M3" "dRefl" "dSym" "dTriang" "MPtus1M1" "MPtus2M2" "MPtus3M3")

(inst-with-to "MCplPairToMon" (pt "d") (pt "us1") (pt "M1") "MPtus1M1" "M1Mon")
(inst-with-to "MCplPairToMon" (pt "d") (pt "us2") (pt "M2") "MPtus2M2" "M2Mon")
(inst-with-to "MCplPairToMon" (pt "d") (pt "us3") (pt "M3") "MPtus3M3" "M3Mon")

(defnc "xs13" "[n]d(us1 n)(us3 n)")
(defnc "xs12" "[n]d(us1 n)(us2 n)")
(defnc "xs23" "[n]d(us2 n)(us3 n)")

(defnc "M13" "[p]M1(PosS p)max M3(PosS p)")
(defnc "M12" "[p]M1(PosS p)max M2(PosS p)")
(defnc "M23" "[p]M2(PosS p)max M3(PosS p)")

(defnc "x13" "RealLim xs13 M13")
(defnc "x12" "RealLim xs12 M12")
(defnc "x23" "RealLim xs23 M23")

(assert "(MCplDist alpha)d(us1 pair M1)(us3 pair M3)eqd x13")
(simp "MCplDist0CompRule")
(simp "x13Def")
(simp "xs13Def")
(simp "M13Def")
(use "InitEqD")
;; Assertion proved.
(assume "x13Char")

(assert "(MCplDist alpha)d(us1 pair M1)(us2 pair M2)eqd x12")
(simp "MCplDist0CompRule")
(simp "x12Def")
(simp "xs12Def")
(simp "M12Def")
(use "InitEqD")
;; Assertion proved.
(assume "x12Char")

(assert "(MCplDist alpha)d(us2 pair M2)(us3 pair M3)eqd x23")
(simp "MCplDist0CompRule")
(simp "x23Def")
(simp "xs23Def")
(simp "M23Def")
(use "InitEqD")
;; Assertion proved.
(assume "x23Char")

(simp "x13Char")
(simp "x12Char")
(simp "x23Char")

;; ?^101:x13<<=x12+x23

;; We need that xs13 x13 are reals and xs13 converges to x13 with M13,
;; and similarly for 12 and 23

(assert "allnc n X^(us1 n)")
(use "MCplPairToX" (pt "d") (pt "M1"))
(use "MPtus1M1")
;; Assertion proved.
(assume "Xus1")

(assert "allnc n X^(us2 n)")
(use "MCplPairToX" (pt "d") (pt "M2"))
(use "MPtus2M2")
;; Assertion proved.
(assume "Xus2")

(assert "allnc n X^(us3 n)")
(use "MCplPairToX" (pt "d") (pt "M3"))
(use "MPtus3M3")
;; Assertion proved.
(assume "Xus3")

(assert "allnc n Real(xs13 n)")
(simp "xs13Def")
(assume "n")
(ng #t)
(assert "d(us1 n)(us3 n)===d(us3 n)(us1 n)")
(use "dSym")
(use "Xus1")
(use "Xus3")
(assume "dSymInst")
(realproof)
;; Assertion proved.
(assume "Rxs13")

(assert "allnc n Real(xs12 n)")
(simp "xs12Def")
(assume "n")
(ng #t)
(assert "d(us1 n)(us2 n)===d(us2 n)(us1 n)")
(use "dSym")
(use "Xus1")
(use "Xus2")
(assume "dSymInst")
(realproof)
;; Assertion proved.
(assume "Rxs12")

(assert "allnc n Real(xs23 n)")
(simp "xs23Def")
(assume "n")
(ng #t)
(assert "d(us2 n)(us3 n)===d(us3 n)(us2 n)")
(use "dSym")
(use "Xus2")
(use "Xus3")
(assume "dSymInst")
(realproof)
;; Assertion proved.
(assume "Rxs23")

(assert "MCauchy d us1 M1")
(use "MCplPairToMCauchy")
(use "MPtus1M1")
;; Assertion proved.
(assume "us1Cs")

(assert "MCauchy d us2 M2")
(use "MCplPairToMCauchy")
(use "MPtus2M2")
;; Assertion proved.
(assume "us2Cs")

(assert "MCauchy d us3 M3")
(use "MCplPairToMCauchy")
(use "MPtus3M3")
;; Assertion proved.
(assume "us3Cs")

(assert "Mon M13")
(simp "M13Def")
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "NatLeMonMax")
(use "MonElim")
(use "M1Mon")
(use "p<=q")
(use "MonElim")
(use "M3Mon")
(use "p<=q")
;; Assertion proved.
(assume "M13Mon")

(assert "Mon M12")
(simp "M12Def")
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "NatLeMonMax")
(use "MonElim")
(use "M1Mon")
(use "p<=q")
(use "MonElim")
(use "M2Mon")
(use "p<=q")
;; Assertion proved.
(assume "M12Mon")

(assert "Mon M23")
(simp "M23Def")
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "NatLeMonMax")
(use "MonElim")
(use "M2Mon")
(use "p<=q")
(use "MonElim")
(use "M3Mon")
(use "p<=q")
;; Assertion proved.
(assume "M23Mon")

(assert "Real x13")
(simp "x13Def")
(use "RealLimReal")
(use "Rxs13")
(use "MCplxsCs" (pt "d") (pt "us1") (pt "M1") (pt "us3") (pt "M3"))
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus3")
(use "us1Cs")
(use "us3Cs")
(assume "n")
(simp "xs13Def")
(use "InitEqD")
(assume "p")
(simp "M13Def")
(use "Truth")
(use "MonElim")
(use "M13Mon")
;; Assertion proved.
(assume "Rx13")

(assert "Real x12")
(simp "x12Def")
(use "RealLimReal")
(use "Rxs12")
(use "MCplxsCs" (pt "d") (pt "us1") (pt "M1") (pt "us2") (pt "M2"))
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus2")
(use "us1Cs")
(use "us2Cs")
(assume "n")
(simp "xs12Def")
(use "InitEqD")
(assume "p")
(simp "M12Def")
(use "Truth")
(use "MonElim")
(use "M12Mon")
;; Assertion proved.
(assume "Rx12")

(assert "Real x23")
(simp "x23Def")
(use "RealLimReal")
(use "Rxs23")
(use "MCplxsCs" (pt "d") (pt "us2") (pt "M2") (pt "us3") (pt "M3"))
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus2")
(use "Xus3")
(use "us2Cs")
(use "us3Cs")
(assume "n")
(simp "xs23Def")
(use "InitEqD")
(assume "p")
(simp "M23Def")
(use "Truth")
(use "MonElim")
(use "M23Mon")
;; Assertion proved.
(assume "Rx23")

;; ?^260:x13<<=x12+x23

(use "RealLeAllPlusToLe") ;here all p rather than allnc p was used.  Change
(autoreal)
;; ?^263:all p x13<<=x12+x23+(1#2**p)
(assume "p")
(simpreal "<-" "RealPlusHalfExpPosS")
(simpreal "RealPlusAssoc")
(use "RealLeTrans" (pt "x13+ RealUMinus(1#2**PosS p)+(1#2**PosS p)"))
;; 270,271
;; ?^270:x13<<=x13+ ~(1#2**PosS p)+(1#2**PosS p)
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "RealUMinus(1#2**PosS p)+(1#2**PosS p)===
               (1#2**PosS p)+ RealUMinus(1#2**PosS p)"))
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;;?^271:x13+ ~(1#2**PosS p)+(1#2**PosS p)<<=x12+x23+(1#2**PosS p)+(1#2**PosS p)
(use "RealLeMonPlus")
;; 285,286
;; ?^285:x13+ ~(1#2**PosS p)<<=x12+x23+(1#2**PosS p)
(use "RealLeTrans" (pt "x12+(1#2**PosS(PosS p))+x23+(1#2**PosS(PosS p))"))
;; 287,288
;; ?^287:x13+ ~(1#2**PosS p)<<=x12+(1#2**PosS(PosS p))+x23+(1#2**PosS(PosS p))

;; Fix a large enough n
(assert "exnc n(M13(PosS p)<=n andnc
                M12(PosS(PosS p))<=n andnc M23(PosS(PosS p))<=n)")
(intro 0 (pt "M13(PosS p) max M12(PosS(PosS p)) max M23(PosS(PosS p))"))
(split)
(use "NatLeTrans" (pt "M13(PosS p) max M12(PosS(PosS p))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(split)
(use "NatLeTrans" (pt "M13(PosS p) max M12(PosS(PosS p))"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "NatMaxUB2")
(assume "nEx")
(by-assume "nEx" "n" "nBd")

;; ?^303:x13+ ~(1#2**PosS p)<<=x12+(1#2**PosS(PosS p))+x23+(1#2**PosS(PosS p))

;; Estimates for 13,12,23
(assert "x13+RealUMinus(1#2**PosS p)<<= xs13 n")
(use "RealLePlusUMinus")
(autoreal)
(use "RealLeTrans" (pt "abs(x13+ ~(xs13 n))"))
(use "RealLeAbsId")
(autoreal)
(simpreal "RealAbsPlusUMinus")
;; ?^313:abs(xs13 n+ ~x13)<<=(1#2**PosS p)
;; (use "x13Approx") ;this is missing.  Use the new RealComplte and MCplxsCs
(simp "x13Def")
(use "RealComplete")
(use "Rxs13")
(use "MCplxsCs" (pt "d") (pt "us1") (pt "M1") (pt "us3") (pt "M3"))
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus3")
(use "us1Cs")
(use "us3Cs")
(assume "n1")
(simp "xs13Def")
(use "InitEqD")
(assume "p1")
(simp "M13Def")
(use "Truth")
(use "MonElim")
(use "M13Mon")
(use "nBd")
(autoreal)
;; Assertion proved.
(assume "x13Est")

(assert "xs12 n<<=x12+(1#2**PosS(PosS p))")
(use "RealLePlusR")
(autoreal)
(simpreal "RealPlusComm")
(use "RealLeTrans" (pt "abs(xs12 n+ ~x12)"))
(use "RealLeAbsId")
(autoreal)
;; (use "x12Approx") ;this is missing.  Use the new RealComplte and MCplxsCs
(simp "x12Def")
(use "RealComplete")
(use "Rxs12")
(use "MCplxsCs" (pt "d") (pt "us1") (pt "M1") (pt "us2") (pt "M2"))
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus2")
(use "us1Cs")
(use "us2Cs")
(assume "n1")
(simp "xs12Def")
(use "InitEqD")
(assume "p1")
(simp "M12Def")
(use "Truth")
(use "MonElim")
(use "M12Mon")
(use "nBd")
(autoreal)
;; Assertion proved.
(assume "x12Est")

(assert "xs23 n<<=x23+(1#2**PosS(PosS p))")
(use "RealLePlusR")
(autoreal)
(simpreal "RealPlusComm")
(use "RealLeTrans" (pt "abs(xs23 n+ ~x23)"))
(use "RealLeAbsId")
(autoreal)
(simp "x23Def")
(use "RealComplete")
(use "Rxs23")
(use "MCplxsCs" (pt "d") (pt "us2") (pt "M2") (pt "us3") (pt "M3"))
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus2")
(use "Xus3")
(use "us2Cs")
(use "us3Cs")
(assume "n1")
(simp "xs23Def")
(use "InitEqD")
(assume "p1")
(simp "M23Def")
(use "Truth")
(use "MonElim")
(use "M23Mon")
(use "nBd")
(autoreal)
;; Assertion proved.
(assume "x23Est")

(use "RealLeTrans" (pt "xs13 n"))
(use "x13Est")
(use "RealLeTrans" (pt "xs12 n+xs23 n"))
;; 402,403
;; ?^402:xs13 n<<=xs12 n+xs23 n
(simp "xs13Def")
(simp "xs12Def")
(simp "xs23Def")
(ng #t)
(use "dTriang")
(use "MCplPairToX" (pt "d") (pt "M1"))
(use "MPtus1M1")
(use "MCplPairToX" (pt "d") (pt "M2"))
(use "MPtus2M2")
(use "MCplPairToX" (pt "d") (pt "M3"))
(use "MPtus3M3")
;; ?^403:xs12 n+xs23 n<<=x12+(1#2**PosS(PosS p))+x23+(1#2**PosS(PosS p))
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlus")
(use "x12Est")
(use "x23Est")
(autoreal)
;;?^288:x12+(1#2**PosS(PosS p))+x23+(1#2**PosS(PosS p))<<=x12+x23+(1#2**PosS p)
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlus")
(use "RealLeRefl")
(autoreal)
(simpreal "RealPlusComm")
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlus")
(use "RealLeRefl")
(autoreal)
(simpreal "RealPlusHalfExpPosS")
(use "RealLeRefl")
(autoreal)
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "MCplTriang")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Properties of the metric completion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-program-constant "Emb" (py "alpha=>(nat=>alpha)yprod(pos=>nat)"))

(add-computation-rules
 "(Emb alpha)u" "([n]u)pair([p]Zero)")

;; EmbTotal
(set-totality-goal "Emb")
(fold-alltotal)
(assume "u")
(ng #t)
(use "YprodTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; MCplEmb
(set-goal "allnc d,u(
 allnc u(X^ u -> d u u===0) ->
 X^ u -> (MCpl (cterm (u^) X^ u^))d((Emb alpha)u))")
(assume "d" "u" "dRefl" "Xu")
(ng #t)
(intro 0)
;; 4-6
(ng #t)
(assume "n")
(use "Xu")
;; 5
(ng #t)
(intro 0)
(assume "p" "n" "m" "Useless1" "Useless2")
(ng #t)
(simpreal "dRefl")
(use "RatLeToRealLe")
(use "Truth")
(use "Xu")
;; 6
(ng #t)
(intro 0)
(assume "p" "q" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "MCplEmb")

(add-var-name "uss" (py "nat=>nat=>alpha"))
(add-var-name "Ns" (py "nat=>pos=>nat"))

;; MCplDistEmb
(set-goal "allnc d,us,uss,Ns(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) ->
 allnc n,m X^(uss n m) ->
 allnc n us n eqd uss n(Ns n(cNatPos n)) ->
 allnc n,m 
  d(us n)(us m)===(MCplDist alpha)d((Emb alpha)(us n))((Emb alpha)(us m)))")
(assume "d" "us" "uss" "Ns" "dSym" "Xuss" "usDef" "n" "m")
(simp "Emb0CompRule")
(simp "Emb0CompRule")
(simp "MCplDist0CompRule")
(simp (pf "([n0]d(([n1]us n)n0)(([n1]us m)n0))eqd([n0]d(us n)(us m))"))
;; ?^6:d(us n)(us m)===
;;     RealLim([n0]d(us n)(us m))([p]([p0]Zero)(PosS p)max([p0]Zero)(PosS p))

(assert "Real(d(us n)(us m))")
(use "MtrReal")
(use "dSym")
(simp "usDef")
(use "Xuss")
(simp "usDef")
(use "Xuss")
;; Assertion proved.
(assume "RHyp")

(simpreal "RealLimConst")
(use "RealEqRefl")
(use "RHyp")

;; ?^18:Mon([p]([p0]Zero)(PosS p)max([p0]Zero)(PosS p))
(ng #t)
(intro 0)
(strip)
(use "Truth")
(use "RHyp")

;; ?^7:([n0]d(([n1]us n)n0)(([n1]us m)n0))eqd([n0]d(us n)(us m))
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "MCplDistEmb")

(add-var-name "ws" (py "nat=>(nat=>alpha)yprod(pos=>nat)"))

;; In a metric completion, we explicitly define the limit of a
;; modulated Cauchy sequence of points, as a program constant.

(add-program-constant
 "MCplLim" (py "(nat=>(nat=>alpha)yprod(pos=>nat))=>(pos=>nat)=>
                (nat=>alpha)yprod(pos=>nat)"))

(add-computation-rules
 "(MCplLim alpha)ws M"
 "([n]lft(ws n)(rht(ws n)(cNatPos n)))pair([p]M(PosS p)max PosS(PosS p))")

;; MCplLimTotal
(set-totality-goal "MCplLim")
(assume "ws^" "Tws" "M^" "TM")
(ng #t)
(intro 0)
;; 4,5
;; ?_4:allnc n^(TotalNat n^ -> Total(([n]lft(ws^ n)(rht(ws^ n)(cNatPos n)))n^))
(fold-alltotal)
(assume "n")
(ng #t)
(assert "TotalYprod(ws^ n)")
(use "Tws")
(use "NatTotalVar")
(assume "Twsn")
(elim "Twsn")
(assume "us^" "Tus" "M^1" "TM1")
(ng #t)
(use "Tus")
(use "TM1")
(use "PosTotalVar")
;; ?_5:allnc p^(TotalPos p^ -> TotalNat(([p]M^(PosS p)max PosS(PosS p))p^))
(fold-alltotal)
(assume "p")
(ng #t)
(use "NatMaxTotal")
(use "TM")
(use "PosTotalVar")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Consider a metric completion.  Let ws be a Cauchy sequence of
;; points with monotone modulus M.  We shall show that its limit
;; formed by (MCplLim alpha)ws M is a point in the completion.  The
;; proof uses auxiliary lemmas MCauchyConvMod MCplSeqApprox
;; MCplCauchyApprox

;; Consider in a metric completion a point w given by a us and M.
;; Then the distance between the embedding of (us n) and w is
;; determined by the modulus M.

;; MCauchyConvMod
(set-goal "allnc d,us,M(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) -> 
 (MCpl (cterm (u^) X^ u^))d(us pair M) ->
 allnc p,n(
  M p<=n -> (MCplDist alpha)d((Emb alpha)(us n))(us pair M)<<=(1#2**p)))")
(assume "d" "us" "M" "dSym" "dTriang" "PusM" "p" "n" "nBd")
(simp "Emb0CompRule")
(simp "MCplDist0CompRule")
(simp (pf "[n0]d(([n1]us n)n0)(us n0)eqd([n0]d(us n)(us n0))"))
(simp (pf "([p0]([p1]Zero)(PosS p0)max M(PosS p0))eqd[p0]M(PosS p0)"))
;; ?^7:RealLim([n0]d(us n)(us n0))([p0]M(PosS p0))<<=(1#2**p)
(inst-with-to "MCplToX" (pt "d") (pt "us pair M") "PusM" "Xus")
(assert "MCauchy d us M")
(inst-with-to "MCplToMCauchy" (pt "d") (pt "us pair M") "PusM" "CusM")
(use "CusM")
(assume "CusM")
(assert "Mon M")
(inst-with-to "MCplToMon" (pt "d") (pt "us pair M") "PusM" "MonM")
(use "MonM")
(assume "MonM")

(defnc "xs" "[n0]d(us n)(us n0)")

(assert "allnc n Real(xs n)")
(assume "n1")
(simp "xsDef")
(ng #t)
(use "MtrReal")
(use "dSym")
(use "Xus")
(use "Xus")
;; Assertion proved.
(assume "Rxs")

(simp "<-" "xsDef")
;; ?^37:RealLim xs([p0]M(PosS p0))<<=(1#2**p)

(defnc "x" "RealLim xs([p0]M(PosS p0))")

(assert "Real x")
(simp "xDef")
(use "RealLimReal")
(use "Rxs")
(ng #t)
(assume "p1" "n1" "m1" "n1Bd" "m1Bd")
(simp "xsDef")
(ng #t)
(use "RealLeTrans" (pt "d(us n1)(us m1)"))
(use "MtrUBAbsR")
(use "dSym")
(use "dTriang")
(use "Xus")
(use "Xus")
(use "Xus")
(use "MCauchyElim" (pt "M"))
(use "CusM")
(use "NatLeTrans" (pt "M(PosS p1)"))
(use "MonElim")
(use "MonM")
(use "Truth")
(use "n1Bd")
(use "NatLeTrans" (pt "M(PosS p1)"))
(use "MonElim")
(use "MonM")
(use "Truth")
(use "m1Bd")
(ng #t)
(assume "p1" "q1" "p1<=q1")
(use "MonElim")
(use "MonM")
(use "p1<=q1")
;; Assertion proved.
(assume "Rx")
;; ?^77:RealLim xs([p0]M(PosS p0))<<=(1#2**p)
(simp "<-" "xDef")
;; ?^78:x<<=(1#2**p)

(assert "RealConv xs(RealLim xs([p0]M(PosS p0)))([p0]M(PosS p0))")
(intro 0)
;; 81-84
(use "Rxs")
;; 82
(simp "<-" "xDef")
(use "Rx")
;; 83
(intro 0)
(assume "p1" "q1" "p1<=q1")
(ng #t)
(use "MonElim")
(use "MonM")
(use "p1<=q1")
;; 84
(use "RealComplete")
;; 91-93
(assume "n1")
(simp "xsDef")
(ng #t)
(use "MtrReal")
(use "dSym")
(use "Xus")
(use "Xus")
;; 92
(ng #t)
(assume "p1" "n1" "m1" "n1Bd" "m1Bd")
(simp "xsDef")
(ng #t)
(use "RealLeTrans" (pt "d(us n1)(us m1)"))
(use "MtrUBAbsR")
(use "dSym")
(use "dTriang")
(use "Xus")
(use "Xus")
(use "Xus")
(use "MCauchyElim" (pt "M"))
(use "CusM")
(use "NatLeTrans" (pt "M(PosS p1)"))
(use "MonElim")
(use "MonM")
(use "Truth")
(use "n1Bd")
(use "NatLeTrans" (pt "M(PosS p1)"))
(use "MonElim")
(use "MonM")
(use "Truth")
(use "m1Bd")
;; 93
(ng #t)
(assume "p1" "q1" "p1<=q1")
(use "MonElim")
(use "MonM")
(use "p1<=q1")
;; Assertion proved.
;; ?^79:RealConv xs(RealLim xs([p0]M(PosS p0)))([p0]M(PosS p0)) -> x<<=(1#2**p)
(simp "<-" "xDef")
;; ?^126:RealConv xs x([p0]M(PosS p0)) -> x<<=(1#2**p)
(assume "RealConvHyp")

(assert "allnc m(M p<=m -> xs m<<=(1#2**p))")
(assume "m" "mBd")
(simp "xsDef")
(ng #t)
(use "MCauchyElim" (pt "M"))
(use "CusM")
(use "nBd")
(use "mBd")
;; ?^118:allnc m(M p<=m -> xs m<<=(1#2**p)) -> x<<=(1#2**p)
;; Assertion proved.
(assume "xsProp")
;; ?^136:x<<=(1#2**p)

(use "RealLeAllPlusToLe")
;; 137-139
;; ?^137:Real x
(use "Rx")
;; 138
(use "RealRat")
;; ?^139:all p0 x<<=RealPlus(1#2**p)(1#2**p0)
(assume "q")
;; ?^140:x<<=RealPlus(1#2**p)(1#2**q)

(defnc "m" "M p max M(PosS q)")

(assert "xs m+abs(xs m+ ~x)<<=RealPlus(1#2**p)(1#2**q)")
(use "RealLeMonPlus")
;; 150,151
;; ?^150:xs m<<=(1#2**p)
(use "xsProp")
(simp "mDef")
(use "NatMaxUB1")
;; ?^151:abs(xs m+ ~x)<<=(1#2**q)
(use "RealConvElim4" (pt "[p]M(PosS p)"))
(use "RealConvHyp")
(ng #t)
(simp "mDef")
(use "NatMaxUB2")
;; Assertion proved.
(assume "LePlusHyp")
(use "RealLeTrans" (pt "xs m+abs(xs m+ ~x)"))
;; ?^159:x<<=xs m+abs(xs m+ ~x)
(assert "Real(xs m)")
(use "Rxs")
(assume "Rxsm")
(simpreal "RealAbsPlusUMinus")
;; ?^164:x<<=xs m+abs(x+ ~(xs m))
(use "RealLeTrans" (pt "xs m+(x+ ~(xs m))"))
(simpreal (pf "x+ ~(xs m)=== ~(xs m)+x"))
(simpreal "RealPlusAssoc")
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
(use "RealLeRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; ?^168:xs m+(x+ ~(xs m))<<=xs m+abs(x+ ~(xs m))
(use "RealLeMonPlus")
(use "RealLeRefl")
(autoreal)
(use "RealLeAbsId")
(autoreal)
;; ?^160:xs m+abs(xs m+ ~x)<<=RealPlus(1#2**p)(1#2**q)
(use "RealLeMonPlus")
(use "xsProp")
(simp "mDef")
(use "NatMaxUB1")
;; ?^187:abs(xs m+ ~x)<<=(1#2**q)
(use "RealConvElim4" (pt "[p]M(PosS p)"))
(use "RealConvHyp")
(ng #t)
(simp "mDef")
(use "NatMaxUB2")

;; ?^8:([p]([p0]Zero)(PosS p)max M(PosS p))eqd([p]M(PosS p))
(ng #t)
(use "InitEqD")
;; ?^6:([n0]d(([n1]us n)n0)(us n0))eqd([n0]d(us n)(us n0))
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "MCauchyConvMod")

;; MCplSeqApprox (uses MCauchyConvMod)
(set-goal "allnc d,uss,Ns,ws,us(
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) ->
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
 allnc n ws n eqd(uss n)pair(Ns n) ->
 allnc n (MCpl (cterm (u^) X^ u^))d(ws n) ->
 allnc n us n eqd uss n(Ns n(cNatPos n)) ->
 allnc n ((MCplDist alpha)d((Emb alpha)(us n))(ws n))<<=(1#2**n))")
(assume "d" "uss" "Ns" "ws" "us" "dSym" "dTriang" "wsDef" "Pws" "usDef" "n")
(use "RealLeTrans" (pt "RealConstr([n0](1#2**cNatPos n))([p]Zero)"))
;; 3,4
(simp "wsDef")
(simp "usDef")
(use "MCauchyConvMod")
(use "dSym")
(use "dTriang")
(simp "<-" "wsDef")
(use "Pws")
(use "Truth")
;; ?^4:(1#2**NatToPos n)<<=(1#2**n)
(use "RatLeToRealLe")
(simp "RatLe0CompRule")
(simp "IntTimes2RewRule")
(simp "IntTimes2RewRule")
(simp "IntLe4CompRule")
(use "PosLeMonPosExp")
(cases (pt "n"))
(assume "Useless")
(use "Truth")
(assume "n0" "Useless")
(simp "NatPosExFree")
(simp "PosToNatToPosId")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "MCplSeqApprox")

;; MCplCauchyApprox (uses MCplSeqApprox)
(set-goal "allnc d,ws,M,uss,Ns,us,L(
 allnc u(X^ u -> d u u===0) -> 
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) ->
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
 allnc n (MCpl (cterm (u^) X^ u^))d(ws n) ->
 allnc p,n,m(M p<=n -> M p<=m -> ((MCplDist alpha)d(ws n)(ws m))<<=(1#2**p)) ->
 allnc n,m X^(uss n m) ->
 allnc n ws n eqd(uss n)pair(Ns n) ->
 allnc n us n eqd uss n(Ns n(cNatPos n)) ->
 allnc p L p=M(PosS p)max PosS(PosS p) ->
 allnc p,n,m(L p<=n  -> L p<=m -> d(us n)(us m)<<=(1#2**p)))")
(assume "d" "ws" "M" "uss" "Ns" "us" "L" "dRefl" "dSym" "dTriang"
	"Pws" "wsCs" "Xuss" "wsDef" "usDef" "LDef" "p" "n" "m" "nBd" "mBd")
(simpreal "MCplDistEmb" (pt "uss") (pt "Ns"))
;; Split (1#2**p)
(use "RealLeTrans" (pt "(1#2**n)+RealPlus(1#2**PosS p)(1#2**m)"))
;; 7,8
;; ?^7:(MCplDist alpha)d((Emb alpha)(us n))((Emb alpha)(us m))<<=
;;     (1#2**n)+RealPlus(1#2**PosS p)(1#2**m)
(use "RealLeTrans" (pt "(MCplDist alpha)d((Emb alpha)(us n))(ws n)+
                        (MCplDist alpha)d(ws n)((Emb alpha)(us m))"))
;; 9,10
;; ?^9:(MCplDist alpha)d((Emb alpha)(us n))((Emb alpha)(us m))<<=
;;     (MCplDist alpha)d((Emb alpha)(us n))(ws n)+
;;     (MCplDist alpha)d(ws n)((Emb alpha)(us m))
(use "MCplTriang")
(use "dRefl")
(use "dSym")
(use "dTriang")
;; ?^14:(MCpl (cterm (u^) X^ u^))d((Emb alpha)(us n))
(use "MCplEmb")
(use "dRefl")
(simp "usDef")
(use "Xuss")
;; ?^15:(MCpl (cterm (u^) X^ u^))d(ws n)
(use "Pws")
;; ?^16:(MCpl (cterm (u^) X^ u^))d((Emb alpha)(us m))
(use "MCplEmb")
(use "dRefl")
(simp "usDef")
(use "Xuss")
;; ?^10:(MCplDist alpha)d((Emb alpha)(us n))(ws n)+
;;      (MCplDist alpha)d(ws n)((Emb alpha)(us m))<<=
;;      (1#2**n)+RealPlus(1#2**PosS p)(1#2**m)
(assert "Real((MCplDist alpha)d(ws n)((Emb alpha)(us m)))")
(use "RealMCplDist")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws")
(use "MCplEmb")
(use "dRefl")
(simp "usDef")
(use "Xuss")
;; Assertion proved.
(assume "Rwsnusm")
(use "RealLeMonPlus")
;; 34,35
;; ?^34:(MCplDist alpha)d((Emb alpha)(us n))(ws n)<<=(1#2**n)
(use "MCplSeqApprox" (pt "uss") (pt "Ns"))
(use "dSym")
(use "dTriang")
(use "wsDef")
(use "Pws")
(use "usDef")
;; ?^35:(MCplDist alpha)d(ws n)((Emb alpha)(us m))<<=
;;      RealPlus(1#2**PosS p)(1#2**m)
(use "RealLeTrans" (pt "(MCplDist alpha)d(ws n)(ws m)+
                        (MCplDist alpha)d(ws m)((Emb alpha)(us m))"))
;; ?^41:(MCplDist alpha)d(ws n)((Emb alpha)(us m))<<=
;;      (MCplDist alpha)d(ws n)(ws m)+
;;      (MCplDist alpha)d(ws m)((Emb alpha)(us m))
(use "MCplTriang")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws")
(use "Pws")
(use "MCplEmb")
(use "dRefl")
(simp "usDef")
(use "Xuss")

;; ?^42:(MCplDist alpha)d(ws n)(ws m)+
;;      (MCplDist alpha)d(ws m)((Emb alpha)(us m))<<=
;;      RealPlus(1#2**PosS p)(1#2**m)

(use "RealLeMonPlus")
;; 52,53
;; ?^52:(MCplDist alpha)d(ws n)(ws m)<<=(1#2**PosS p)
(use "wsCs")
(use "NatLeTrans" (pt "L p"))
(simp "LDef")
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "L p"))
(simp "LDef")
(use "NatMaxUB1")
(use "mBd")
;; ?^53:(MCplDist alpha)d(ws m)((Emb alpha)(us m))<<=(1#2**m)
(simpreal "MCplSym")
(use "MCplSeqApprox" (pt "uss") (pt "Ns"))
(use "dSym")
(use "dTriang")
(use "wsDef")
(use "Pws")
(use "usDef")
(use "MCplEmb")
(use "dRefl")
(simp "usDef")
(use "Xuss")
(use "Pws")
(use "dTriang")
(use "dSym")
(use "dRefl")

;; ?^8:(1#2**n)+RealPlus(1#2**PosS p)(1#2**m)<<=(1#2**p)
(simpreal "<-" "RatPlusRealPlus")
(simpreal "<-" "RatPlusRealPlus")
(use "RatLeToRealLe")
(simp "RatPlusAssoc")
(use "RatLeTrans" (pt "(1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))"))
(use "RatLeMonPlus")
(use "RatLeMonPlus")
(ng #t)
(use "PosLeMonPosExp")
(use "NatLeTrans" (pt "L p"))
(simp "LDef")
(use "NatMaxUB2")
(use "nBd")
(use "Truth")
(ng #t)
(use "PosLeMonPosExp")
(use "NatLeTrans" (pt "L p"))
(simp "LDef")
(use "NatMaxUB2")
(use "mBd")
;; ?^81:(1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))<=(1#2**p)
(simp
 (pf "(1#2**PosS(PosS p))+(1#2**PosS p)=(1#2**PosS p)+(1#2**PosS(PosS p))"))
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(simprat "RatPlusHalfExpPosS")
(use "RatLeRefl")
(use "Truth")
(use "RatPlusComm")
;; ?^6:allnc n us n eqd uss n(Ns n(cNatPos n))
(use "usDef")
(use "Xuss")
(use "dSym")
;; Proof finished.
;; (cdp)
(save "MCplCauchyApprox")

;; Consider a metric completion.  Let ws be a Cauchy sequence of
;; points with monotone modulus M.  We show that its limit formed by
;; (MCplLim alpha)ws M is a point in the completion.

;; MCplLimMCpl
(set-goal "allnc d,ws,M(
 allnc u(X^ u -> d u u===0) ->
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) ->
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) ->
 allnc n (MCpl (cterm (u^) X^ u^))d(ws n) -> 
 allnc p,n,m(M p<=n -> M p<=m -> (MCplDist alpha)d(ws n)(ws m)<<=(1#2**p)) -> 
 allnc p,q(p<=q -> M p<=M q) ->
 (MCpl (cterm (u^) X^ u^))d((MCplLim alpha)ws M))")
(assume "d" "ws" "M" "dRefl" "dSym" "dTriang" "Pws" "wsCs" "MMon")
(intro 0)
;; 3-5
;; ?^3:allnc n X^(lft((MCplLim alpha)ws M)n)
(assume "n")
(ng #t)
(use "MCplToX" (pt "d"))
(use "Pws")
;; ?^4:MCauchy d(lft((MCplLim alpha)ws M))(rht((MCplLim alpha)ws M))
(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(ng #t)

;; To apply MCplCauchyApprox we need ussDef NsDef wsChar usDef LDef

(defnc "uss" "[n]lft(ws n)")

(assert "allnc n uss n eqd lft(ws n)")
(assume "n1")
(simp "ussDef")
(use "InitEqD")
;; Assertion proved.
(assume "ussnEq")

(defnc "Ns" "[n]rht(ws n)")

(assert "allnc n Ns n eqd rht(ws n)")
(assume "n1")
(simp "NsDef")
(use "InitEqD")
;; Assertion proved.
(assume "NsnEq")

(assert "allnc n ws n eqd (uss n)pair(Ns n)")
(assume "n1")
(simp "ussDef")
(simp "NsDef")
(ng #t)
(use "InitEqD")
(assume "wsChar")

(defnc "us" "[n]uss n(Ns n(cNatPos n))")

(assert "allnc n us n eqd uss n(Ns n(cNatPos n))")
(assume "n1")
(simp "usDef")
(use "InitEqD")
(assume "usnEq")

(defnc "L" "[p]M(PosS p)max PosS(PosS p)")

;; ?^61:d(lft(ws n)(rht(ws n)(cNatPos n)))(lft(ws m)(rht(ws m)(cNatPos m)))<<=
;;      (1#2**p)
(simp "<-" "ussnEq")
(simp "<-" "ussnEq")
(simp "<-" "NsnEq")
(simp "<-" "NsnEq")
(simp "<-" "usnEq")
(simp "<-" "usnEq")

;; ?^67:d(us n)(us m)<<=(1#2**p)
(use "MCplCauchyApprox" (pt "ws") (pt "M") (pt "uss") (pt "Ns") (pt "L"))
;; 68-78
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws")
(use "wsCs")
;; ?^73:allnc n,m X^(uss n m)
(assume "n1" "m1")
(simp "ussDef")
(use "MCplToX" (pt "d"))
(use "Pws")
;; ?^74:allnc n ws n eqd(uss n pair Ns n)
(use "wsChar")
;; ?^75:allnc n us n eqd uss n(Ns n(cNatPos n))
(use "usnEq")
;; ?^76:allnc p L p=M(PosS p)max PosS(PosS p)
(assume "p1")
(simp "LDef")
(use "Truth")
;; ?^77:L p<=n
(use "NatLeTrans" (pt "rht((MCplLim alpha)ws M)p"))
(ng #t)
(simp "LDef")
(use "Truth")
(use "nBd")
;; ?^78:L p<=m
(use "NatLeTrans" (pt "rht((MCplLim alpha)ws M)p"))
(ng #t)
(simp "LDef")
(use "Truth")
(use "mBd")
;; ?^5:Mon(rht((MCplLim alpha)ws M))
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "NatLeMonMax")
(use "MMon")
(use "p<=q")
(simp "PosToNatLe")
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "MCplLimMCpl")

;; We will prove that the metric space MCpl is complete.  This uses an
;; auxiliary lemma MCplCauchyConvMod

;; MCplCauchyConvMod
(set-goal "allnc d,uss,Ns,ws,M,us,L,w(
 allnc u(X^ u -> d u u===0) ->
 allnc u1,u2(X^ u1 -> X^ u2 -> d u1 u2===d u2 u1) -> 
 allnc u1,u2,u3(X^ u1 -> X^ u2 -> X^ u3 -> d u1 u3<<=d u1 u2+d u2 u3) -> 
 allnc n ws n eqd((uss n)pair(Ns n)) -> 
 allnc n (MCpl (cterm (u^) X^ u^))d(ws n) -> 
 allnc p,n,m(M p<=n -> M p<=m -> (MCplDist alpha)d(ws n)(ws m)<<=(1#2**p)) -> 
 allnc p,q(p<=q -> M p<=M q) ->
 allnc n us n eqd uss n(Ns n(cNatPos n)) ->
 allnc p L p=M(PosS p)max PosS(PosS p) -> 
 w eqd(us pair L) ->
 ((MCpl (cterm (u^) X^ u^))d w) ->
 allnc p,n(M p<=n -> (MCplDist alpha)d(ws n)w<<=(1#2**p)))")
(assume "d" "uss" "Ns" "ws" "M" "us" "L" "w" "dRefl" "dSym" "dTriang"	
	"wsDef" "Pws" "wsCs" "MMon" "usDef" "LDef" "wDef" "Pw"
	"p" "n" "nBd")
;; Plan.  Mimic the proof of RealCauchyConvMod.  Use MCplTriang to deal with
;; (MCplDist alpha)d(ws n)w<<=RealPlus(1#2**p)(1#2**q) by inserting ws m

(assert "allnc n Real((MCplDist alpha)d(ws n)w)")
(assume "n1")
(use "RealMCplDist")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws")
(use "Pw")
;; Assertion proved.
(assume "Rwsw")

(use "RealLeAllPlusToLe")
(autoreal)
(assume "q")
;; ?^15:(MCplDist alpha)d(ws n)w<<=RealPlus(1#2**p)(1#2**q)

(defnc "m" "(M p)max(PosS q max L(PosS q))")

(use "RealLeTrans"
     (pt "(MCplDist alpha)d(ws n)(ws m)+(MCplDist alpha)d(ws m)w"))
(use "MCplTriang")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws")
(use "Pws")
(use "Pw")
(use "RealLeMonPlus")
;; 31,32
;; ?^31:(MCplDist alpha)d(ws n)(ws m)<<=(1#2**p)
(use "wsCs")
(use "nBd")
(simp "mDef")
(use "NatMaxUB1")
;; ?^32:(MCplDist alpha)d(ws m)w<<=(1#2**q)
(simpreal (pf "(1#2**q)===RealPlus(1#2**PosS q)(1#2**PosS q)"))
;; 36,37
(use "RealLeTrans" (pt "(MCplDist alpha)d(ws m)((Emb alpha)(us m))+
                        (MCplDist alpha)d((Emb alpha)(us m))w"))
(use "MCplTriang")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws")
(use "MCplEmb")
(use "dRefl")
(use "MCplPairToX" (pt "d") (pt "L"))
(simp "<-" "wDef")
(use "Pw")
(use "Pw")
(use "RealLeMonPlus")
;; 50,51
;; ?^50:(MCplDist alpha)d(ws m)((Emb alpha)(us m))<<=(1#2**PosS q)
(simpreal "MCplSym")
(simp "usDef")
(simp "wsDef")
(use "MCauchyConvMod")
;; 60-62
(use "dSym")
(use "dTriang")
(simp "<-" "wsDef")
(use "Pws")
;; ?^63:Ns m(PosS q)<=Ns m(cNatPos m)
(assert "Mon(rht(ws m))")
(use "MCplToMon" (pt "d"))
(use "Pws")
;; Assertion proved.
(simp "wsDef")
(ng #t)
(assume "MonNsm")
(use "MonElim" (pt "Ns m"))
(use "MonNsm")

;; ?^72:PosS q<=cNatPos m
(simp "NatPosExFree")
(simp "<-" "PosToNatLe")
(simp "PosToNatToPosId")
(use "NatLeTrans" (pt "L(PosS q)"))
(simp "LDef")
(use "NatLeTrans" (pt "PosToNat(PosS(PosS(PosS q)))"))
(simp "PosToNatLe")
(use "PosLeTrans" (pt "PosS(PosS q)"))
(use "Truth")
(use "Truth")
(use "NatMaxUB2")
(simp "mDef")
(use "NatLeTrans" (pt "(PosS q max L(PosS q))"))
(use "NatMaxUB2")
(use "NatMaxUB2")
;; ?^76:Zero<m
(use "NatLtLeTrans" (pt "PosToNat(PosS(PosS(PosS q)))"))
(use "NatLt0Pos")
(use "NatLeTrans" (pt "L(PosS q)"))
(simp "LDef")
(use "NatMaxUB2")
;; ?^91:L(PosS q)<=m
(simp "mDef")
(use "NatMaxUB2")
;; ?^57:(MCpl (cterm (u^) X^ u^))d((Emb alpha)(us m))
(use "MCplEmb")
(use "dRefl")
(use "MCplPairToX" (pt "d") (pt "L"))
(simp "<-" "wDef")
(use "Pw")
(use "Pws")
(use "dTriang")
(use "dSym")
(use "dRefl")
;; ?^51:(MCplDist alpha)d((Emb alpha)(us m))w<<=(1#2**PosS q)
(simp "wDef")
(use "MCauchyConvMod")
(use "dSym")
(use "dTriang")
(simp "<-" "wDef")
(use "Pw")
;; ?^102:L(PosS q)<=m
(simp "mDef")
(use "NatMaxUB2")
;; ?^37:(1#2**q)===RealPlus(1#2**PosS q)(1#2**PosS q)
(simpreal "<-" "RatPlusRealPlus")
(use "RatEqvToRealEq")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "MCplCauchyConvMod")

;; Every Cauchy sequence ws of points in the metric completion with
;; monotone modulus M converges with the same modulus M to its limit
;; (MCplLim alpha)ws M

;; MCplComplete
(set-goal "allnc d,ws,M(
 allnc u(X^ u -> d u u===0) -> 
 allnc u,u0(X^ u -> X^ u0 -> d u u0===d u0 u) -> 
 allnc u,u0,u1(X^ u -> X^ u0 -> X^ u1 -> d u u1<<=d u u0+d u0 u1) -> 
 allnc n (MCpl (cterm (u^) X^ u^))d(ws n) -> 
 allnc p,n,m(M p<=n -> M p<=m -> (MCplDist alpha)d(ws n)(ws m)<<=(1#2**p)) -> 
 allnc p,q(p<=q -> M p<=M q) -> 
 allnc p,n(
  M p<=n -> (MCplDist alpha)d(ws n)((MCplLim alpha)ws M)<<=(1#2**p)))")
(assume "d" "ws" "M" "dRefl" "dSym" "dTriang" "Pws" "wsCs" "MMon")

(defnc "uss" "[n]lft(ws n)")
(defnc "Ns" "[n]rht(ws n)")

(assert "ws eqd([n](uss n)pair(Ns n))")
(simp "ussDef")
(simp "NsDef")
(use "InitEqD")
;; Assertion proved
(assume "wsChar")

(defnc "us" "[n]uss n(Ns n(cNatPos n))")
(defnc "L" "[p]M(PosS p)max PosS(PosS p)")

;; ?^35:
;; allnc p,n(M p<=n -> (MCplDist alpha)d(ws n)((MCplLim alpha)ws M)<<=(1#2**p))
(use "MCplCauchyConvMod" (pt "uss") (pt "Ns") (pt "us") (pt "L"))
(use "dRefl")
(use "dSym")
(use "dTriang")
(assume "n")
(simp "wsChar")
(use "InitEqD")
(use "Pws")
(use "wsCs")
(use "MMon")
(assume "n")
(simp "usDef")
(use "InitEqD")
(assume "p")
(simp "LDef")
(use "Truth")
;; ?^45:(MCplLim alpha)ws M eqd(us pair L)
(simp "MCplLim0CompRule")
;; ?^53:(([n]lft(ws n)(rht(ws n)(cNatPos n)))pair
;;       ([p]M(PosS p)max PosS(PosS p)))eqd(us pair L)
(simp "wsChar")
(ng #t)
(simp "usDef")
(simp "LDef")
(use "InitEqD")
;; ?^46:(MCpl (cterm (u^) X^ u^))d((MCplLim alpha)ws M)
(use "MCplLimMCpl")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws")
(use "wsCs")
(use "MMon")
;; Proof finished.
;; (cdp)
(save "MCplComplete")

;; Finally we prove that MCplDist is pointwise continuous.  We will
;; use that MCpl is a metric space, and hence has all properties of them.
;; We prove MCplUBAbsQuad from MtrUBAbsQuad accordingly.

;; MCplDistCont
(set-goal "allnc d,ws1,ws2,M1,M2(
 allnc u(X^ u -> d u u===0) -> 
 allnc u,u0(X^ u -> X^ u0 -> d u u0===d u0 u) -> 
 allnc u,u0,u1(X^ u -> X^ u0 -> X^ u1 -> d u u1<<=d u u0+d u0 u1) -> 
 allnc n (MCpl (cterm (u^) X^ u^))d(ws1 n) -> 
 allnc n (MCpl (cterm (u^) X^ u^))d(ws2 n) ->
 allnc p,n,m(
  M1 p<=n -> M1 p<=m -> (MCplDist alpha)d(ws1 n)(ws1 m)<<=(1#2**p)) -> 
 allnc p,n,m(
  M2 p<=n -> M2 p<=m -> (MCplDist alpha)d(ws2 n)(ws2 m)<<=(1#2**p)) -> 
 allnc p,q(p<=q -> M1 p<=M1 q) ->
 allnc p,q(p<=q -> M2 p<=M2 q) ->
 (MCplDist alpha)d((MCplLim alpha)ws1 M1)((MCplLim alpha)ws2 M2)===
 RealLim([n]((MCplDist alpha)d(ws1 n)(ws2 n)))([p]M1(PosS p)max M2(PosS p)))")
(assume "d" "ws1" "ws2" "M1" "M2" "dRefl" "dSym" "dTriang"
	"Pws1" "Pws2" "Cws1" "Cws2" "MonM1" "MonM2")

(assert "allnc n,m Real((MCplDist alpha)d(ws1 n)(ws1 m))")
(assume "n" "m")
(use "RealMCplDist")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws1")
(use "Pws1")
(assume "Rws1")

(assert "allnc n,m Real((MCplDist alpha)d(ws2 n)(ws2 m))")
(assume "n" "m")
(use "RealMCplDist")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws2")
(use "Pws2")
(assume "Rws2")

(assert "allnc n,m Real((MCplDist alpha)d(ws1 n)(ws2 m))")
(assume "n" "m")
(use "RealMCplDist")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws1")
(use "Pws2")
(assume "Rws12")

(assert "allnc p,n,m(
      M1(PosS p)max M2(PosS p)<=n -> 
      M1(PosS p)max M2(PosS p)<=m -> 
      abs((MCplDist alpha)d(ws1 n)(ws2 n)+ 
          ~((MCplDist alpha)d(ws1 m)(ws2 m)))<<=
      (1#2**p))")
(assume "p" "n" "m" "nBd" "mBd")
(inst-with-to
 "MtrUBAbsQuad"
 (py "(nat=>alpha)yprod(pos=>nat)")
 (make-cterm (pv "w") (pf "(MCpl (cterm (u^) X^ u^))d w"))
 (pt "(MCplDist alpha)d")
 "Inst" )
(use "RealLeTrans"
     (pt "(MCplDist alpha)d(ws1 n)(ws1 m)+(MCplDist alpha)d(ws2 m)(ws2 n)"))
(use "Inst")
;; 37-42
(drop "Inst")
(assume "w1" "w2")
(use "MCplSym")
(use "dRefl")
(use "dSym")
(use "dTriang")
;; 38
(drop "Inst")
(assume "w1" "w2" "w3")
(use "MCplTriang")
(use "dRefl")
(use "dSym")
(use "dTriang")
;; 39
(drop "Inst")
(use "Pws1")
;; 40
(drop "Inst")
(use "Pws1")
;; 41
(drop "Inst")
(use "Pws2")
;; 42
(drop "Inst")
(use "Pws2")

;; 36
;; (MCplDist alpha)d(ws1 n)(ws1 m)+(MCplDist alpha)d(ws2 m)(ws2 n)<<=(1#2**p)
(drop "Inst")
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 59,60
;; ?^59:(MCplDist alpha)d(ws1 n)(ws1 m)<<=(1#2**PosS p)
(use "Cws1")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "mBd")
;; ?^60:(MCplDist alpha)d(ws2 m)(ws2 n)<<=(1#2**PosS p)
(use "Cws2")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "mBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "nBd")
;; Assertion proved
(assume "Cws12")

;; ?^73:(MCplDist alpha)d((MCplLim alpha)ws1 M1)((MCplLim alpha)ws2 M2)===
;;      RealLim([n](MCplDist alpha)d(ws1 n)(ws2 n))
;;      ([p]M1(PosS p)max M2(PosS p))

(defnc "w1" "(MCplLim alpha)ws1 M1")
(defnc "w2" "(MCplLim alpha)ws2 M2")
(simp "<-" "w1Def")
(simp "<-" "w2Def")

;; ?^89:(MCplDist alpha)d w1 w2===
;;      RealLim([n](MCplDist alpha)d(ws1 n)(ws2 n))
;;      ([p]M1(PosS p)max M2(PosS p))

;; We first prove that both sides are real numbers.  This will be used
;; later again.

(assert "Real((MCplDist alpha)d w1 w2)")
(use "RealMCplDist")
(use "dRefl")
(use "dSym")
(use "dTriang")

(simp "w1Def")
(use "MCplLimMCpl")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws1")
(use "Cws1")
(use "MonM1")

(simp "w2Def")
(use "MCplLimMCpl")
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws2")
(use "Cws2")
(use "MonM2")

;; Assertion proved.
(assume "Rw12")

;; ?^111:(MCplDist alpha)d w1 w2===
;;       RealLim([n](MCplDist alpha)d(ws1 n)(ws2 n))
;;       ([p]M1(PosS p)max M2(PosS p))

(assert "Real(RealLim([n](MCplDist alpha)d(ws1 n)(ws2 n))
                     ([p]M1(PosS p)max M2(PosS p)))")
(use "RealLimReal")
;; 114-115
(assume "n")
(ng #t)
(realproof)
;; 115
(ng #t)
;; ?^119:allnc p,n,m(
;;        M1(PosS p)max M2(PosS p)<=n -> 
;;        M1(PosS p)max M2(PosS p)<=m -> 
;;        abs((MCplDist alpha)d(ws1 n)(ws2 n)+ 
;;            ~((MCplDist alpha)d(ws1 m)(ws2 m)))<<=
;;        (1#2**p))
(inst-with-to
 "MtrUBAbsQuad"
 (py "(nat=>alpha)yprod(pos=>nat)")
 (make-cterm (pv "w") (pf "(MCpl (cterm (u^) X^ u^))d w"))
 (pt "(MCplDist alpha)d")
 "Inst" )
(assume "p" "n" "m" "nBd" "mBd")
(use "RealLeTrans"
     (pt "(MCplDist alpha)d(ws1 n)(ws1 m)+(MCplDist alpha)d(ws2 m)(ws2 n)"))
(use "Inst")
;; 125-130
(drop "Inst")
(assume "w3" "w4")
(use "MCplSym")
(use "dRefl")
(use "dSym")
(use "dTriang")
;; 126
(drop "Inst")
(assume "w3" "w4" "w5")
(use "MCplTriang")
(use "dRefl")
(use "dSym")
(use "dTriang")
;; 127
(drop "Inst")
(use "Pws1")
;; 128
(drop "Inst")
(use "Pws1")
;; 129
(drop "Inst")
(use "Pws2")
;; 130
(drop "Inst")
(use "Pws2")
;; 124
;; (MCplDist alpha)d(ws1 n)(ws1 m)+(MCplDist alpha)d(ws2 m)(ws2 n)<<=(1#2**p)

(drop "Inst")
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 147,148
;; ?^147:(MCplDist alpha)d(ws1 n)(ws1 m)<<=(1#2**PosS p)
(use "Cws1")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB1")
(use "mBd")
;; ?^148:(MCplDist alpha)d(ws2 m)(ws2 n)<<=(1#2**PosS p)
(use "Cws2")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "mBd")
(use "NatLeTrans" (pt "M1(PosS p)max M2(PosS p)"))
(use "NatMaxUB2")
(use "nBd")

;; ?^116:allnc p,q(
;;        p<=q -> 
;;        ([p0]M1(PosS p0)max M2(PosS p0))p<=([p0]M1(PosS p0)max M2(PosS p0))q)
(ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
(use "MonM1")
(use "p<=q")
(use "MonM2")
(use "p<=q")
;; Assertion proved.
(assume "RLws12")

;; ?^167:(MCplDist alpha)d w1 w2===
;;       RealLim([n](MCplDist alpha)d(ws1 n)(ws2 n))
;;       ([p]M1(PosS p)max M2(PosS p))

(use "RealEqIntro1")
;; 168-170
(autoreal)

;; ?^170:all p 
;;        abs((MCplDist alpha)d w1 w2+ 
;;            ~(RealLim([n](MCplDist alpha)d(ws1 n)(ws2 n))
;;              ([p0]M1(PosS p0)max M2(PosS p0))))<<=
;;        (1#2**p)

;; This is the essential part for usage of RealEqIntro1 .  We use
;; MCplComplete to approximate w1 and w2 (formed with MCplLim),
;; RealComplete to approximate RealLim, and RealLeAbsMinus for
;; estimates.  For the given p we choose n,l large enough.

(assume "p")

(defnc "n" "M1(p+1+1+1+1)max M2(p+1+1+1+1)max(p+1+1+1+1+1)")

;; Before defining l we introduce abbreviations
;; uss1Def Ns1Def ws1Char us1Def L1Def
;; uss2Def Ns2Def ws2Char us2Def L2Def

(defnc "uss1" "[n]lft(ws1 n)")
(defnc "uss2" "[n]lft(ws2 n)")
(defnc "Ns1" "[n]rht(ws1 n)")
(defnc "Ns2" "[n]rht(ws2 n)")

;; Introduce ws1Char
(assert "allnc n ws1 n eqd (uss1 n)pair(Ns1 n)")
(assume "n1")
(simp "uss1Def")
(simp "Ns1Def")
(cases (pt "ws1 n1"))
(assume "us" "M" "ws1n1Eq")
(ng #t)
(simp "ws1n1Eq")
(use "InitEqD")
(assume "ws1Char")

;; Introduce ws2Char
(assert "allnc n ws2 n eqd (uss2 n)pair(Ns2 n)")
(assume "n1")
(simp "uss2Def")
(simp "Ns2Def")
(cases (pt "ws2 n1"))
(assume "us" "M" "ws2n2Eq")
(ng #t)
(simp "ws2n2Eq")
(use "InitEqD")
(assume "ws2Char")

(assert "allnc n,m,l Real(d(uss1 n m)(uss2 n l))")
(assume "n1" "m" "l")
(use "MtrReal")
(use "dSym")
(use "MCplPairToX" (pt "d") (pt "Ns1 n1"))
(simp "<-" "ws1Char")
(use "Pws1")
(use "MCplPairToX" (pt "d") (pt "Ns2 n1"))
(simp "<-" "ws2Char")
(use "Pws2")
;; Assertion proved.
(assume "Russ12")

(assert "allnc n,l X^(uss1 n l)")
(assume "n1" "l")
(simp "uss1Def")
(ng #t)
(use "MCplToX" (pt "d"))
(use "Pws1")
(assume "Xuss1")

(assert "allnc n,l X^(uss2 n l)")
(assume "n1" "l")
(simp "uss2Def")
(ng #t)
(use "MCplToX" (pt "d"))
(use "Pws2")
(assume "Xuss2")

(defnc "l" "Ns1 n(cNatPos n)max Ns2 n(cNatPos n)")

;; Insert d(uss1 n l)(uss2 n l)

(use "RealLeTrans"
     (pt "abs((MCplDist alpha)d w1 w2+ ~(d(uss1 n l)(uss2 n l)))+
          abs((d(uss1 n l)(uss2 n l))+
               ~(RealLim([n](MCplDist alpha)d(ws1 n)(ws2 n))
                        ([p0]M1(PosS p0)max M2(PosS p0))))"))
;; 259,260
(use "RealLeAbsMinus")
(autoreal)

;; ?^260:abs((MCplDist alpha)d w1 w2+ ~(d(uss1 n l)(uss2 n l)))+
;;       abs(d(uss1 n l)(uss2 n l)+ 
;;           ~(RealLim([n0](MCplDist alpha)d(ws1 n0)(ws2 n0))
;;             ([p0]M1(PosS p0)max M2(PosS p0))))<<=
;;       (1#2**p)
(simpreal "<-" "RealPlusHalfExpPosS")

;; ?^264:abs((MCplDist alpha)d w1 w2+ ~(d(uss1 n l)(uss2 n l)))+
;;       abs(d(uss1 n l)(uss2 n l)+ 
;;           ~(RealLim([n0](MCplDist alpha)d(ws1 n0)(ws2 n0))
;;             ([p0]M1(PosS p0)max M2(PosS p0))))<<=
;;       RealPlus(1#2**PosS p)(1#2**PosS p)

(use "RealLeMonPlus")
;; 265,266
;; ?^265:abs((MCplDist alpha)d w1 w2+ ~(d(uss1 n l)(uss2 n l)))<<=(1#2**PosS p)

;; ;; Apply RealLeAbsMinus inserting the d-term with (cNatPos n) for l.

(defnc "us1" "([n]uss1 n(Ns1 n(cNatPos n)))")
(defnc "us2" "([n]uss2 n(Ns2 n(cNatPos n)))")

(assert "allnc n Real(d(us1 n)(us2 n))")
(assume "n1")
(use "MtrReal")
(use "dSym")
(simp "us1Def")
(ng #t)
(use "Xuss1")
(simp "us2Def")
(ng #t)
(use "Xuss2")
(assume "Rus12")

(assert "allnc n X^(us1 n)")
(assume "n1")
(simp "us1Def")
(use "Xuss1")
(assume "Xus1")

(assert "allnc n X^(us2 n)")
(assume "n2")
(simp "us2Def")
(use "Xuss2")
(assume "Xus2")

;; Introduce us1Char
(assert "us1 eqd([n]lft(ws1 n)(rht(ws1 n)(cNatPos n)))")
(simp "us1Def")
(simp "uss1Def")
(simp "Ns1Def")
(use "InitEqD")
;; Assertion proved.
(assume "us1Char")

(assert "us2 eqd([n]lft(ws2 n)(rht(ws2 n)(cNatPos n)))")
(simp "us2Def")
(simp "uss2Def")
(simp "Ns2Def")
(use "InitEqD")
;; Assertion proved.
(assume "us2Char")

;; Insert d(us1 n)(us2 n)

(use "RealLeTrans"
     (pt "abs((MCplDist alpha)d w1 w2+ ~(d(us1 n)(us2 n)))+
          abs(d(us1 n)(us2 n)+ ~(d(uss1 n l)(uss2 n l)))"))
;; 314,315
(use "RealLeAbsMinus")
(autoreal)

;; ?^315:abs((MCplDist alpha)d w1 w2+ ~(d(us1 n)(us2 n)))+
;;       abs(d(us1 n)(us2 n)+ ~(d(uss1 n l)(uss2 n l)))<<=
;;       (1#2**PosS p)

(defnc "L1" "[p]M1(PosS p)max PosS(PosS p)")
(defnc "L2" "[p]M2(PosS p)max PosS(PosS p)")

(assert "allnc p,n,m(L1 p<=n -> L1 p<=m -> d(us1 n)(us1 m)<<=(1#2**p))")
(use "MCplCauchyApprox" (pt "ws1") (pt "M1") (pt "uss1") (pt "Ns1"))
;; 335-343
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws1")
(use "Cws1")
(use "Xuss1")
(use "ws1Char")
(assume "n1")
(simp "us1Def")
(use "InitEqD")
(assume "p1")
(simp "L1Def")
(use "Truth")
(assume "Cus1")

(assert "allnc p,n,m(L2 p<=n -> L2 p<=m -> d(us2 n)(us2 m)<<=(1#2**p))")
(use "MCplCauchyApprox" (pt "ws2") (pt "M2") (pt "uss2") (pt "Ns2")) 
;; 351-359
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Pws2")
(use "Cws2")
(use "Xuss2")
(use "ws2Char")
(assume "n1")
(simp "us2Def")
(use "InitEqD")
(assume "p1")
(simp "L2Def")
(use "Truth")
(assume "Cus2")

(assert "allnc p,n,m(
       L1(PosS p)max L2(PosS p)<=n -> 
       L1(PosS p)max L2(PosS p)<=m -> 
       abs(d(us1 n)(us2 n)+ ~(d(us1 m)(us2 m)))<<=(1#2**p))")
(use "MCplLimCauchy")
;; 367-373
(use "dRefl")
(use "dSym")
(use "dTriang")
(use "Xus1")
(use "Xus2")
(use "Cus1")
(use "Cus2")
(assume "Cus12")

(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 376-377
;; ?^376:abs((MCplDist alpha)d w1 w2+ ~(d(us1 n)(us2 n)))<<=(1#2**PosS(PosS p))

(simpreal "RealAbsPlusUMinus")
(simp "w1Def")
(simp "w2Def")
(simp "MCplLim0CompRule")
(simp "MCplLim0CompRule")
(simp "MCplDist0CompRule")
(simp "<-" "L1Def")
(simp "<-" "L2Def")
(simp "<-" "us1Char")
(simp "<-" "us2Char")

;; ?^389:abs(d(us1 n)(us2 n)+ 
;;       ~(RealLim([n0]d(us1 n0)(us2 n0))([p0]L1(PosS p0)max L2(PosS p0))))<<=
;;       (1#2**PosS(PosS p))

(use-with
 "RealComplete"
 (pt "[n0]d(us1 n0)(us2 n0)")
 (pt "[p0]L1(PosS p0)max L2(PosS p0)")
 "?" "?" "?" (pt "PosS(PosS p)") (pt "n") "?")
;; 390-393
(use "Rus12")
;; 391
(ng #t)
(use "Cus12")
;; 392
(ng #t)
;; ?^395:allnc p,q(p<=q -> L1(PosS p)max L2(PosS p)<=L1(PosS q)max L2(PosS q))
(assume "p1" "q1" "p1<=q1")
(use "NatLeMonMax")
(simp "L1Def")
(ng #t)
(use "NatLeMonMax")
(use "MonM1")
(use "p1<=q1")
(simp "PosToNatLe")
(use "p1<=q1")
(simp "L2Def")
(ng #t)
(use "NatLeMonMax")
(use "MonM2")
(use "p1<=q1")
(simp "PosToNatLe")
(use "p1<=q1")
;; 393
(ng #t)
;; ?^411:L1(PosS(PosS(PosS p)))max L2(PosS(PosS(PosS p)))<=n
(use "NatMaxLUB")
;; 412,413
;; ?^412:L1(PosS(PosS(PosS p)))<=n
(simp "L1Def")
(use "NatMaxLUB")
;; 415,416
;; ?^415:M1(PosS(PosS(PosS(PosS p))))<=n
;; nDef:n eqd M1(p+1+1+1+1)max M2(p+1+1+1+1)max(p+1+1+1+1+1)
(simp "nDef")
(use "NatLeTrans" (pt "M1(p+1+1+1+1)max M2(p+1+1+1+1)"))
(use "NatMaxUB1")
(use "NatMaxUB1")
;; ?^416:PosS(PosS(PosS(PosS(PosS p))))<=n
(simp "nDef")
(use "NatMaxUB2")
;; ?^413:L2(PosS(PosS(PosS p)))<=n
;; Similar to 412, with 2 for 1
(simp "L2Def")
(use "NatMaxLUB")
;; 422,423
;; ?^422:M2(PosS(PosS(PosS(PosS p))))<=n
;; nDef:n eqd M1(p+1+1+1+1)max M2(p+1+1+1+1)max(p+1+1+1+1+1)
(simp "nDef")
(simp "L2Def")
(use "NatMaxLUB")
(use "NatLeTrans" (pt "M1(p+1+1+1+1)max M2(p+1+1+1+1)"))
(use "NatMaxUB2")
(use "NatMaxUB1")
;; ?^423:PosS(PosS(PosS(PosS(PosS p))))<=n
(simp "nDef")
(use "NatMaxUB2")

;; ?^380:Real(d(us1 n)(us2 n))
(autoreal)

;; ?^377:abs(d(us1 n)(us2 n)+ ~(d(uss1 n l)(uss2 n l)))<<=(1#2**PosS(PosS p))
(simp "us1Def")
(simp "us2Def")
(ng #t)

;; ?^430:abs(d(uss1 n(Ns1 n(cNatPos n)))(uss2 n(Ns2 n(cNatPos n)))+ 
;;           ~(d(uss1 n l)(uss2 n l)))<<=
;;       (1#2**PosS(PosS p))

(use "RealLeTrans"  (pt "d(uss1 n(Ns1 n(cNatPos n)))(uss1 n l)+
                         d(uss2 n l)(uss2 n(Ns2 n(cNatPos n)))"))
;; 431,432
;; ?^431:abs(d(uss1 n(Ns1 n(cNatPos n)))(uss2 n(Ns2 n(cNatPos n)))+ 
;;           ~(d(uss1 n l)(uss2 n l)))<<=
;;       d(uss1 n(Ns1 n(cNatPos n)))(uss1 n l)+
;;       d(uss2 n l)(uss2 n(Ns2 n(cNatPos n)))

(use "MtrUBAbsQuad")
(use "dSym")
(use "dTriang")
(use "Xuss1")
(use "Xuss1")
(use "Xuss2")
(use "Xuss2")

;; ?^432:d(uss1 n(Ns1 n(cNatPos n)))(uss1 n l)+
;;       d(uss2 n l)(uss2 n(Ns2 n(cNatPos n)))<<=
;;       (1#2**PosS(PosS p))

(assert "allnc n,m,l Real(d(uss1 n m)(uss1 n l))")
(assume "n1" "m1" "l1")
(use "MtrReal")
(use "dSym")
(use "Xuss1")
(use "Xuss1")
(assume "Russ1")

(assert "allnc n,m,l Real(d(uss2 n m)(uss2 n l))")
(assume "n1" "m1" "l1")
(use "MtrReal")
(use "dSym")
(use "Xuss2")
(use "Xuss2")
(assume "Russ2")

(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 454,455
;; ?^454:d(uss1 n(Ns1 n(cNatPos n)))(uss1 n l)<<=(1#2**PosS(PosS(PosS p)))
(use "MCauchyElim" (pt "Ns1 n"))
;; 456,457
;; ?^456:MCauchy d(uss1 n)(Ns1 n)
(simp "uss1Def")
(simp "Ns1Def")
(ng #t)
(use "MCplToMCauchy")
(use "Pws1")

;; ?^457:Ns1 n(PosS(PosS(PosS p)))<=Ns1 n(cNatPos n)
(assert "Mon(rht(ws1 n))")
(use "MCplToMon" (pt "d"))
(use "Pws1")
;; Assertion proved.
(simp "ws1Char")
(ng #t)
(assume "MonNs1n")

(use "MonElim" (pt "Ns1 n"))
(use "MonNs1n")

;; ?^470:PosS(PosS(PosS p))<=cNatPos n
(simp "nDef")
(use "PosLeTrans" (pt "p+1+1+1+1+1"))
(ng #t)
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")

(simp "NatPosExFree")
(simp (pf "p+1+1+1+1+1=NatToPos(PosToNat(p+1+1+1+1+1))"))
(simp "NatToPosLe")
(simp "NatToPosToNatId")
(use "NatMaxUB2")
(simp "NatToPosToNatId")
(use "NatLtLeTrans" (pt "PosToNat(p+1+1+1+1+1)"))
(use "NatLtZeroPosToNat")
(use "NatMaxUB2")
(use "NatLtZeroPosToNat")
(simp "NatToPosToNatId")
(use "Truth")

;; ?^458:Ns1 n(PosS(PosS(PosS p)))<=l
(simp "lDef")

(assert "Mon(rht(ws1 n))")
(use "MCplToMon" (pt "d"))
(use "Pws1")
;; Assertion proved.
(simp "ws1Char")
(ng #t)
(assume "MonNs1n")

(use "NatLeTrans" (pt "Ns1 n(cNatPos n)"))
(use "MonElim" (pt "Ns1 n"))
(use "MonNs1n")

;; ?^498:PosS(PosS(PosS p))<=cNatPos n
(simp "nDef")
(use "PosLeTrans" (pt "p+1+1+1+1+1"))
(ng #t)
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")

;; ?^501:p+1+1+1+1+1<=cNatPos(M1(p+1+1+1+1)max M2(p+1+1+1+1)max(p+1+1+1+1+1))
(simp "NatPosExFree")
(use "PosLeTrans" (pt "NatToPos(PosToNat(p+1+1+1+1+1))"))
(simp "NatToPosToNatId")
(use "Truth")
(simp "NatToPosLe")
(use "NatMaxUB2")
(use "NatLtLeTrans" (pt "PosToNat(p+1+1+1+1)"))
(use "NatLtZeroPosToNat")
(use "NatLeTrans" (pt "PosToNat(p+1+1+1+1+1)"))
(simp "PosToNatLe")
(use "Truth")
(use "NatMaxUB2")
(use "NatLtZeroPosToNat")

;; ?^496:Ns1 n(cNatPos n)<=Ns1 n(cNatPos n)max Ns2 n(cNatPos n)
(use "NatMaxUB1")

;; ?^455:d(uss2 n l)(uss2 n(Ns2 n(cNatPos n)))<<=(1#2**PosS(PosS(PosS p)))
;; Similar to 454, with 2 for 1 and lhs reversed
;; ?^454:d(uss1 n(Ns1 n(cNatPos n)))(uss1 n l)<<=(1#2**PosS(PosS(PosS p)))
(use "MCauchyElim" (pt "Ns2 n"))
;; 517,518
;; ?^517:MCauchy d(uss2 n)(Ns2 n)
(simp "uss2Def")
(simp "Ns2Def")
(ng #t)
(use "MCplToMCauchy")
(use "Pws2")

;; ?^518:Ns2 n(PosS(PosS(PosS p)))<=Ns2 n(cNatPos n)
(assert "Mon(rht(ws2 n))")
(use "MCplToMon" (pt "d"))
(use "Pws2")
;; Assertion proved.
(simp "ws2Char")
(ng #t)
(assume "MonNs2n")

(use "NatLeTrans" (pt "Ns2 n(cNatPos n)"))
(use "MonElim" (pt "Ns2 n"))
(use "MonNs2n")

;; ?^533:PosS(PosS(PosS p))<=cNatPos n
(simp "nDef")
(use "PosLeTrans" (pt "p+1+1+1+1+1"))
(ng #t)
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")

;; ?^536:p+1+1+1+1+1<=cNatPos(M1(p+1+1+1+1)max M2(p+1+1+1+1)max(p+1+1+1+1+1))
(simp "NatPosExFree")
(use "PosLeTrans" (pt "NatToPos(PosToNat(p+1+1+1+1+1))"))
(simp "NatToPosToNatId")
(use "Truth")
(simp "NatToPosLe")
(use "NatMaxUB2")
(use "NatLtLeTrans" (pt "PosToNat(p+1+1+1+1)"))
(use "NatLtZeroPosToNat")
(use "NatLeTrans" (pt "PosToNat(p+1+1+1+1+1)"))
(simp "PosToNatLe")
(use "Truth")
(use "NatMaxUB2")
(use "NatLtZeroPosToNat")

;; ?^531:Ns2 n(cNatPos n)<=l
(simp "lDef")
(use "NatMaxUB2")

;; ?^519:Ns2 n(PosS(PosS(PosS p)))<=Ns2 n(cNatPos n)
(assert "Mon(rht(ws2 n))")
(use "MCplToMon" (pt "d"))
(use "Pws2")
;; Assertion proved.
(simp "ws2Char")
(ng #t)
(assume "MonNs2n")

(use "MonElim" (pt "Ns2 n"))
(use "MonNs2n")

;; ?^560:PosS(PosS(PosS p))<=cNatPos n
(simp "nDef")
(use "PosLeTrans" (pt "p+1+1+1+1+1"))
(ng #t)
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")

(simp "NatPosExFree")
(simp (pf "p+1+1+1+1+1=NatToPos(PosToNat(p+1+1+1+1+1))"))
(simp "NatToPosLe")
(simp "NatToPosToNatId")
(use "NatMaxUB2")
(simp "NatToPosToNatId")
(use "NatLtLeTrans" (pt "PosToNat(p+1+1+1+1+1)"))
(use "NatLtZeroPosToNat")
(use "NatMaxUB2")
(use "NatLtZeroPosToNat")
(simp "NatToPosToNatId")
(use "Truth")

;; ?^266:abs(d(uss1 n l)(uss2 n l)+ 
;;           ~(RealLim([n0](MCplDist alpha)d(ws1 n0)(ws2 n0))
;;             ([p0]M1(PosS p0)max M2(PosS p0))))<<=
;;       (1#2**PosS p)

;; Insert (MCplDist alpha)d(ws1 n)(ws2 n) and use RealComplete
(use "RealLeTrans"
     (pt "abs(d(uss1 n l)(uss2 n l)+ ~((MCplDist alpha)d(ws1 n)(ws2 n)))+
          abs((MCplDist alpha)d(ws1 n)(ws2 n)+
              ~(RealLim([n0](MCplDist alpha)d(ws1 n0)(ws2 n0))
              ([p0]M1(PosS p0)max M2(PosS p0))))"))
(use "RealLeAbsMinus")
(autoreal)

;; ?^579:abs(d(uss1 n l)(uss2 n l)+ ~((MCplDist alpha)d(ws1 n)(ws2 n)))+
;;       abs((MCplDist alpha)d(ws1 n)(ws2 n)+ 
;;           ~(RealLim([n0](MCplDist alpha)d(ws1 n0)(ws2 n0))
;;             ([p0]M1(PosS p0)max M2(PosS p0))))<<=
;;       (1#2**PosS p)
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 584,585
;; ?^584:abs(d(uss1 n l)(uss2 n l)+ ~((MCplDist alpha)d(ws1 n)(ws2 n)))<<=
;;       (1#2**PosS(PosS p))
(simp "ws1Char")
(simp "ws2Char")
(simp "MCplDist0CompRule")
(use-with
 "RealComplete"
 (pt "[l]d(uss1 n l)(uss2 n l)")
 (pt "([p0]Ns1 n(PosS p0)max Ns2 n(PosS p0))")
 "?" "?" "?" (pt "PosS(PosS p)") (pt "l") "?")
;; 589-592
(assume "n1")
(ng #t)
(autoreal)
;; 590
(ng #t)
;; ?^595:allnc p,n0,m(
;;        Ns1 n(PosS p)max Ns2 n(PosS p)<=n0 -> 
;;        Ns1 n(PosS p)max Ns2 n(PosS p)<=m -> 
;;        abs(d(uss1 n n0)(uss2 n n0)+ ~(d(uss1 n m)(uss2 n m)))<<=(1#2**p))
(assume "p1" "n1" "m1" "n1Bd" "m1Bd")
(use "RealLeTrans" (pt "d(uss1 n n1)(uss1 n m1)+d(uss2 n m1)(uss2 n n1)"))
(use "MtrUBAbsQuad")
(use "dSym")
(use "dTriang")
(use "Xuss1")
(use "Xuss1")
(use "Xuss2")
(use "Xuss2")

;; ?^598:d(uss1 n n1)(uss1 n m1)+d(uss2 n m1)(uss2 n n1)<<=(1#2**p1)
(assert "allnc n,m,l Real(d(uss1 n m)(uss1 n l))")
(assume "n2" "m2" "l2")
(use "MtrReal")
(use "dSym")
(use "Xuss1")
(use "Xuss1")
(assume "Russ1")

(assert "allnc n,m,l Real(d(uss2 n m)(uss2 n l))")
(assume "n2" "m2" "l2")
(use "MtrReal")
(use "dSym")
(use "Xuss2")
(use "Xuss2")
(assume "Russ2")

(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlus")
;; 620,621
;; ?^620:d(uss1 n n1)(uss1 n m1)<<=(1#2**PosS p1)
(use "MCauchyElim" (pt "Ns1 n"))
;; 622,623
;; ?^622:MCauchy d(uss1 n)(Ns1 n)
(simp "uss1Def")
(simp "Ns1Def")
(ng #t)
(use "MCplToMCauchy")
(use "Pws1")
;; ?^623:Ns1 n(PosS p1)<=n1
(use "NatLeTrans" (pt "Ns1 n(PosS p1)max Ns2 n(PosS p1)"))
(use "NatMaxUB1")
(use "n1Bd")
;; ?^624:Ns1 n(PosS p1)<=m1
(use "NatLeTrans" (pt "Ns1 n(PosS p1)max Ns2 n(PosS p1)"))
(use "NatMaxUB1")
(use "m1Bd")

;; ?^621:d(uss2 n m1)(uss2 n n1)<<=(1#2**PosS p1)
(use "MCauchyElim" (pt "Ns2 n"))
;; 633,634
;; ?^633:MCauchy d(uss2 n)(Ns2 n)
(simp "uss2Def")
(simp "Ns2Def")
(ng #t)
(use "MCplToMCauchy")
(use "Pws2")
;; ?^634:Ns2 n(PosS p1)<=m1
(use "NatLeTrans" (pt "Ns1 n(PosS p1)max Ns2 n(PosS p1)"))
(use "NatMaxUB2")
(use "m1Bd")
;; ?^635:Ns2 n(PosS p1)<=n1
(use "NatLeTrans" (pt "Ns1 n(PosS p1)max Ns2 n(PosS p1)"))
(use "NatMaxUB2")
(use "n1Bd")

;; 591
(ng #t)
;; ?^644:allnc p,q(
;;        p<=q -> 
;;        Ns1 n(PosS p)max Ns2 n(PosS p)<=Ns1 n(PosS q)max Ns2 n(PosS q))
(assume "p1" "q1" "p1<=q1")
(use "NatLeMonMax")
;; 646,647
;; ?^646:Ns1 n(PosS p1)<=Ns1 n(PosS q1)
(assert "Mon(rht(ws1 n))")
(use "MCplToMon" (pt "d"))
(use "Pws1")
;; Assertion proved
(simp "Ns1Def")
(ng #t)
(assume "MonNs1")
(use "MonElim")
(use "MonNs1")
(use "p1<=q1")

;; ?^647:Ns2 n(PosS p1)<=Ns2 n(PosS q1)
(assert "Mon(rht(ws2 n))")
(use "MCplToMon" (pt "d"))
(use "Pws2")
;; Assertion proved
(simp "Ns2Def")
(ng #t)
(assume "MonNs2")
(use "MonElim")
(use "MonNs2")
(use "p1<=q1")

;; 592
(ng #t)
;; ?^664:Ns1 n(PosS(PosS(PosS p)))max Ns2 n(PosS(PosS(PosS p)))<=l
(simp "lDef")
(use "NatLeMonMax")
;; 666,667
;; ?^666:Ns1 n(PosS(PosS(PosS p)))<=Ns1 n(cNatPos n)
(assert "Mon(rht(ws1 n))")
(use "MCplToMon" (pt "d"))
(use "Pws1")
;; Assertion proved.
(simp "ws1Char")
(ng #t)
(assume "MonNs1n")
(use "MonElim" (pt "Ns1 n"))
(use "MonNs1n")

;; ?^675:PosS(PosS(PosS p))<=cNatPos n ;same goal as 560
(simp "nDef")
(use "PosLeTrans" (pt "p+1+1+1+1+1"))
(ng #t)
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")

(simp "NatPosExFree")
(simp (pf "p+1+1+1+1+1=NatToPos(PosToNat(p+1+1+1+1+1))"))
(simp "NatToPosLe")
(simp "NatToPosToNatId")
(use "NatMaxUB2")
(simp "NatToPosToNatId")
(use "NatLtLeTrans" (pt "PosToNat(p+1+1+1+1+1)"))
(use "NatLtZeroPosToNat")
(use "NatMaxUB2")
(use "NatLtZeroPosToNat")
(simp "NatToPosToNatId")
(use "Truth")

;; ?^667:Ns2 n(PosS(PosS(PosS p)))<=Ns2 n(cNatPos n)
;; Similar to 666, now with 2 for 1.  We do it again
(assert "Mon(rht(ws2 n))")
(use "MCplToMon" (pt "d"))
(use "Pws2")
;; Assertion proved.
(simp "ws2Char")
(ng #t)
(assume "MonNs2n")

(use "MonElim" (pt "Ns2 n"))
(use "MonNs2n")
;; ?^848:PosS(PosS(PosS p))<=cNatPos n ;same goal as 502
(simp "nDef")
(simp "NatPosExFree")
;; 702
;; PosS(PosS(PosS p))<=NatToPos(M1(p+1+1+1+1)max M2(p+1+1+1+1)max(p+1+1+1+1+1))
(simp (pf "PosS(PosS(PosS p))=NatToPos(PosToNat(PosS(PosS(PosS p))))"))
(simp "NatToPosLe")
(use "NatLeTrans" (pt "PosToNat(p+1+1+1+1+1)"))
(simp "PosToNatLe")
(ng #t)
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")

;; ?^709:p+1+1+1+1+1<=M1(p+1+1+1+1)max M2(p+1+1+1+1)max(p+1+1+1+1+1)
(use "NatMaxUB2")
(use "NatLtLeTrans" (pt "PosToNat(p+1+1+1+1+1)"))
(use "NatLtZeroPosToNat")
(use "NatMaxUB2")
(use "NatLtZeroPosToNat")
(simp "NatToPosToNatId")
(use "Truth")

;; ?^585:abs((MCplDist alpha)d(ws1 n)(ws2 n)+ 
;;           ~(RealLim([n0](MCplDist alpha)d(ws1 n0)(ws2 n0))
;;             ([p0]M1(PosS p0)max M2(PosS p0))))<<=
;;       (1#2**PosS(PosS p))
;; Second half of the splitting in goal 579.  Use RealComplete
(use-with
 "RealComplete"
 (pt "[n](MCplDist alpha)d(ws1 n)(ws2 n)")
 (pt "([p0]M1(PosS p0)max M2(PosS p0))")
 "?" "?" "?" (pt "PosS(PosS p)") (pt "n") "?")
;; 717-720
(assume "n1")
(ng #t)
(autoreal)
(ng #t)

;; ?^723:allnc p,n,m(
;;        M1(PosS p)max M2(PosS p)<=n -> 
;;        M1(PosS p)max M2(PosS p)<=m -> 
;;        abs((MCplDist alpha)d(ws1 n)(ws2 n)+ 
;;            ~((MCplDist alpha)d(ws1 m)(ws2 m)))<<=
;;        (1#2**p))
(use "Cws12")
;; 719
(ng #t)
;; ?^724:allnc p,q(p<=q -> M1(PosS p)max M2(PosS p)<=M1(PosS q)max M2(PosS q))
(assume "p1" "q1" "p1<=q1")
(use "NatLeMonMax")
(use "MonM1")
(use "p1<=q1")
(use "MonM2")
(use "p1<=q1")
;; 720
(ng #t)
;; ?^730:M1(PosS(PosS(PosS p)))max M2(PosS(PosS(PosS p)))<=n
(simp "nDef")
(use "NatLeTrans" (pt "M1(p+1+1+1+1)max M2(p+1+1+1+1)"))
(use "NatLeMonMax")
;; 734,735
;; ?^734:M1(PosS(PosS(PosS p)))<=M1(p+1+1+1+1)
(use "MonM1")
(use "Truth")
;; ?^735:M2(PosS(PosS(PosS p)))<=M2(p+1+1+1+1)
(use "MonM2")
(use "Truth")

;; ?^733:M1(p+1+1+1+1)max M2(p+1+1+1+1)<=
;;       M1(p+1+1+1+1)max M2(p+1+1+1+1)max(p+1+1+1+1+1)
(use "NatMaxUB1")
;; Proof finished.
;; (cp)
(save "MCplDistCont")

