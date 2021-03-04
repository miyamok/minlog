;; 2021-02-26.  examples/analysis/sdlim.scm
;; Based on Franziskus Wiesnet's CoILim.scm and CoIClosure.scm
;; New: Cauchy sequence with modulus instead of converging sequence.
;; The latter needs the limit, which can be computed from the Cs

;; (load "~/git/minlog/init.scm")

(load "~/git/minlog/examples/analysis/sddiv.scm")
;; (set! COMMENT-FLAG #t)

;; CoIDoubleClosure
(set-goal "allnc x(
     CoI x -> 
     exr d,e,x0(
      Sd d andd Sd e andd abs x0<<=1 andr CoI x0 andl x===(1#4)*(x0+e+2*d)))")
(assume "x" "CoIx")
(inst-with-to "CoIClosure" (pt "x") "CoIx" "CoIInst")
(by-assume "CoIInst" "d" "CoIInst1")
(by-assume "CoIInst1" "x0" "CoIInst2")
(elim "CoIInst2")
(assume "Sdd" "Conj0")
(elim "Conj0")
(drop "Conj0")
(assume "CoIx0" "xDef")
(inst-with-to "CoIClosure" (pt "x0") "CoIx0" "CoIInst3")
(by-assume "CoIInst3" "e" "CoIInst4")
(by-assume "CoIInst4" "x1" "CoIInst5")
(elim "CoIInst5")
(assume "Sde" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume  "CoIx1" "x0Def")
(intro 0 (pt "d"))
(intro 0 (pt "e"))
(intro 0 (pt "x1"))
(split)
(use "Sdd")
(split)
(use "Sde")
(split)
(use "CoIToBd")
(use "CoIx1")
(split)
(use "CoIx1")
(use "RealEqTrans" (pt "(1#2)*(x0+d)"))
(use "xDef")
(simpreal "x0Def")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(ng)
(simpreal "RealTimesAssoc")
(ng)
(assert "d#2 === (2*d#4)")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(ng)
(assume "n")
(assert "d*4 = d*2*2")
(simp "<-" "IntTimesAssoc")
(ng)
(use "Truth")
(assume "Simp")
(simp "Simp")
(simp "IntTimesComm")
(use "IntTimesAssoc")
(assume "simp")
(simpreal "<-" "simp")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIDoubleClosure")

(pp (rename-variables (nt (proof-to-extracted-term))))

;; [u] [if (cCoIClosure u)
;;         ([s,u0][if (cCoIClosure u0) ([s0,u1]s pair s0 pair u1)])]

(ppc (rename-variables (nt (proof-to-extracted-term))))

;; [u]
;;  [case (cCoIClosure u)
;;    (s pair u0 -> [case (cCoIClosure u0) (s0 pair u1 -> s pair s0 pair u1)])]

(add-sound "CoIDoubleClosure")

;; ok, CoIDoubleClosureSound has been added as a new theorem:

;; allnc x,u^(
;;  CoIMR x u^ -> 
;;  (ExRTMR int
;;    sd yprod sd yprod ai
;;    (cterm (d,(sd yprod sd yprod ai)^) 
;;    (ExRTMR int
;;      sd yprod sd yprod ai
;;      (cterm (e,(sd yprod sd yprod ai)^0) 
;;      (ExRTMR rea
;;        sd yprod sd yprod ai
;;        (cterm (x0,(sd yprod sd yprod ai)^1) 
;;        (AndDMR (cterm (s^) SdMR d s^)
;;          (cterm (su^) 
;;          (AndDMR (cterm (s^) SdMR e s^)
;;            (cterm (u^0) 
;;            (AndRMR (cterm () abs x0<<=1)
;;              (cterm (u^1) 
;;              (AndLMR (cterm (u^2) CoIMR x0 u^2)
;;                (cterm () x===(1#4)*(x0+e+2*d)))
;;              u^1))
;;            u^0))
;;          su^))
;;        (sd yprod sd yprod ai)^1))
;;      (sd yprod sd yprod ai)^0))
;;    (sd yprod sd yprod ai)^))
;;  (cCoIDoubleClosure u^))

;; with computation rule

;; cCoIDoubleClosure eqd
;; ([u]
;;   [if (cCoIClosure u) ([s,u0][if (cCoIClosure u0) ([s0,u1]s pair s0 pair u1)])])

(deanimate "CoIDoubleClosure")

;; CoITripleClosure
(set-goal "allnc x(
     CoI x ->
     exr d1,d2,d3,x0(
      Sd d1 andd
      Sd d2 andd
      Sd d3 andd abs x0<<=1 andr CoI x0 andl x===(1#8)*(x0+d1+2*d2+4*d3)))")
(assume "x" "CoIx")
(inst-with-to "CoIDoubleClosure" (pt "x") "CoIx" "CoIxInst")
(by-assume "CoIxInst" "d" "CoIxInst1")
(by-assume "CoIxInst1" "d0" "CoIxInst2")
(by-assume "CoIxInst2" "x0" "CoIxInst3")
(elim "CoIxInst3")
(assume "Sdd" "Conj0")
(drop "CoIxInst3")
(elim "Conj0")
(assume "Sdd0" "Conj1")
(drop "Conj0")
(elim "Conj1")
(assume "x0Bd" "Conj2")
(drop "Conj1")
(elim "Conj2")
(assume "CoIx0" "xDef")
(drop "Conj2")
(inst-with-to "CoIClosure" (pt "x0") "CoIx0" "CoIx0Inst")
(by-assume "CoIx0Inst" "d1" "CoIx0Inst1")
(by-assume "CoIx0Inst1" "x1" "CoIx0Inst2")
(elim "CoIx0Inst2")
(assume "Sdd1" "Conj3")
(drop "CoIx0Inst2")
(elim "Conj3")
(assume "CoIx1" "x0Def")
(drop "Conj3")
(intro 0 (pt "d1"))
(intro 0 (pt "d0"))
(intro 0 (pt "d"))
(intro 0 (pt "x1"))
(split)
(use "Sdd1")
(split)
(use "Sdd0")
(split)
(use "Sdd")
(split)
(use "CoIToBd")
(use "CoIx1")
(split)
(use "CoIx1")
(simpreal "xDef")
(simpreal "x0Def")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(ng)
(simpreal "RealTimesAssoc")
(ng)
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqRefl")
(realproof)
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(ng)
(assume "n")
(assert "d0*8 = d0*2*4")
(simp "<-" "IntTimesAssoc")
(ng)
(use "Truth")
(assume "Simp")
(simp "Simp")
(assert "d0*2=2*d0")
(use "IntTimesComm")
(assume "Simp1")
(simp "Simp1")
(use "Truth")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(ng)
(assume "n")
(assert "2*d=d*2")
(use "IntTimesComm")
(assume "Simp1")
(simp "Simp1")
(assert "4*d = d*4")
(use "IntTimesComm")
(assume "Simp2")
(simp "Simp2")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoITripleClosure")

(pp (rename-variables (nt (proof-to-extracted-term))))

;; [u]
;;  [if (cCoIDoubleClosure u)
;;    ([s,su]
;;     [if su
;;       ([s0,u0][if (cCoIClosure u0) ([s1,u1]s1 pair s0 pair s pair u1)])])]

(ppc (rename-variables (nt (proof-to-extracted-term))))

;; [u]
;;  [case (cCoIDoubleClosure u)
;;    (s pair su -> 
;;    [case su
;;      (s0 pair u0 -> 
;;      [case (cCoIClosure u0) (s1 pair u1 -> s1 pair s0 pair s pair u1)])])]

(add-sound "CoITripleClosure")

;; ok, CoITripleClosureSound has been added as a new theorem:

;; allnc x,u^(
;;  CoIMR x u^ -> 
;;  (ExRTMR int
;;    sd yprod sd yprod sd yprod ai
;;    (cterm (d,(sd yprod sd yprod sd yprod ai)^) 
;;    (ExRTMR int
;;      sd yprod sd yprod sd yprod ai
;;      (cterm (d0,(sd yprod sd yprod sd yprod ai)^0) 
;;      (ExRTMR int
;;        sd yprod sd yprod sd yprod ai
;;        (cterm (d1,(sd yprod sd yprod sd yprod ai)^1) 
;;        (ExRTMR rea
;;          sd yprod sd yprod sd yprod ai
;;          (cterm (x0,(sd yprod sd yprod sd yprod ai)^2) 
;;          (AndDMR (cterm (s^) SdMR d s^)
;;            (cterm ((sd yprod sd yprod ai)^3) 
;;            (AndDMR (cterm (s^) SdMR d0 s^)
;;              (cterm (su^) 
;;              (AndDMR (cterm (s^) SdMR d1 s^)
;;                (cterm (u^0) 
;;                (AndRMR (cterm () abs x0<<=1)
;;                  (cterm (u^1) 
;;                  (AndLMR (cterm (u^2) CoIMR x0 u^2)
;;                    (cterm () x===(1#8)*(x0+d+2*d0+4*d1)))
;;                  u^1))
;;                u^0))
;;              su^))
;;            (sd yprod sd yprod ai)^3))
;;          (sd yprod sd yprod sd yprod ai)^2))
;;        (sd yprod sd yprod sd yprod ai)^1))
;;      (sd yprod sd yprod sd yprod ai)^0))
;;    (sd yprod sd yprod sd yprod ai)^))
;;  (cCoITripleClosure u^))

;; with computation rule

;; cCoITripleClosure eqd
;; ([u]
;;   [if (cCoIDoubleClosure u)
;;     ([s,su]
;;     [if su ([s0,u0][if (cCoIClosure u0) ([s1,u1]s1 pair s0 pair s pair u1)])])])

(deanimate "CoITripleClosure")

;; Auxiliary lemmas for SdLim.  From sddiv we have
;; (pp "CoIToBd")
;; all x(CoI x -> abs x<<=1)

;; CoIToLowBd
(set-goal "all x(CoI x -> ~1<<=x)")
(assume "x" "CoIx")
(use "RealLeUMinusInv")
(use "RealLeTrans" (pt "abs x"))
(simpreal "<-" "RealAbsUMinus")
(use "RealLeIdAbs")
(autoreal)
(use "CoIToBd")
(use "CoIx")
;; Proof finished.
;; (cdp)
(save "CoIToLowBd")

;; CoIToUpBd
(set-goal "all x(CoI x -> x<<=1)")
(assume "x" "CoIx")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeIdAbs")
(realproof)
(use "CoIToBd")
(use "CoIx")
;; Proof finished.
;; (cdp)
(save "CoIToUpBd")

;; SdToLowBd
(set-goal "all d(Sd d -> RealPlus 0 ~1<<=d)")
(assume "d")
(elim)
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "SdToLowBd")

;; SdToUpBd
(set-goal "all d(Sd d -> d<<=RealPlus 1 0)")
(assume "d")
(elim)
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "SdToUpBd")

(add-var-name "xs" (py "nat=>rea"))
(add-var-name "us" (py "nat=>ai"))
(add-var-name "Mus" (py "(pos=>nat)yprod(nat=>ai)"))

;; CoILimToBd
(set-goal "all x,xs,M(Real x -> all n(CoI (xs n)) ->
  all p,n (M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) -> abs x<<=1)")
(assume "x" "xs" "M" "Rx" "AllCoI" "xsTox")
(use "RealLeAllPlusToLe")
(autoreal)
(assume "p")
(assert "Real(xs(M p))")
(use "CoIToReal")
(use "AllCoI")
(assume "RealxsMp")
(use "RealLeTrans" (pt "abs(xs(M p)) + abs(x+ ~(xs(M p)))"))
(ng)
(use "RealLeTrans"  (pt "abs(xs(M p) + (x+ ~(xs(M p))))"))
(simpreal "RealPlusComm")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "(~(xs(M p))+xs(M p)) === 0"))
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(simpreal "RealPlusComm")
(use "RealPlusMinusZero")
(autoreal)
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "CoIToBd")
(use "AllCoI")
(simpreal "<-" "RealAbsUMinus")
(ng)
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
(simpreal "RealPlusComm")
(use "xsTox")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoILimToBd")

;; For CoIToCoIDoublePlusOne we use (from sddiv)
;; (pp "CoIDivSatCoIClAuxR")
;; allnc x,y(
;;  CoI x -> 
;;  CoI y -> (1#4)<<=y -> abs x<<=y -> 0<<=x -> CoI(4*((1#2)*(x+ ~((1#2)*y)))))

;; CoIToCoIDoublePlusOne
(set-goal "allnc x(CoI x -> 0<<=x -> CoI(2*x+ IntN 1))")
(assume "x" "CoIx" "0<<=x")
(assert "2*x+IntN 1===4*((1#2)*(x+ ~(1#2)*1))")
(ng)
(simpreal "RealTimesAssoc")
(ng)
(simpreal "RealTimesPlusDistr")
(ng)
(use "RealEqRefl")
(autoreal)
;; Assertion proved.
(assume "Eq")
(ng)
(simpreal "Eq")
(use-with "CoIDivSatCoIClAuxR"
 (pt "x") (pt "RealPlus 0 1") "CoIx" "CoIOne" "?" "?" "?")
(use "RatLeToRealLe")
(use "Truth")
(use "CoIToBd")
(use "CoIx")
(use "0<<=x")
;; Proof finished.
;; (cdp)
(save "CoIToCoIDoublePlusOne")

;; (pp (rename-variables (nt (proof-to-extracted-term))))
;; [u]cCoICompat(cCoIDivSatCoIClAuxR u cCoIOne)

(add-sound "CoIToCoIDoublePlusOne")

;; ok, CoIToCoIDoublePlusOneSound has been added as a new theorem:

;; allnc x,u^(CoIMR x u^ -> 0<<=x -> CoIMR(2*x+IntN 1)(cCoIToCoIDoublePlusOne u^))

;; with computation rule

;; cCoIToCoIDoublePlusOne eqd([u]cCoICompat(cCoIDivSatCoIClAuxR u cCoIOne))

(deanimate "CoIToCoIDoublePlusOne")

;; For SdLimAuxL we use (from sddiv)
;; (pp "CoIDivSatCoIClAuxL")
;; allnc x,y(
;;  CoI x -> 
;;  CoI y -> (1#4)<<=y -> abs x<<=y -> x<<=0 -> CoI(4*((1#2)*(x+(1#2)*y))))

;; CoIToCoIDoubleMinusOne
(set-goal "allnc x(CoI x -> x<<=0 -> CoI(2*x+1))")
(assume "x" "CoIx" "x<<=0")
(assert "2*x+1===4*((1#2)*(x+RealTimes(1#2)1))")
(ng)
(simpreal "RealTimesAssoc")
(ng)
(simpreal "RealTimesPlusDistr")
(ng)
(use "RealEqRefl")
(autoreal)
;; Assertion proved.
(assume "Eq")
(simpreal "Eq")
(use-with "CoIDivSatCoIClAuxL"
	  (pt "x") (pt "RealPlus 0 1") "CoIx""CoIOne" "?" "?" "?")
(use "RatLeToRealLe")
(use "Truth")
(use "CoIToBd")
(use "CoIx")
(use "x<<=0")
;; Proof finished.
;; (cdp)
(save "CoIToCoIDoubleMinusOne")

;; (pp (rename-variables (nt (proof-to-extracted-term))))
;; [u]cCoICompat(cCoIDivSatCoIClAuxL u cCoIOne)

(add-sound "CoIToCoIDoubleMinusOne")

;; ok, CoIToCoIDoubleMinusOneSound has been added as a new theorem:

;; allnc x,u^(CoIMR x u^ -> x<<=0 -> CoIMR(2*x+1)(cCoIToCoIDoubleMinusOne u^))

;; with computation rule

;; cCoIToCoIDoubleMinusOne eqd([u]cCoICompat(cCoIDivSatCoIClAuxL u cCoIOne))

(deanimate "CoIToCoIDoubleMinusOne")

;; Need 0<<=xs(M 3+n) from xsCs and (1#8)<<=xs(M 3)

;; RealPosToSqPos
(set-goal "all xs,M(
     all n CoI(xs n) -> 
     all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
     (1#8)<<=xs(M 3) -> all n 0<<=xs(M 3+n))")
(assume "xs" "M" "AllCoI" "xsCs" "1/8<=xsM3" "n")
(assert "Real(xs(M 3+n))")
 (use "CoIToReal")
(use "AllCoI")
;; Assertion proved.
(assume "RHyp")
(simpreal (pf "0===RealUMinus(1#2**3)+(1#2**3)"))
(use "RealLeTrans" (pt "RealUMinus(1#2**3)+xs(M 3)"))
(use "RealLeMonPlusR")
(autoreal)
(use "1/8<=xsM3")
(use "RealLePlusRInv")
(autoreal)
(simpreal "RealPlusComm")
(use "RealLeTrans" (pt "xs(M 3+n)+ ~(xs(M 3+n))+xs(M 3)"))
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusComm")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlusR")
(autoreal)
(simpreal "RealPlusComm")
(use "RealLeTrans" (pt "abs(xs(M 3)+ ~(xs(M 3+n)))"))
(use "RealLeIdAbs")
(autoreal)
(use "xsCs")
(use "Truth")
(use "Truth")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealPosToSqPos")

;; RealPosToLimPos
(set-goal "all x,xs,M(
     Real x -> 
     all n CoI(xs n) -> 
     all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) -> (1#8)<<=xs(M 3) -> 0<<=x)")
(assume "x" "xs" "M" "Rx" "AllCoI" "xsTox" "1/8<=xsM3")
(simpreal (pf "0===RealUMinus(1#8)+(1#8)"))
(use "RealLeTrans" (pt "RealUMinus(1#8)+xs(M 3)"))
(use "RealLeMonPlusR")
(autoreal)
(use "1/8<=xsM3")
(use "RealLePlusRInv")
(autoreal)
(use "RealLeTrans" (pt "x+ ~x+xs(M 3)"))
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusComm")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(use "RealLeTrans" (pt "x+abs(~x+xs(M 3))"))
(use "RealLeMonPlusR")
(autoreal)
(use "RealLeIdAbs")
(autoreal)
(simpreal (pf "(1#8)+x===x+(1#8)"))
(use "RealLeMonPlusR")
(autoreal)
(simpreal "RealPlusComm")
(use-with "xsTox" (pt "3") (pt "M 3") "Truth")
(autoreal)
(use "RealPlusComm")
(autoreal)
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "RealPosToLimPos")

;; RealPosToAbsBd
(set-goal "all x,xs,M(
     Real x ->
     all n CoI(xs n) ->
     all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) ->
     (1#8)<<=xs(M 3) -> abs(2*x+ ~1)<<=1)")
(assume "x" "xs" "M" "Rx" "AllCoI" "xsTox" "1/8<=xsM3")
(use "RealLeAbs")
(ng)
(use "RealLeTrans" (pt "RealPlus (2*1) ~1"))
(use "RealLeMonPlusTwo")
(use-with
 "RealLeMonTimesR" (pt "RealPlus 2 0") (pt "x") (pt "RealPlus 1 0") "?" "?")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeIdAbs")
(use "Rx")
(use "CoILimToBd" (pt "xs") (pt "M"))
(use "Rx")
(use "AllCoI")
(use "xsTox")
(use "RealLeRefl")
(realproof)
(use "RealLeRefl")
(autoreal)
(use "RealLeUMinusInv")
(ng)
(simpreal "RealUMinusUMinus")
(use "RealLeTrans" (pt "RealTimes 2 0+IntN 1"))
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealPosToLimPos" (pt "xs") (pt "M"))
(use "Rx")
(use "AllCoI")
(use "xsTox")
(use "1/8<=xsM3")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealPosToAbsBd")

;; We need RealLimToDoubleLimMinusOne for the limit x
;; RealLimToDoubleLimMinusOne
(set-goal "all x,xs,M,p,n(
 Real x ->
 all n CoI(xs n) ->
 all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) ->
 M(PosS p)<=n ->
 abs(2*xs(M 3+n)+IntN 1+ ~(2*x+IntN 1))<<=(1#2**p))")
(assume "x" "xs" "M" "p" "n" "Rx" "AllCoI" "xsTox" "nBd")
(assert "CoI(xs(M 3+n))")
 (use "AllCoI")
(assume "Rxs(M 3+n)")
(simpreal "RealUMinusPlus")
;; ?^6:abs(2*xs(M 3+n)+IntN 1+(~(2*x)+ ~IntN 1))<<=(1#2**p)
(ng #t)
(simpreal (pf "~(2*x)+1===1+ ~(2*x)"))
(simpreal "RealPlusAssoc")
(simpreal (pf "2*xs(M 3+n)+IntN 1+1===2*xs(M 3+n)+(IntN 1+1)"))
(ng #t)
(simpreal "RealPlusZero")
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(simpreal "RealAbsTimes")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 2(1#2**(PosS p))"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "xsTox")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
(use "RatLeToRealLe")
(simprat (pf "(2#2**(PosS p)) == (1+1)*(1#2**(PosS p))"))
(simprat (pf "(1+1)*(1#2**(PosS p)) == 1*(1#2**(PosS p)) + 1*(1#2**(PosS p))"))
(simprat (pf "1*(1#2**(PosS p)) == (1#2**(PosS p))"))
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
(use-with "RatTimesPlusDistrLeft" (pt "1#1") (pt "1#1") (pt "(1#2**(PosS p))"))
(use "Truth")
(autoreal)
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLimToDoubleLimMinusOne")

;; RealCsToDoubleCsMinusOne
(set-goal "all xs,M,p,n,m(
 all n CoI(xs n) ->
 all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
 M(PosS p)<=n ->
 M(PosS p)<=m ->
 abs(2*xs(M 3+n)+IntN 1+ ~(2*xs(M 3+m)+IntN 1))<<=(1#2**p))")
(assume "xs" "M" "p" "n" "m" "AllCoI" "xsCs" "nBd" "mBd")
(assert "CoI(xs(M 3+n))")
 (use "AllCoI")
(assume "Rxs(M 3+n)")
(assert "CoI(xs(M 3+m))")
 (use "AllCoI")
(assume "Rxs(M 3+m)")
(simpreal "RealUMinusPlus")
;; ?^9:abs(2*xs(M 3+n)+IntN 1+(~(2*xs(M 3+m))+ ~IntN 1))<<=(1#2**p)
(ng #t)
(simpreal (pf "~(2*xs(M 3+m))+1===1+ ~(2*xs(M 3+m))"))
(simpreal "RealPlusAssoc")
(simpreal (pf "2*xs(M 3+n)+IntN 1+1===2*xs(M 3+n)+(IntN 1+1)"))
(ng #t)
(simpreal "RealPlusZero")
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(simpreal "RealAbsTimes")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 2 (1#2**(PosS p))"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "xsCs")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
(use "NatLeTrans" (pt "m"))
(use "mBd")
(use "Truth")
(use "RatLeToRealLe")
(simprat (pf "(2#2**(PosS p)) == (1+1)*(1#2**(PosS p))"))
(simprat (pf "(1+1)*(1#2**(PosS p)) == 1*(1#2**(PosS p)) + 1*(1#2**(PosS p))"))
(simprat (pf "1*(1#2**(PosS p)) == (1#2**(PosS p))"))
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
(use-with "RatTimesPlusDistrLeft" (pt "1#1") (pt "1#1") (pt "(1#2**(PosS p))"))
(use "Truth")
(autoreal)
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealCsToDoubleCsMinusOne")

;; RealAbsBdToLimAbsBd
(set-goal "all x,xs,M(
 Real x ->
 all n CoI(xs n) ->
 all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) ->
 abs(xs(M 3))<<=(1#4) ->
 abs x<<=(1#2))")
(assume "x" "xs" "M" "Rx" "AllCoI" "xsTox" "absxsM3<=1/4")
(assert "Real(xs(M 3))")
 (use "CoIToReal")
 (use "AllCoI")
(assume "RxsM3")
(use "RealLeTrans" (pt "abs(xs(M 3))+abs(x+ ~(xs(M 3)))"))
(simpreal (pf "abs x===abs(xs(M 3)+(x+ ~(xs(M 3))))"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealAbsCompat")
(simpreal "RealPlusComm")
(simpreal "<-" "RealPlusAssoc")
(use "RealEqTrans" (pt "RealPlus x 0"))
(use "RealEqSym")
(use "RealPlusZero")
(autoreal)
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusComm")
(use "RealEqSym")
(use "RealPlusMinusZero")
(autoreal)
;; 8
(use "RealLeTrans" (pt "RealPlus(1#4)(1#8)"))
(use "RealLeMonPlusTwo")
(use "absxsM3<=1/4")
(simpreal "<-" "RealAbsUMinus")
(simpreal "RealUMinusPlus")
(simpreal "RealPlusComm")
(simpreal "RealUMinusUMinus")
(use-with "xsTox" (pt "3") (pt "M 3") "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
;;Proof finished.
;; (cdp)
(save "RealAbsBdToLimAbsBd")

;; RealAbsBdToSqAbsBd
(set-goal "all xs,M(
 all n CoI(xs n) ->
 all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
 abs(xs(M 3))<<=(1#4) ->
 all n abs(xs(M 3+n))<<=(1#2))")
(assume "xs" "M" "AllCoI" "xsCs" "absxsM3<=1/4" "n")
(assert "Real(xs(M 3+n))")
 (use "CoIToReal")
 (use "AllCoI")
(assume "R1")
(assert "Real(xs(M 3))")
 (use "CoIToReal")
 (use "AllCoI")
(assume "R2")
(use "RealLeTrans" (pt "abs(xs(M 3)+ ~(xs(M 3))+xs(M 3+n))"))
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
(use "RealLeRefl")
(autoreal)
;; 12
(simpreal  "<-" "RealPlusAssoc")
(use "RealLeTrans" (pt "abs(xs(M 3))+abs(~(xs(M 3))+xs(M 3+n))"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeTrans" (pt "RealPlus(1#4)(1#2**3)"))
(use "RealLeMonPlusTwo")
(use "absxsM3<=1/4")
(simpreal "RealPlusComm")
(use "xsCs")
(use "Truth")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealAbsBdToSqAbsBd")

;; RealLimToDoubleLim
(set-goal "all x,xs,M,p,n(
 Real x -> 
 all n0 CoI(xs n0) -> 
 all p0,n0(M p0<=n0 -> abs(xs n0+ ~x)<<=(1#2**p0)) -> 
 M(PosS p)<=n -> abs(2*xs(M 3+n)+ ~(2*x))<<=(1#2**p))")
(assume "x" "xs" "M" "p" "n" "Rx" "AllCoI" "xsTox" "nBd")
(assert "CoI(xs(M 3+n))")
 (use "AllCoI")
(assume "Rxs(M 3+n)")
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 2(1#2**(PosS p))"))
(use "RealLeMonTimesTwo")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeZeroAbs")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use "xsTox")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
(use "RatLeToRealLe")
(simprat (pf "(2#2**(PosS p)) == (1+1)*(1#2**(PosS p))"))
(simprat (pf "(1+1)*(1#2**(PosS p)) == 1*(1#2**(PosS p)) + 1*(1#2**(PosS p))"))
(simprat (pf "1*(1#2**(PosS p)) == (1#2**(PosS p))"))
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
(use-with "RatTimesPlusDistrLeft" (pt "1#1") (pt "1#1") (pt "(1#2**(PosS p))"))
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLimToDoubleLim")

;; RealCsToDoubleCs
(set-goal "all xs,M,p,n,m(
 all n0 CoI(xs n0) -> 
 all p0,n0,m0(M p0<=n0 -> M p0<=m0 -> abs(xs n0+ ~(xs m0))<<=(1#2**p0)) -> 
 M(PosS p)<=n -> 
 M(PosS p)<=m -> abs(2*xs(M 3+n)+ ~(2*xs(M 3+m)))<<=(1#2**p))")
(assume "xs" "M" "p" "n" "m" "AllCoI" "xsCs" "nBd" "mBd")
(assert "CoI(xs(M 3+n))")
 (use "AllCoI")
(assume "Rxs(M 3+n)")
(assert "CoI(xs(M 3+m))")
 (use "AllCoI")
(assume "Rxs(M 3+m)")
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 2 (1#2**(PosS p))"))
(use "RealLeMonTimesTwo")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeZeroAbs")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use "xsCs")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
(use "NatLeTrans" (pt "m"))
(use "mBd")
(use "Truth")
;; ?^20:RealTimes 2(1#2**PosS p)<<=(1#2**p)
(use "RatLeToRealLe")
(simprat (pf "(2#2**(PosS p)) == (1+1)*(1#2**(PosS p))"))
(simprat (pf "(1+1)*(1#2**(PosS p)) == 1*(1#2**(PosS p)) + 1*(1#2**(PosS p))"))
(simprat (pf "1*(1#2**(PosS p)) == (1#2**(PosS p))"))
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
(use-with "RatTimesPlusDistrLeft" (pt "1#1") (pt "1#1") (pt "(1#2**(PosS p))"))
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealCsToDoubleCs")

;; RealNegToAbsBd con be proved from RealPosToAbsBd by taking negatives.

;; RealNegToAbsBd
(set-goal "all x,xs,M(
     Real x ->
     all n CoI(xs n) ->
     all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) ->
     xs(M 3)<<= ~(1#8) -> abs(2*x+1)<<=1)")
(assume "x" "xs" "M" "Rx" "AllCoI" "xsTox" "xsM3<=~(1#8)")
(assert (pf "abs(2*(~ x)+ ~1)<<=1"))
(use-with "RealPosToAbsBd" (pt "~x") (pt "[n]~(xs n)") (pt "M") "?" "?" "?" "?")
(autoreal)
(assume "n")
(ng)
(use "CoIUMinus")
(simpreal "RealUMinusUMinus")
(use "AllCoI")
(use "CoIToReal")
(use "AllCoI")
;; 7
(assume "p" "n" "nBd")
(ng)
(assert "Real(xs n)")
(use "CoIToReal")
(use "AllCoI")
(assume "Rxsn")
(simpreal "<-" "RealUMinusPlus")
(simpreal "RealAbsUMinus")
(use "xsTox")
(use "nBd")
(autoreal)
;; 8
(ng)
(simpreal "<-" "RealUMinusUMinus")
(use "RealLeUMinus")
(use "xsM3<=~(1#8)")
(autoreal)
;; 3
(assume "LeHyp")
(simpreal "<-" "RealAbsUMinus")
(simpreal "RealUMinusPlus")
(simpreal "<-" "RealTimesIdUMinus")
(use "LeHyp")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealNegToAbsBd")

;; RealNegToLimNeg
(set-goal "all xs,M(
 all n CoI(xs n) ->
 all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
 xs(M 3)<<=(IntN  1#8) -> all n xs(M 3+n)<<=0)")
(assume "xs" "M" "AllCoI" "xsCs" "xsM3<=~1/8" "n")
(assert "Real(xs(M 3))")
(use "CoIToReal")
(use "AllCoI")
(assume "RxsM3")
(assert "Real(xs(M 3+n))")
(use "CoIToReal")
(use "AllCoI")
(assume "RxsM3+n")
(use "RealLeTrans" (pt "xs(M 3+n)+(~(xs(M 3))+(xs(M 3)))"))
(simpreal (pf "~(xs(M 3))+xs(M 3)===xs(M 3)+ ~(xs(M 3))"))
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
(simpreal "RealPlusAssoc")
(use "RealLeTrans" (pt "RealPlus(1#2**3)(IntN 1#8)"))
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "abs(xs(M 3+n)+ ~(xs(M 3)))"))
(use "RealLeIdAbs")
(autoreal)
(use "xsCs")
(use "Truth")
(use "Truth")
(use "xsM3<=~1/8")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealNegToLimNeg")

;; Need an analogue to RealCsToDoubleCsMinusOne
;; RealCsToDoubleCsPlusOne
(set-goal "all xs,M,p,n,m(
 all n CoI(xs n) ->
 all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
 M(PosS p)<=n ->
 M(PosS p)<=m ->
 abs(2*xs(M 3+n)+1+ ~(2*xs(M 3+m)+1))<<=(1#2**p))")
(assume "xs" "M" "p" "n" "m" "AllCoI" "xsCs" "nBd" "mBd")
(assert "CoI(xs(M 3+n))")
 (use "AllCoI")
(assume "Rxs(M 3+n)")
(assert "CoI(xs(M 3+m))")
 (use "AllCoI")
(assume "Rxs(M 3+m)")
(simpreal "RealUMinusPlus")
;; ?^9:abs(2*xs(M 3+n)+1+(~(2*xs(M 3+m))+ ~1))<<=(1#2**p)
(ng #t)
(simpreal (pf "~(2*xs(M 3+m))+IntN 1===IntN 1+ ~(2*xs(M 3+m))"))
(simpreal "RealPlusAssoc")
(simpreal (pf "2*xs(M 3+n)+1+IntN 1===2*xs(M 3+n)+(1+IntN 1)"))
(ng #t)
(simpreal "RealPlusZero")
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(simpreal "RealAbsTimes")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 2 (1#2**(PosS p))"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "xsCs")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
(use "NatLeTrans" (pt "m"))
(use "mBd")
(use "Truth")
(use "RatLeToRealLe")
(simprat (pf "(2#2**(PosS p)) == (1+1)*(1#2**(PosS p))"))
(simprat (pf "(1+1)*(1#2**(PosS p)) == 1*(1#2**(PosS p)) + 1*(1#2**(PosS p))"))
(simprat (pf "1*(1#2**(PosS p)) == (1#2**(PosS p))"))
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
(use-with "RatTimesPlusDistrLeft" (pt "1#1") (pt "1#1") (pt "(1#2**(PosS p))"))
(use "Truth")
(autoreal)
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealCsToDoubleCsPlusOne")

;; RealLimToDoubleLimPlusOne
(set-goal "all x,xs,M,p,n(
 Real x ->
 all n CoI(xs n) ->
 all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) ->
 M(PosS p)<=n ->
 abs(2*xs(M 3+n)+1+ ~(2*x+1))<<=(1#2**p))")
(assume "x" "xs" "M" "p" "n" "Rx" "AllCoI" "xsTox" "nBd")
(assert "CoI(xs(M 3+n))")
 (use "AllCoI")
(assume "Rxs(M 3+n)")
(simpreal "RealUMinusPlus")
;; ?^6:abs(2*xs(M 3+n)+1+(~(2*x)+ ~1))<<=(1#2**p)
(ng #t)
(simpreal (pf "~(2*x)+IntN 1===IntN 1+ ~(2*x)"))
(simpreal "RealPlusAssoc")
(simpreal (pf "2*xs(M 3+n)+1+IntN 1===2*xs(M 3+n)+(1+IntN 1)"))
(ng #t)
(simpreal "RealPlusZero")
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(simpreal "RealAbsTimes")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 2(1#2**(PosS p))"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "xsTox")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
(use "RatLeToRealLe")
(simprat (pf "(2#2**(PosS p)) == (1+1)*(1#2**(PosS p))"))
(simprat (pf "(1+1)*(1#2**(PosS p)) == 1*(1#2**(PosS p)) + 1*(1#2**(PosS p))"))
(simprat (pf "1*(1#2**(PosS p)) == (1#2**(PosS p))"))
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
(use-with "RatTimesPlusDistrLeft" (pt "1#1") (pt "1#1") (pt "(1#2**(PosS p))"))
(use "Truth")
(autoreal)
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealLimToDoubleLimPlusOne")

;; SdLimCaseR
(set-goal "allnc x,xs 
   all M(
    Real x -> 
    all n CoI(xs n) -> 
    all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
    all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) -> 
    (1#8)<<=xs(M 3) -> 
    exr d,x0,y(
     Sd d andi
     Real x0 andi
     abs x0<<=1 andi
     (CoI x0 ord 
      Real x0 andi
      exr xs0 
       exd M0(
        all n CoI(xs0 n) andi
        all p,n,m(M0 p<=n -> M0 p<=m -> abs(xs0 n+ ~(xs0 m))<<=(1#2**p)) andi
        all p,n(M0 p<=n -> abs(xs0 n+ ~x0)<<=(1#2**p)))) andi
     y===(1#2)*(x0+d) andnc x===y))")
(assume "x" "xs" "M" "Rx" "AllCoI" "xsCs" "xsTox" "1/8<=xsM3")
(intro 0 (pt "IntPos 1"))
(intro 0 (pt "2*x+ ~1"))
(intro 0 (pt "x"))
(split)
(intro 0)
(split)
(realproof)
(split)
(use-with "RealPosToAbsBd"
 (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsTox" "1/8<=xsM3")
(split)
(intro 1)
(split)
(realproof)
(intro 0 (pt "[n]2*xs(M 3+n)+ IntN 1"))
(intro 0 (pt "[p]M(PosS p)"))
(split)
(assume "n")
(ng #t)
(use "CoIToCoIDoublePlusOne")
(use "AllCoI")
;; ?^24:0<<=xs(M 3+n)
(use "RealPosToSqPos")
(use "AllCoI")
(use "xsCs")
(use "1/8<=xsM3")
(ng)
(split)
;; 29,30
(assume "p" "n" "m" "nBd" "mBd")
;; ?^31:abs(2*xs(M 3+n)+IntN 1+ ~(2*xs(M 3+m)+IntN 1))<<=(1#2**p)
(use "RealCsToDoubleCsMinusOne")
(use "AllCoI")
(use "xsCs")
(use "nBd")
(use "mBd")
;; 30
(assume "p" "n")
;; ?^36:M(PosS p)<=n -> abs(2*xs(M 3+n)+IntN 1+ ~(2*x+IntN 1))<<=(1#2**p)
(use "RealLimToDoubleLimMinusOne")
(use "Rx")
(use "AllCoI")
(use "xsTox")
;; ?^13:x===(1#2)*(2*x+ ~1+1) andnc x===x
(split)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "SdLimCaseR")

;; (pp (rename-variables (nt (proof-to-extracted-term))))

;; [M,us]
;;  SdR pair
;;  (InR (pos=>nat)yprod(nat=>ai) ai)
;;  (([p]M(PosS p))pair([n]cCoIToCoIDoublePlusOne(us(M 3+n))))

;; (ppc (rename-variables (nt (proof-to-extracted-term))))
;; [M,us]SdR pair InR(([p]M(PosS p))pair([n]cCoIToCoIDoublePlusOne(us(M 3+n))))

(add-sound "SdLimCaseR")

;; ok, SdLimCaseRSound has been added as a new theorem:

;; allnc x,xs,M(
;;  Real x -> 
;;  allnc us^(
;;   allnc n CoIMR(xs n)(us^ n) -> 
;;   all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
;;   all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) -> 
;;   (1#8)<<=xs(M 3) -> 
;;   (ExRTMR int
;;     sd yprod(ai ysum(pos=>nat)yprod(nat=>ai))
;;     (cterm (d,(sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^) 
;;     (ExRTMR rea
;;       sd yprod(ai ysum(pos=>nat)yprod(nat=>ai))
;;       (cterm (x0,(sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^0) 
;;       (ExRTMR rea
;;         sd yprod(ai ysum(pos=>nat)yprod(nat=>ai))
;;         (cterm (y,(sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^1) 
;;         (AndDMR (cterm (s^) SdMR d s^)
;;           (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^2) 
;;           (AndRMR (cterm () Real x0)
;;             (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^3) 
;;             (AndRMR (cterm () abs x0<<=1)
;;               (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^4) 
;;               (AndLMR (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^5) 
;;                         (OrDMR (cterm (u^) CoIMR x0 u^)
;;                           (cterm (Mus^) 
;;                           (AndRMR (cterm () Real x0)
;;                             (cterm (Mus^0) 
;;                             (ExRTMR nat=>rea
;;                               (pos=>nat)yprod(nat=>ai)
;;                               (cterm (xs0,Mus^1) 
;;                               (ExDTMR (cterm (M0,us^0) 
;;                                         (AndLMR (cterm (us^1) 
;;                                                   allnc n 
;;                                                    CoIMR(xs0 n)(us^1 n))
;;                                           (cterm () 
;;                                           all p,n,m(
;;                                            M0 p<=n -> 
;;                                            M0 p<=m -> 
;;                                            abs(xs0 n+ ~(xs0 m))<<=(1#2**p)) andnc 
;;                                           all p,n(
;;                                            M0 p<=n -> 
;;                                            abs(xs0 n+ ~x0)<<=(1#2**p))))
;;                                         us^0))
;;                               Mus^1))
;;                             Mus^0))
;;                           Mus^))
;;                         (ai ysum(pos=>nat)yprod(nat=>ai))^5)
;;                 (cterm () y===(1#2)*(x0+d) andnc x===y))
;;               (ai ysum(pos=>nat)yprod(nat=>ai))^4))
;;             (ai ysum(pos=>nat)yprod(nat=>ai))^3))
;;           (ai ysum(pos=>nat)yprod(nat=>ai))^2))
;;         (sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^1))
;;       (sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^0))
;;     (sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^))
;;   (cSdLimCaseR M us^)))

;; with computation rule

;; cSdLimCaseR eqd
;; ([M,us]
;;   SdR pair
;;   (InR (pos=>nat)yprod(nat=>ai) ai)
;;   (([p]M(PosS p))pair([n]cCoIToCoIDoublePlusOne(us(M 3+n)))))

(deanimate "SdLimCaseR")

;; SdLimCaseM
(set-goal "allnc x,xs 
   all M(
    Real x -> 
    all n CoI(xs n) -> 
    all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
    all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) -> 
    abs(xs(M 3))<<=(1#4) -> 
    exr d,x0,y(
     Sd d andi
     Real x0 andi
     abs x0<<=1 andi
     (CoI x0 ori
      Real x0 andi
      exr xs0 
       exd M0(
        all n CoI(xs0 n) andi
        all p,n,m(M0 p<=n -> M0 p<=m -> abs(xs0 n+ ~(xs0 m))<<=(1#2**p)) andi 
        all p,n(M0 p<=n -> abs(xs0 n+ ~x0)<<=(1#2**p)))) andi
     y===(1#2)*(x0+d) andnc x===y))")
(assume "x" "xs" "M" "Rx" "AllCoI" "xsCs" "xsTox" "absxsM3<=1/4")
(intro 0 (pt "0"))
(intro 0 (pt "2*x"))
(intro 0 (pt "x"))
(split)
(intro 1)
(split)
(realproof)
(split)
(simpreal "RealAbsTimes")
(use "RealLeTrans"(pt "RealAbs 2*RealPlus(1#2)0"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealAbsBdToLimAbsBd" (pt "xs") (pt "M"))
(use "Rx")
(use "AllCoI")
(use "xsTox")
(use "absxsM3<=1/4")
;; 16
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; 11
(split)
(intro 1)
(split)
(autoreal)
(intro 0 (pt "[n]2*xs(M 3+n)"))
(intro 0 (pt "[p]M(PosS p)"))
(split)
(ng)
(assume "n")
(use "CoIToCoIDouble")
(use "AllCoI")
(use "RealAbsBdToSqAbsBd")
(use "AllCoI")
(use "xsCs")
(use "absxsM3<=1/4")
;; 33
(split)
;; 41,42
(ng)
(assume "p" "n" "m")
(use "RealCsToDoubleCs")
(use "AllCoI")
(use "xsCs")
;; 42
(ng)
(assume "p" "n")
;; ?^48:M(PosS p)<=n -> abs(2*xs(M 3+n)+ ~(2*x))<<=(1#2**p)
(use "RealLimToDoubleLim")
(use "Rx")
(use "AllCoI")
(use "xsTox")
;; ?^26:x===(1#2)*(2*x+0) andnc x===x
(split)
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(ng)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "SdLimCaseM")

;; (pp (rename-variables (nt (proof-to-extracted-term))))

;; [M,us]
;;  SdM pair
;;  (InR (pos=>nat)yprod(nat=>ai) ai)
;;  (([p]M(PosS p))pair([n]cCoIToCoIDouble(us(M 3+n))))

;; (ppc (rename-variables (nt (proof-to-extracted-term))))
;; [M,us]SdM pair InR(([p]M(PosS p))pair([n]cCoIToCoIDouble(us(M 3+n))))

(add-sound "SdLimCaseM")

;; ok, SdLimCaseMSound has been added as a new theorem:

;; allnc x,xs,M(
;;  Real x -> 
;;  allnc us^(
;;   allnc n CoIMR(xs n)(us^ n) -> 
;;   all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
;;   all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) -> 
;;   abs(xs(M 3))<<=(1#4) -> 
;;   (ExRTMR int
;;     sd yprod(ai ysum(pos=>nat)yprod(nat=>ai))
;;     (cterm (d,(sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^) 
;;     (ExRTMR rea
;;       sd yprod(ai ysum(pos=>nat)yprod(nat=>ai))
;;       (cterm (x0,(sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^0) 
;;       (ExRTMR rea
;;         sd yprod(ai ysum(pos=>nat)yprod(nat=>ai))
;;         (cterm (y,(sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^1) 
;;         (AndDMR (cterm (s^) SdMR d s^)
;;           (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^2) 
;;           (AndRMR (cterm () Real x0)
;;             (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^3) 
;;             (AndRMR (cterm () abs x0<<=1)
;;               (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^4) 
;;               (AndLMR (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^5) 
;;                         (OrDMR (cterm (u^) CoIMR x0 u^)
;;                           (cterm (Mus^) 
;;                           (AndRMR (cterm () Real x0)
;;                             (cterm (Mus^0) 
;;                             (ExRTMR nat=>rea
;;                               (pos=>nat)yprod(nat=>ai)
;;                               (cterm (xs0,Mus^1) 
;;                               (ExDTMR (cterm (M0,us^0) 
;;                                         (AndLMR (cterm (us^1) 
;;                                                   allnc n 
;;                                                    CoIMR(xs0 n)(us^1 n))
;;                                           (cterm () 
;;                                           all p,n,m(
;;                                            M0 p<=n -> 
;;                                            M0 p<=m -> 
;;                                            abs(xs0 n+ ~(xs0 m))<<=(1#2**p)) andnc 
;;                                           all p,n(
;;                                            M0 p<=n -> 
;;                                            abs(xs0 n+ ~x0)<<=(1#2**p))))
;;                                         us^0))
;;                               Mus^1))
;;                             Mus^0))
;;                           Mus^))
;;                         (ai ysum(pos=>nat)yprod(nat=>ai))^5)
;;                 (cterm () y===(1#2)*(x0+d) andnc x===y))
;;               (ai ysum(pos=>nat)yprod(nat=>ai))^4))
;;             (ai ysum(pos=>nat)yprod(nat=>ai))^3))
;;           (ai ysum(pos=>nat)yprod(nat=>ai))^2))
;;         (sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^1))
;;       (sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^0))
;;     (sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^))
;;   (cSdLimCaseM M us^)))

;; with computation rule

;; cSdLimCaseM eqd
;; ([M,us]
;;   SdM pair
;;   (InR (pos=>nat)yprod(nat=>ai) ai)
;;   (([p]M(PosS p))pair([n]cCoIToCoIDouble(us(M 3+n)))))

(deanimate "SdLimCaseM")

;; SdLimCaseL
(set-goal "allnc x,xs 
 all M(
  Real x -> 
  all n CoI(xs n) -> 
  all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
  all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) -> 
  xs(M 3)<<= ~(1#8) -> 
     exr d,x0,y(
      Sd d andi
      Real x0 andi
      abs x0<<=1 andi
      (CoI x0 ori
       Real x0 andi
       exr xs0 
        exd M0(
         all n CoI(xs0 n) andi
         all p,n,m(M0 p<=n -> M0 p<=m -> abs(xs0 n+ ~(xs0 m))<<=(1#2**p)) andi
         all p,n(M0 p<=n -> abs(xs0 n+ ~x0)<<=(1#2**p)))) andi
      y===(1#2)*(x0+d) andnc x===y))")
(assume "x" "xs" "M" "Rx" "AllCoI" "xsCs" "xsTox" "xsM3<=~1/8")
(intro 0 (pt "IntN 1"))
(intro 0 (pt "2*x+1"))
(intro 0 (pt "x"))
(split)
(intro 2)
(split)
(realproof)
(split)
(use "RealNegToAbsBd" (pt "xs") (pt "M"))
(use "Rx")
(use "AllCoI")
(use "xsTox")
(use "xsM3<=~1/8")
(split)
(intro 1)
(split)
(realproof)
(intro 0 (pt "[n]2*xs(M 3+n)+1"))
(intro 0 (pt "[p]M(PosS p)"))
(ng)
(split)
(assume "n")
(use "CoIToCoIDoubleMinusOne")
(use "AllCoI")
(use "RealNegToLimNeg")
(use "AllCoI")
(use "xsCs")
(use "xsM3<=~1/8")
;; 25
(split)
;; 32,33
(assume "p" "n" "m" "nBd" "mBd")
(use "RealCsToDoubleCsPlusOne")
(use "AllCoI")
(use "xsCs")
(use "nBd")
(use "mBd")
;; 33
(assume "p" "n" "nBd")
(use "RealLimToDoubleLimPlusOne")
(use "Rx")
(use "AllCoI")
(use "xsTox")
(use "nBd")
;; 17
(split)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finshed.
;; (cdp)
(save "SdLimCaseL")

;; (pp (rename-variables (nt (proof-to-extracted-term))))

;; [M,us]
;;  SdL pair
;;  (InR (pos=>nat)yprod(nat=>ai) ai)
;;  (([p]M(PosS p))pair([n]cCoIToCoIDoubleMinusOne(us(M 3+n))))

;; (ppc (rename-variables (nt (proof-to-extracted-term))))
;; [M,us]SdL pair InR(([p]M(PosS p))pair([n]cCoIToCoIDoubleMinusOne(us(M 3+n))))

(add-sound "SdLimCaseL")

;; ok, SdLimCaseLSound has been added as a new theorem:

;; allnc x,xs,M(
;;  Real x -> 
;;  allnc us^(
;;   allnc n CoIMR(xs n)(us^ n) -> 
;;   all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
;;   all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) -> 
;;   xs(M 3)<<= ~(1#8) -> 
;;   (ExRTMR int
;;     sd yprod(ai ysum(pos=>nat)yprod(nat=>ai))
;;     (cterm (d,(sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^) 
;;     (ExRTMR rea
;;       sd yprod(ai ysum(pos=>nat)yprod(nat=>ai))
;;       (cterm (x0,(sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^0) 
;;       (ExRTMR rea
;;         sd yprod(ai ysum(pos=>nat)yprod(nat=>ai))
;;         (cterm (y,(sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^1) 
;;         (AndDMR (cterm (s^) SdMR d s^)
;;           (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^2) 
;;           (AndRMR (cterm () Real x0)
;;             (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^3) 
;;             (AndRMR (cterm () abs x0<<=1)
;;               (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^4) 
;;               (AndLMR (cterm ((ai ysum(pos=>nat)yprod(nat=>ai))^5) 
;;                         (OrDMR (cterm (u^) CoIMR x0 u^)
;;                           (cterm (Mus^) 
;;                           (AndRMR (cterm () Real x0)
;;                             (cterm (Mus^0) 
;;                             (ExRTMR nat=>rea
;;                               (pos=>nat)yprod(nat=>ai)
;;                               (cterm (xs0,Mus^1) 
;;                               (ExDTMR (cterm (M0,us^0) 
;;                                         (AndLMR (cterm (us^1) 
;;                                                   allnc n 
;;                                                    CoIMR(xs0 n)(us^1 n))
;;                                           (cterm () 
;;                                           all p,n,m(
;;                                            M0 p<=n -> 
;;                                            M0 p<=m -> 
;;                                            abs(xs0 n+ ~(xs0 m))<<=(1#2**p)) andnc 
;;                                           all p,n(
;;                                            M0 p<=n -> 
;;                                            abs(xs0 n+ ~x0)<<=(1#2**p))))
;;                                         us^0))
;;                               Mus^1))
;;                             Mus^0))
;;                           Mus^))
;;                         (ai ysum(pos=>nat)yprod(nat=>ai))^5)
;;                 (cterm () y===(1#2)*(x0+d) andnc x===y))
;;               (ai ysum(pos=>nat)yprod(nat=>ai))^4))
;;             (ai ysum(pos=>nat)yprod(nat=>ai))^3))
;;           (ai ysum(pos=>nat)yprod(nat=>ai))^2))
;;         (sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^1))
;;       (sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^0))
;;     (sd yprod(ai ysum(pos=>nat)yprod(nat=>ai)))^))
;;   (cSdLimCaseL M us^)))

;; with computation rule

;; cSdLimCaseL eqd
;; ([M,us]
;;   SdL pair
;;   (InR (pos=>nat)yprod(nat=>ai) ai)
;;   (([p]M(PosS p))pair([n]cCoIToCoIDoubleMinusOne(us(M 3+n)))))

(deanimate "SdLimCaseL")

;; Let xs be a Cauchy sequence of reals with modulus M, and x its
;; limit.  (Recall that (xs n)_n converges to x with the same
;; modulus).  Then if all xs(n) are in CoI, then also x is in CoI

;; (set! COMMENT-FLAG #f)
;; SdLim
(set-goal "allnc x(
     Real x andr 
     exr xs 
      exd M(
       all n CoI(xs n) andi
       all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) andi
       all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p))) -> 
     CoI x)")
(assume "x0" "Conj")
(coind "Conj")
(drop "Conj")
(assume "x" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume "Rx" "ExHyp")
(by-assume "ExHyp" "xs" "xsProp")
(by-assume "xsProp" "M" "xsMProp")
(elim "xsMProp")
(drop "xsMProp")
(assume "AllCoI" "Conj2")
(elim "Conj2")
(drop "Conj2")
(assume "xsCs" "xsTox")
(inst-with-to "AllCoI" (pt "M 3") "CoIxsM3")
(drop "AllCoI")
(inst-with-to "CoITripleClosure" (pt "xs(M 3)") "CoIxsM3" "CoIxsM3Inst")
(drop "CoIxsM3")
(by-assume "CoIxsM3Inst" "d2" "CoIxsM3Inst1")
(by-assume "CoIxsM3Inst1" "d1" "CoIxsM3Inst2")
(by-assume "CoIxsM3Inst2" "d0" "CoIxsM3Inst3")
(by-assume "CoIxsM3Inst3" "y" "CoIxsM3Inst4")
(elim "CoIxsM3Inst4")
(drop "CoIxsM3Inst4")
(assume "Sdd2" "Conj3")
(elim "Conj3")
(drop "Conj3")
(assume "Sdd1" "Conj4")
(elim "Conj4")
(drop "Conj4")
(assume "Sdd0" "Conj5")
(elim "Conj5")
(drop "Conj5")
(assume "yBd" "Conj6")
(elim "Conj6")
(drop "Conj6")
(assume "CoIy")
(elim "Sdd0")
;; 54-56
;; ?_54:xs(M 3)===(1#8)*(y+d2+2*d1+4*0) -> 
;;      exr d,x0,y0(
;;       Sd d andd 
;;       Real x0 andr 
;;       abs x0<<=1 andr 
;;       (CoI x0 ord 
;;        Real x0 andr 
;;        exr xs0 
;;         exd M0(
;;          all n CoI(xs0 n) andl 
;;          all p,n,m(M0 p<=n -> M0 p<=m -> abs(xs0 n+ ~(xs0 m))<<=(1#2**p)) andl 
;;          all p,n(M0 p<=n -> abs(xs0 n+ ~x0)<<=(1#2**p)))) andl 
;;       y0===(1#2)*(x0+d) andnc x===y0)

;; Case f(M 3)=1...
(drop "Sdd0")
(elim "Sdd1")
;; 58-60
(drop "Sdd1")
;; Case xs(M 3)=11...
(assume "xsM3Eq")
(assert "(1#8)<<=xs(M 3)")
 (simpreal "xsM3Eq")
 (ng #t)
 (use "RealLeTrans" (pt "(1#8)*((RealPlus 0 ~1)+(RealPlus 0 ~1)+2+4)"))
 (ng #t)
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlusTwo")
 (use "RealLeMonPlusTwo")
 (use "RealLeMonPlusTwo")
 (use "CoIToLowBd")
 (use "CoIy")
 (use "SdToLowBd")
 (use "Sdd2")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
;; Assertion proved.
(use-with
 "SdLimCaseR" (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 59
 (drop "Sdd1")
;; Case xs(M3)=10...
(assume "xsM3Eq")
(assert "(1#8)<<=xs(M 3)")
 (simpreal "xsM3Eq")
 (ng #t)
 (use "RealLeTrans" (pt "(1#8)*((RealPlus 0 ~1)+(RealPlus 0 ~1)+0+4)"))
 (ng #t)
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlusTwo")
 (use "RealLeMonPlusTwo")
 (use "RealLeMonPlusTwo")
 (use "CoIToLowBd")
 (use "CoIy")
 (use "SdToLowBd")
 (use "Sdd2")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
;; Assertion proved.
(use-with
 "SdLimCaseR" (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 60
(drop "Sdd1")
;; Case xs(M3)=1-1...
(elim "Sdd2")
;; 108-110
;; Case xs(M3)=1-11...
(drop "Sdd2")
(assume "xsM3Eq")
(assert "(1#8)<<=xs(M 3)")
 (simpreal "xsM3Eq")
 (ng #t)
 (use "RealLeTrans" (pt "(1#8)*((RealPlus 0 ~1)+1+(IntN 2)+4)"))
 (ng #t)
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlusTwo")
 (use "RealLeMonPlusTwo")
 (use "RealLeMonPlusTwo")
 (use "CoIToLowBd")
 (use "CoIy")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
;; Assertion proved.
(use-with
 "SdLimCaseR" (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 109
(drop "Sdd2")
;; Case xs(M3)=1-10...
(assume "xsM3Eq")
(assert "(1#8)<<=xs(M 3)")
 (simpreal "xsM3Eq")
 (ng)
 (use "RealLeTrans" (pt "(1#8)*((RealPlus 0 ~1)+0+(IntN 2)+4)"))
 (ng)
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlusTwo")
 (use "RealLeMonPlusTwo")
 (use "RealLeMonPlusTwo")
 (use "CoIToLowBd")
 (use "CoIy")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
;; Assertion proved.
(use-with
 "SdLimCaseR" (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 110
(drop "Sdd2")
;; Case xs(M3)=1-1-1...
(assume "xsM3Eq")
(assert "abs(xs(M 3))<<=(1#4)")
 (simpreal "xsM3Eq")
 (ng)
 (use "RealLeAbs")
;; 163,164
 (use "RealLeTrans" (pt "RealTimes(1#8)2"))
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (simpreal "<-" "RealPlusAssoc")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt "RealPlus 1 1"))
 (use "RealLeMonPlus")
 (autoreal)
 (use "CoIToUpBd")
 (use "CoIy")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
 (use "RatLeToRealLe")
 (use "Truth")
;; 164
 (use "RealLeUMinusInv")
 (simpreal "RealUMinusUMinus")
 (use "RealLeTrans" (pt "RealTimes(1#8) ~2"))
 (use "RealLeRefl")
 (realproof)
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (simpreal "<-" "RealPlusAssoc")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt "RealPlus ~1 ~1"))
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlusTwo")
 (use "CoIToLowBd")
 (use "CoIy")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
;; Assertion proved.
(use-with
 "SdLimCaseM" (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 55
(drop "Sdd0")
;; Case xs(M3)=0...
(elim "Sdd1")
;; 212-214
(drop "Sdd1")
;; Case xs(M3)=01...
(elim "Sdd2")
;; 216-218
(drop "Sdd2")
;; Case xs(M3)=011...
(assume "xsM3Eq")
(assert "(1#8)<<=xs(M 3)")
 (simpreal "xsM3Eq")
 (ng #t)
 (simpreal "RealPlusZero")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt "RealTimes(1#8)2"))
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeTrans" (pt "RealPlus ~1 3"))
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlus")
 (autoreal)
 (use "CoIToLowBd")
 (use "CoIy")
 (autoreal)
;; Assertion proved.
(use-with
 "SdLimCaseR" (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 217
(drop "Sdd2")
;; Case xs(M3)=010...
(assume "xsM3Eq")
(assert "(1#8)<<=xs(M 3)")
 (simpreal "xsM3Eq")
 (ng #t)
 (simpreal "RealPlusZero")
 (simpreal "RealPlusZero")
 (use "RealLeTrans" (pt "(1#8)*RealPlus(IntN 1)2"))
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlus")
 (autoreal)
 (use "CoIToLowBd")
 (use "CoIy")
 (autoreal)
;; Assertion proved.
(use-with
 "SdLimCaseR" (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 218
(drop "Sdd2")
;; Case xs(M3)=01-1...
(assume "xsM3Eq")
(assert "abs(xs(M 3))<<=(1#4)")
 (simpreal "xsM3Eq")
 (use "RealLeAbs")
;; 268,269
 (ng #t)
 (simpreal "RealPlusZero")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt"(1#8)*RealPlus 1 1"))
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlus")
 (autoreal)
 (use "CoIToUpBd")
 (use "CoIy")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
;; 269
 (use "RealLeUMinusInv")
 (simpreal "RealUMinusUMinus")
 (use "RealLeTrans" (pt "RealTimes(1#8) ~2"))
 (use "RealLeRefl")
 (realproof)
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (simpreal "<-" "RealPlusAssoc")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt "RealPlus ~1 ~1"))
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlusTwo")
 (use "CoIToLowBd")
 (use "CoIy")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
;; Assertion proved.
(use-with
 "SdLimCaseM"  (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 213
(drop "Sdd1")
;; Case xs(M3)=00...
(assume "xsM3Eq")
(assert "abs(xs(M 3))<<=(1#4)")
 (simpreal "xsM3Eq")
 (use "RealLeAbs")
 (use "RealLeTrans" (pt "RealTimes(1#8)2"))
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (simpreal "<-" "RealPlusAssoc")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt "RealPlus 1 1"))
 (use "RealLeMonPlusTwo")
 (use "CoIToUpBd")
 (use "CoIy")
 (use "SdToUpBd")
 (use "Sdd2")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeUMinusInv")
 (simpreal "RealUMinusUMinus")
 (use "RealLeTrans" (pt "RealTimes(1#8) ~2"))
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (simpreal "<-" "RealPlusAssoc")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt "RealPlus ~1 ~1"))
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlusTwo")
 (use "CoIToLowBd")
 (use "CoIy")
 (use "SdToLowBd")
 (use "Sdd2")
 (autoreal)
;; Assertion proved.
(use-with
 "SdLimCaseM"  (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 214
(drop "Sdd1")
;; Case xs(M3)=0-1...
(elim "Sdd2")
;; 367-369
(drop "Sdd2")
;; Case xs(M3)=0-11...
(assume "xsM3Eq")
(assert "abs(xs(M 3))<<=(1#4)")
 (simpreal "xsM3Eq")
 (use "RealLeAbs")
 (use "RealLeTrans" (pt "RealTimes(1#8)2"))
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (simpreal "<-" "RealPlusAssoc")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt "RealPlus 1 ~1"))
 (use "RealLeMonPlusTwo")
 (use "CoIToUpBd")
 (use "CoIy")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeUMinusInv")
 (simpreal "RealUMinusUMinus")
 (use "RealLeTrans" (pt "RealTimes (1#8) ~2"))
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (simpreal "<-" "RealPlusAssoc")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt "RealPlus ~1 ~1"))
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonPlusTwo")
 (use "CoIToLowBd")
 (use "CoIy")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
;; Assertion proved.
(use-with
 "SdLimCaseM"  (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 368
(drop "Sdd2")
;; Case xs(M3)=0-10...
(assume "xsM3Eq")
(assert "xs(M 3)<<= ~(1#8)")
 (simpreal "xsM3Eq")
 (use "RealLeTrans" (pt "RealTimes(1#8)(~1)"))
 (use "RealLeMonTimesR")
 (use "RatLeToRealLe")
 (use "Truth")
 (simpreal "<-" "RealPlusAssoc")
 (simpreal "<-" "RealPlusAssoc")
 (ng #t)
 (use "RealLeTrans" (pt "RealPlus 1 ~2"))
 (use "RealLeMonPlusTwo")
 (use "CoIToUpBd")
 (use "CoIy")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
 (use "RatLeToRealLe")
 (use "Truth")
;; Assertion proved.
;; ?_426:xs(M 3)<<= ~(1#8) -> 
;;       exr d,x0,y(
;;        Sd d andd 
;;        Real x0 andr 
;;        abs x0<<=1 andr 
;;        (CoI x0 ord 
;;         Real x0 andr 
;;         exr xs0 
;;          exd M0(
;;           all n CoI(xs0 n) andl 
;;           all p,n,m(M0 p<=n -> M0 p<=m -> abs(xs0 n+ ~(xs0 m))<<=(1#2**p)) andl 
;;           all p,n(M0 p<=n -> abs(xs0 n+ ~x0)<<=(1#2**p)))) andl 
;;        y===(1#2)*(x0+d) andnc x===y)

(use "SdLimCaseL")
(use "Rx")
(use "AllCoI") ;should not have beed droped
(use "xsCs")
(use "xsTox")
;; 369
(drop "Sdd2")
;; Case xs(M3)=0-1-1...
(assume "xsM3Eq")
(assert "xs(M 3)<<= ~(1#8)")
(simpreal "xsM3Eq")
(use "RealLeTrans" (pt "RealTimes(1#8)(~1)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealLeTrans" (pt "RealPlus 1 ~2"))
(use "RealLeMonPlusTwo")
(use "CoIToUpBd")
(use "CoIy")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use-with "SdLimCaseL"
	  (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 56
;; Case xs(M 3)=-1...
(drop "Sdd0")
(elim "Sdd1")
;; 483-485
(drop "Sdd1")
;; Case xs(M 3)=-11...
(elim "Sdd2")
;; 487-489
;; Case xs(M 3)=-111...
(drop "Sdd2")
(assume "xsM3Eq")
(assert "abs(xs(M 3))<<=(1#4)")
(simpreal "xsM3Eq")
(use "RealLeAbs")
;; 495-496
(use "RealLeTrans" (pt "RealTimes(1#8)2"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealLeTrans" (pt "RealPlus 1 1"))
(use "RealLeMonPlusTwo")
(use "CoIToUpBd")
(use "CoIy")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeUMinusInv")
(simpreal "RealUMinusUMinus")
(use "RealLeTrans" (pt "RealTimes(1#8) ~2"))
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealLeTrans" (pt "RealPlus ~1 ~1"))
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlusTwo")
(use "CoIToLowBd")
(use "CoIy")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use-with "SdLimCaseM"
	  (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 488
;; Case xs(M 3)=-110
(drop "Sdd2")
(assume "xsM3Eq")
(assert "xs(M 3)<<= ~(1#8)")
(simpreal "xsM3Eq")
(use "RealLeTrans" (pt "RealTimes(1#8)(~1)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealLeTrans" (pt "RealPlus 1 ~2"))
(use "RealLeMonPlusTwo")
(use "CoIToUpBd")
(use "CoIy")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use-with "SdLimCaseL" (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs""xsTox")
;; Case xs(M 3)=-11-1
(drop "Sdd2")
(assume "xsM3Eq")
(assert "xs(M 3)<<= ~(1#8)")
(simpreal "xsM3Eq")
(use "RealLeTrans" (pt "RealTimes(1#8)(~1)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealLeTrans" (pt "RealPlus 1 ~2"))
(use "RealLeMonPlusTwo")
(use "CoIToUpBd")
(use "CoIy")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use-with "SdLimCaseL"
	  (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 484
;; Case xs(M 3)=-10...
(drop "Sdd1" "Sdd2")
(assume "xsM3Eq")
(assert "xs(M 3)<<= ~(1#8)")
(simpreal "xsM3Eq")
(use "RealLeTrans" (pt "RealTimes(1#8) (~1)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealLeTrans" (pt "RealPlus 2 ~4"))
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "RealPlus 1 1"))
(use "RealLeMonPlusTwo")
(use "CoIToUpBd")
(use "CoIy")
(use "SdToUpBd")
(use "Sdd2")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use-with "SdLimCaseL"
	  (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; 485
;; Case xs(M 3)=-1-1...
(drop "Sdd1" "Sdd2")
(assume "xsM3Eq")
(assert "xs(M 3)<<= ~(1#8)")
(simpreal "xsM3Eq")
(use "RealLeTrans" (pt "RealTimes(1#8)(~1)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "<-" "RealPlusAssoc")
(ng $t)
(use "RealLeTrans" (pt "RealPlus 2 ~6"))
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "RealPlus 1 1"))
(use "RealLeMonPlusTwo")
(use "CoIToUpBd")
(use "CoIy")
(use "SdToUpBd")
(use "Sdd2")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use-with "SdLimCaseL"
	  (pt "x") (pt "xs") (pt "M") "Rx" "AllCoI" "xsCs" "xsTox")
;; Proof finished.
;; (cdp)
(save "SdLim")

;; (set! COMMENT-FLAG #t)
(define CoILim-eterm (nt (proof-to-extracted-term)))

(ppc (rename-variables (nt (proof-to-extracted-term))))

;; [Mus]
;;  (CoRec (pos=>nat)yprod(nat=>ai)=>ai)Mus
;;  ([Mus0]
;;    [case Mus0
;;      (M pair us -> 
;;      [case (cCoITripleClosure(us(M 3)))
;;        (s pair(sd yprod sd yprod ai) -> 
;;        [case (sd yprod sd yprod ai)
;;          (s0 pair su -> 
;;          [case su
;;            (s1 pair u -> 
;;            [case s1
;;              (SdR -> 
;;              [case s0
;;                (SdR -> cSdLimCaseR M us)
;;                (SdM -> cSdLimCaseR M us)
;;                (SdL -> 
;;                [case s
;;                  (SdR -> cSdLimCaseR M us)
;;                  (SdM -> cSdLimCaseR M us)
;;                  (SdL -> cSdLimCaseM M us)])])
;;              (SdM -> 
;;              [case s0
;;                (SdR -> 
;;                [case s
;;                  (SdR -> cSdLimCaseR M us)
;;                  (SdM -> cSdLimCaseR M us)
;;                  (SdL -> cSdLimCaseM M us)])
;;                (SdM -> cSdLimCaseM M us)
;;                (SdL -> 
;;                [case s
;;                  (SdR -> cSdLimCaseM M us)
;;                  (SdM -> cSdLimCaseL M us)
;;                  (SdL -> cSdLimCaseL M us)])])
;;              (SdL -> 
;;              [case s0
;;                (SdR -> 
;;                [case s
;;                  (SdR -> cSdLimCaseM M us)
;;                  (SdM -> cSdLimCaseL M us)
;;                  (SdL -> cSdLimCaseL M us)])
;;                (SdM -> cSdLimCaseL M us)
;;                (SdL -> cSdLimCaseL M us)])])])])])])

(add-sound "SdLim")

;; ok, SdLimSound has been added as a new theorem:

;; allnc x,Mus^(
;;  (AndRMR (cterm () Real x)
;;    (cterm (Mus^0) 
;;    (ExRTMR nat=>rea
;;      (pos=>nat)yprod(nat=>ai)
;;      (cterm (xs,Mus^1) 
;;      (ExDTMR (cterm (M,us^) 
;;                (AndLMR (cterm (us^0) allnc n CoIMR(xs n)(us^0 n))
;;                  (cterm () 
;;                  all p,n,m(
;;                   M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) andnc 
;;                  all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p))))
;;                us^))
;;      Mus^1))
;;    Mus^0))
;;  Mus^ -> 
;;  CoIMR x(cSdLim Mus^))

;; with computation rule

;; cSdLim eqd
;; ([Mus]
;;   (CoRec (pos=>nat)yprod(nat=>ai)=>ai)Mus
;;   ([Mus0]
;;     [if Mus0
;;       ([M,us]
;;        [if (cCoITripleClosure(us(M 3)))
;;          ([s,(sd yprod sd yprod ai)]
;;           [if (sd yprod sd yprod ai)
;;             ([s0,su]
;;              [if su
;;                ([s1,u]
;;                 [if s1
;;                   [if s0
;;                    (cSdLimCaseR M us)
;;                    (cSdLimCaseR M us)
;;                    [if s
;;                     (cSdLimCaseR M us)
;;                     (cSdLimCaseR M us)
;;                     (cSdLimCaseM M us)]]
;;                   [if s0
;;                    [if s
;;                     (cSdLimCaseR M us)
;;                     (cSdLimCaseR M us)
;;                     (cSdLimCaseM M us)]
;;                    (cSdLimCaseM M us)
;;                    [if s
;;                     (cSdLimCaseM M us)
;;                     (cSdLimCaseL M us)
;;                     (cSdLimCaseL M us)]]
;;                   [if s0
;;                    [if s
;;                     (cSdLimCaseM M us)
;;                     (cSdLimCaseL M us)
;;                     (cSdLimCaseL M us)]
;;                    (cSdLimCaseL M us)
;;                    (cSdLimCaseL M us)]])])])])]))

(deanimate "SdLim")

'(
(animate "SdLimCaseL")
(animate "SdLimCaseM")
(animate "SdLimCaseR")
(animate "CoIToCoIDoubleMinusOne")
(animate "CoIToCoIDoublePlusOne")
(animate "CoITripleClosure")
(animate "CoIDoubleClosure")
(animate "RealToCoI")
(animate "RealToCoIAux")
(animate "ApproxSplitZeroMinusPtFive")
(animate "ApproxSplitZeroPtFive")
(animate "ApproxSplit")
(animate "CoIToCoIDouble")
(animate "CoIToCoIQuad")
(animate "CoIDivSatCoIClAuxL")
(animate "CoIDivSatCoIClAuxR")
(animate "CoIPosToCoIMinusOne")
(animate "CoIUMinus")
(animate "Rht")
(animate "SdUMinus")
(animate "Lft")
(animate "CoINegToCoIPlusOne")
(animate "CoIOne")
(animate "CoIClosure")
(animate "CoIIntNOne")
(animate "CoICompat")
(animate "CoIClosureInv")
(animate "CoIAverage")
(animate "CoIAvcToCoI")
(animate "CoIAvToAvc")
(animate "IntPlusSdToSdtwo")
(animate "CoIClauseInv")
(animate "CoIAvcSatCoICl")
(animate "CoIAvcSatCoIClAuxK")
(animate "CoIAvcSatCoIClAuxJ")

(add-program-constant "SdRs" (py "ai"))
(add-computation-rules "SdRs" "C SdR SdRs")

(add-program-constant "SdMsSdRLsSeq" (py "nat=>ai"))
(add-computation-rules
 "SdMsSdRLsSeq Zero" "SdRs"
 "SdMsSdRLsSeq (Succ n)" "C SdM (cCoIUMinus (SdMsSdRLsSeq n))")

(terms-to-haskell-program
 "sdlimtest.hs"
 (list (list CoILim-eterm "coilim")
       (list RealToCoI-eterm "realtocoi")
       (list RatToCoI-eterm "rattocoi")
       (list (pt "SdRs") "sdrs")
       (list (pt "SdMsSdRLsSeq") "sdmssdrlsseq")
       (list (pt "PosToNat") "postonat")
       (list (pt "[n] SdMs") "zerosequence")
       (list (pt "[p] Zero") "zeromodul")))
;; ok, output written to file ~/temp/sdlimtest.hs

(deanimate "SdLimCaseL")
(deanimate "SdLimCaseM")
(deanimate "SdLimCaseR")
(deanimate "CoIToCoIDoubleMinusOne")
(deanimate "CoIToCoIDoublePlusOne")
(deanimate "CoITripleClosure")
(deanimate "CoIDoubleClosure")
(deanimate "RealToCoI")
(deanimate "RealToCoIAux")
(deanimate "ApproxSplitZeroMinusPtFive")
(deanimate "ApproxSplitZeroPtFive")
(deanimate "ApproxSplit")
(deanimate "CoIToCoIDouble")
(deanimate "CoIToCoIQuad")
(deanimate "CoIDivSatCoIClAuxL")
(deanimate "CoIDivSatCoIClAuxR")
(deanimate "CoIPosToCoIMinusOne")
(deanimate "CoIUMinus")
(deanimate "Rht")
(deanimate "SdUMinus")
(deanimate "Lft")
(deanimate "CoINegToCoIPlusOne")
(deanimate "CoIOne")
(deanimate "CoIClosure")
(deanimate "CoIIntNOne")
(deanimate "CoICompat")
(deanimate "CoIClosureInv")
(deanimate "CoIAverage")
(deanimate "CoIAvcToCoI")
(deanimate "CoIAvToAvc")
(deanimate "IntPlusSdToSdtwo")
(deanimate "CoIClauseInv")
(deanimate "CoIAvcSatCoICl")
(deanimate "CoIAvcSatCoIClAuxK")
(deanimate "CoIAvcSatCoIClAuxJ")
)
