;; 2022-09-17.  sdind.scm.  Essentially written by Nils Koepp

;; sd-code exact real arithmetic with inductive prediacte and lookahead

(load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")
(load "~/git/minlog/examples/analysis/digits.scm")
(set! COMMENT-FLAG #t)

;; End of changes in ets.scm

;; Inductive predicate L
;; =====================

(add-algs "al"
	  '("U" "al")
	  '("C" "sd=>al=>al"))
(add-var-name "u" "v" "w" (py "al"))

(add-eqpnc "al")
(add-totality "al")
(add-totalnc "al")
(add-mr-ids "TotalAl")

(remove-var-name "L")
(remove-token "L")

(add-ids
 (list (list "L" (make-arity (py "rea") (py "nat")) "al"))
 '("allnc x (Real x -> abs x<<=1 -> L x Zero)" "InitL")
 '("allnc d,x,y,n(Sd d -> L x n -> y===(1#2)*(x+d) -> L y(n+1))" "GenL"))

(add-mr-ids "L")

;; LToReal
(set-goal "all x,n(L x n -> Real x)")
(assume "x" "n" "Lx")
(elim "Lx")
(assume "y" "Ry" "yBd")
(use "Ry")
(assume "d" "y" "y0" "n0" "Sdd" "Ly" "Ry" "y0Def")
(use "RealEqToReal0" (pt "(1#2)*(y+d)"))
(use "y0Def")
;; Proof finished.
;; (cdp)
(save "LToReal")

;; SdBoundReal
(set-goal "all d(Sd d -> RealAbs d<<=1)")
(assume "d" "Sdd")
(use "RatLeToRealLe")
(use "SdBound")
(use "Sdd")
;; Proof finished.
;; (cdp)
(save "SdBoundReal")

;; LToBd
(set-goal "all x,n(L x n -> abs x<<=1)")
(assume "x" "n" "Lx")
(elim "Lx")
(assume "y" "Ry" "yBd")
(use "yBd")
(assume "d" "x1" "y" "n1" "Sdd" "Lx1n1" "x1Bd" "yDef")
(assert "Real x1")
(use "LToReal" (pt "n1"))
(use "Lx1n1")
(assume "Rx1")
(simpreal "yDef")
(use "RealLeAbs")
;; 19,20
(simpreal (pf "RealConstr([n](1#1))([p]Zero)===RealTimes(1#2)(RealPlus 1 1)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "abs x1"))
(use "RealLeIdAbs")
(use "Rx1")
(use "x1Bd")
(use "RealLeTrans" (pt "RealAbs d"))
(use "RealLeIdAbs")
(use "RealRat")
(use "SdBoundReal")
(use "Sdd")
;; ?^22:1===(1#2)*RealPlus 1 1
(use "RealEqRefl")
(use "RealRat")
;; ?^20:~((1#2)*(x1+d))<<=1
(simpreal "<-" (pf "~(RealUMinus 1)===1"))
(use "RealLeUMinus")
(simpreal
 (pf "RealUMinus 1===RealTimes(1#2)(RealPlus(RealUMinus 1)(RealUMinus 1))"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlusTwo")
(simpreal "<-" (pf "~ ~x1===x1"))
(use "RealLeUMinus")
(use "RealLeTrans" (pt "abs x1"))
(simpreal "<-" "RealAbsUMinus")
(use "RealLeIdAbs")
(autoreal)
(use "x1Bd")
(use "RealUMinusUMinus")
(use "Rx1")
(simpreal "<-" (pf "~(RealUMinus d)===d"))
(use "RealLeUMinus")
(use "RealLeTrans" (pt "RealAbs d"))
(simpreal "<-" "RealAbsUMinus")
(use "RealLeIdAbs")
(autoreal)
(use "SdBoundReal")
(use "Sdd")
(use "RealUMinusUMinus")
(use "RealRat")
(use "RealEqRefl")
(use "RealRat")
(use "RealUMinusUMinus")
(use "RealRat")
;; Proof finished.
;; (cdp)
(save "LToBd")

;; LCompat
(set-goal "allnc x,y,n(x===y -> L x n -> L y n)")
(cut "allnc x,n(L x n -> allnc y(x===y -> L y n))")
(assume "CutHyp" "x0" "x1" "n1" "x0=x1" "Lx0")
(use "CutHyp" (pt "x0"))
(auto)
(assume "x" "n" "Lx")
(elim "Lx")
(assume "z" "Rz" "zBd" "y" "z=y")
(intro 0)
(use "RealEqToReal1" (pt "z"))
(use "z=y")
(simpreal "<-" "z=y")
(use "zBd")
(assume "d0" "y0" "y1" "n2" "Sdd" "Ly0" "IH" "y1Def" "y2" "y1=y")
(intro 1 (pt "d0") (pt "y0"))
(auto)
(simpreal "<-" "y1=y")
(auto)
;; Proof finished.
;; (cdp)
(save "LCompat")

(define eterm (proof-to-extracted-term))
;; (pp (rename-variables (nt eterm)))
;; [u]u

(add-sound "LCompat")

;; ok, LCompatSound has been added as a new theorem:

;; allnc x,y,n(x===y -> allnc u^(LMR x n u^ -> LMR y n(cLCompat u^)))

;; with computation rule

;; cLCompat eqd([u]u)

;; We leave LCompat animated because it is simple.

;; LClosure
(set-goal
 "allnc x,n(L x(n+1) -> exr d,x0(Sd d andi x===(1#2)*(x0+d) andi L x0 n))")
(cut "allnc x,n,m(L x m -> m=n+1 ->
                  exr d,x0(Sd d andi x===(1#2)*(x0+d) andi L x0 n))")
(assume "CutHyp" "x" "n" "Lx")
(use "CutHyp" (pt "n+1"))
(use "Lx")
(use "Truth")
(assume "x" "n" "m" "Lxm")
(elim "Lxm")
(assume "x0" "Rx0" "x0Bd" "0=Sn")
(use "Efq")
(use "0=Sn")
(assume "d0" "x1" "y1" "n1" "Sdd0" "Lx1" "IH" "y1Def" "n1=n")
(intro 0 (pt "d0"))
(intro 0 (pt "x1"))
(split)
(use "Sdd0")
(split)
(use "y1Def")
(simp "<-" "n1=n")
(use "Lx1")
;; Proof finished.
;; (cdp)
(save "LClosure")

(define eterm (proof-to-extracted-term))
;; (ppc (rename-variables (nt eterm)))
;; [u][case u (U -> SdR pair U) (C s u -> s pair u)]

(add-sound "LClosure")

;; ok, LClosureSound has been added as a new theorem:

;; allnc x,n,u^(
;;  LMR x(n+1)u^ -> 
;;  (ExRTMR int
;;    sd yprod al
;;    (cterm (d,(sd yprod al)^) 
;;    (ExRTMR rea
;;      sd yprod al
;;      (cterm (x0,(sd yprod al)^0) 
;;      (AndDMR (cterm (s^) SdMR d s^)
;;        (cterm (u^0) 
;;        (AndRMR (cterm () x===(1#2)*(x0+d)) (cterm (u^1) LMR x0 n u^1))u^0))
;;      (sd yprod al)^0))
;;    (sd yprod al)^))
;;  (cLClosure u^))

;; with computation rule

;; cLClosure eqd([u][if u (SdR pair U) (PairConstr sd al)])

(deanimate "LClosure")

;; LSuccToL
(set-goal "all n allnc x(L x(n+1) -> L x n)")
(ind)
(assume "x" "Hyp")
(intro 0)
(use "LToReal" (pt "Succ Zero"))
(use "Hyp")
(use "LToBd" (pt "Succ Zero"))
(use "Hyp")
(assume "n" "IH" "x" "Hyp")
(inst-with-to "LClosure" (pt "x") (pt "Succ n") "Hyp" "ExHypx")
(by-assume "ExHypx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(intro 1 (pt "d1") (pt "x1"))
(use "d1x1Prop")
(use "IH")
(use "d1x1Prop")
(use "d1x1Prop")
;; Proof finished.
;; (cdp)
(save "LSuccToL")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n]
;;  (Rec nat=>al=>al)n([u]U)
;;  ([n0,(al=>al),u]C clft(cLClosure u)((al=>al)crht(cLClosure u)))

(add-sound "LSuccToL")

;; ok, LSuccToLSound has been added as a new theorem:

;; allnc n,x,u^(LMR x(n+1)u^ -> LMR x n(cLSuccToL n u^))

;; with computation rule

;; cLSuccToL eqd
;; ([n]
;;   (Rec nat=>al=>al)n([u]U)
;;   ([n0,(al=>al),u]C clft(cLClosure u)((al=>al)crht(cLClosure u))))

(deanimate "LSuccToL")

;; LToLPred
(set-goal "all n allnc x(L x n -> L x(Pred n))")
(ind)
(assume "x" "Hyp")
(intro 0)
(use "LToReal" (pt "Zero"))
(use "Hyp")
(use "LToBd" (pt "Zero"))
(use "Hyp")
(assume "n" "LH" "x" "Hyp")
(ng #t)
(use "LSuccToL")
(use "Hyp")
;; Proof finished.
;; (cdp)
(save "LToLPred")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [n,u][case n (Zero -> U) (Succ n0 -> cLSuccToL n0 u)]

(add-sound "LToLPred")

;; ok, LToLPredSound has been added as a new theorem:

;; allnc n,x,u^(LMR x n u^ -> LMR x(Pred n)(cLToLPred n u^))

;; with computation rule

;; cLToLPred eqd([n,u][if n U ([n0]cLSuccToL n0 u)])

(deanimate "LToLPred")

;; LUMinus
(set-goal "allnc x,n(L x n -> L(~x)n)")
(assume "x" "n" "Lxn")
(elim "Lxn")
(assume "x0" "Rx0" "x0Bd")
(intro 0)
(autoreal)
(simpreal "RealAbsUMinus")
(use "x0Bd")
(use "Rx0")
(assume "d" "x0" "y0" "n0" "Sdd" "Lx0" "L-x0" "y0Def")
(assert "Real x0")
(use "LToReal" (pt "n0"))
(use "Lx0")
(assume "Rx0")
(intro 1 (pt "~d") (pt "~x0"))
(use "SdUMinus")
(use "Sdd")
(use "L-x0")
(simpreal "<-" "RealUMinusPlusRat")
(simpreal "RealTimesIdUMinus")
(use "RealUMinusInj")
(use "RealEqTrans" (pt "((1#2)*(x0+d))"))
(simpreal "RealUMinusUMinus")
(use "y0Def")
(autoreal)
(simpreal "RealUMinusUMinus")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LUMinus")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [u](Rec al=>al)u U([s,u0]C(cSdUMinus s))
(animate "SdUMinus")
;; (ppc (rename-variables (nt neterm)))
;; [u](Rec al=>al)u U([s,u0]C[case s (SdR -> SdL) (SdM -> SdM) (SdL -> SdR)])
(deanimate "SdUMinus")

(add-sound "LUMinus")

;; ok, LUMinusSound has been added as a new theorem:

;; allnc x,n,u^(LMR x n u^ -> LMR(~x)n(cLUMinus u^))

;; with computation rule

;; cLUMinus eqd([u](Rec al=>al)u U([s,u0]C(cSdUMinus s)))

(deanimate "LUMinus")

(set! COMMENT-FLAG #f)
(load "~/git/minlog/examples/analysis/JK.scm")
(set! COMMENT-FLAG #t)

;; LAvToAvc
(set-goal "allnc x,y,n(L x(n+1) -> L y(n+1) -> 
 exr i,x1,y1(Sdtwo i andi L x1 n andi L y1 n andi
 (1#2)*(x+y)===(1#4)*(x1+y1+i)))")
(cut "allnc x,y,n,m(L x m -> L y m -> m=n+1 ->
 exr i,x1,y1(Sdtwo i andi L x1 n andi L y1 n andi
 (1#2)*(x+y)===(1#4)*(x1+y1+i)))")
(assume "CutHyp" "x" "y" "n" "Lx" "Ly")
(use "CutHyp" (pt "n+1"))
(auto)
(assume "x" "y" "n" "m" "Lx" "Ly" "m=Sn")
(assert "Real x")
(use "LToReal" (pt "m"))
(use "Lx")
(assume "Rx")
(assert "Real y")
(use "LToReal" (pt "m"))
(use "Ly")
(assume "Ry")
(simphyp-to "Lx" "m=Sn" "LxSn")
(simphyp-to "Ly" "m=Sn" "LySn")
(inst-with-to "LClosure" (pt "x") (pt "n") "LxSn" "Instx")
(inst-with-to "LClosure" (pt "y") (pt "n") "LySn" "Insty")
(by-assume "Instx" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "Insty" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(assert "Real x1")
(use "LToReal" (pt "n"))
(use "dx1Prop")
(assume "Rx1")
(assert "Real y1")
(use "LToReal" (pt "n"))
(use "ey1Prop")
(assume "Ry1")
(intro 0 (pt "d+e"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "IntPlusSdToSdtwo")
(use "dx1Prop")
(use "ey1Prop")
(split)
(use "dx1Prop")
(split)
(use "ey1Prop")
(assert "Real((1#4)*(x1+y1+(d+e)))")
(autoreal)
(assume "R")
(simpreal "dx1Prop")
(simpreal "ey1Prop")
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(use "RealEqSIntro")
(assume "n2")
(ng #t)
(simprat "<-" "RatTimesPlusDistr")
(ng #t)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
(simp (pf "d+bs n2=bs n2+d"))
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "RatPlusComm")
;; Proof finished.
;; (cdp)
(save "LAvToAvc")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [u,u0]
;;  cIntPlusSdToSdtwo clft(cLClosure u)clft(cLClosure u0)pair 
;;  crht(cLClosure u)pair crht(cLClosure u0)

(add-sound "LAvToAvc")

;; ok, LAvToAvcSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x(n+1)u^ -> 
;;  allnc u^0(
;;   LMR y(n+1)u^0 -> 
;;   (ExRTMR int
;;     sdtwo yprod al yprod al
;;     (cterm (i,(sdtwo yprod al yprod al)^) 
;;     (ExRTMR rea
;;       sdtwo yprod al yprod al
;;       (cterm (x0,(sdtwo yprod al yprod al)^0) 
;;       (ExRTMR rea
;;         sdtwo yprod al yprod al
;;         (cterm (y0,(sdtwo yprod al yprod al)^1) 
;;         (AndDMR (cterm (t^) SdtwoMR i t^)
;;           (cterm ((al yprod al)^2) 
;;           (AndDMR (cterm (u^1) LMR x0 n u^1)
;;             (cterm (u^1) 
;;             (AndLMR (cterm (u^2) LMR y0 n u^2)
;;               (cterm () (1#2)*(x+y)===(1#4)*(x0+y0+i)))
;;             u^1))
;;           (al yprod al)^2))
;;         (sdtwo yprod al yprod al)^1))
;;       (sdtwo yprod al yprod al)^0))
;;     (sdtwo yprod al yprod al)^))
;;   (cLAvToAvc u^ u^0)))

;; with computation rule

;; cLAvToAvc eqd
;; ([u,u0]
;;   cIntPlusSdToSdtwo clft(cLClosure u)clft(cLClosure u0)pair 
;;   crht(cLClosure u)pair crht(cLClosure u0))

(deanimate "LAvToAvc")

;; We can turn the extracted term of LAvToAvc into a more explicit form
;; by nimating its constants:

(animate "IntPlusSdToSdtwo")
(animate "LClosure")
(animate "Rht")
(animate "Lft")
;; (ppc (rename-variables (nt neterm)))

;; [u,u0]
;;  IntToSdtwo
;;  (SdToInt[case u (U -> SdR) (C s u1 -> s)]+
;;   SdToInt[case u0 (U -> SdR) (C s u1 -> s)])pair
;;  [case u (U -> U) (C s u1 -> u1)]pair[case u0 (U -> U) (C s u1 -> u1)]

;; However, for readability we prefer not to do this.

(deanimate "IntPlusSdToSdtwo")
(deanimate "LClosure")
(deanimate "Rht")
(deanimate "Lft")

(add-var-name "tuv" (py "sdtwo yprod al yprod al"))

;; LAvcSatLClAuxJ
(set-goal "allnc d,e,i(Sd d -> Sd e -> Sdtwo i -> Sdtwo(J(d+e+i*2)))")
(assume "d" "e" "i" "Sdd" "Sde" "Sdtwoi")
(assert "exl s1 SdInj d s1")
(use "SdInjIntro")
(use "Sdd")
(assume "ExHyp1")
(by-assume "ExHyp1" "s1" "s1Prop")
(assert "exl s2 SdInj e s2")
(use "SdInjIntro")
(use "Sde")
(assume "ExHyp2")
(by-assume "ExHyp2" "s2" "s2Prop")
(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdtwoInjElim"
     (pt "IntToSdtwo(J(SdToInt s1+SdToInt s2+SdtwoToInt t*2))"))
(simp (pf "J(SdToInt s1+SdToInt s2+SdtwoToInt t*2)=J(d+e+i*2)"))
(use "SdtwoInjIntToSdtwo")
;; ?^27:abs(J(d+e+i*2))<=2
(use "JProp")
(simp (pf "SdToInt s1+SdToInt s2+SdtwoToInt t*2=d+e+i*2"))
(use "Truth")
;; ?^29:SdToInt s1+SdToInt s2+SdtwoToInt t*2=d+e+i*2
(inst-with-to "SdInjId" (pt "d") (pt "s1") "s1Prop" "SdInjIdInst1")
(inst-with-to "SdInjId" (pt "e") (pt "s2") "s2Prop" "SdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "SdInjIdInst1")
(simp "SdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "LAvcSatLClAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [s,s0,t]IntToSdtwo(J(SdToInt s+SdToInt s0+SdtwoToInt t*2))

(add-sound "LAvcSatLClAuxJ")

;; ok, LAvcSatLClAuxJSound has been added as a new theorem:

;; allnc d,e,i,s^(
;;  SdMR d s^ -> 
;;  allnc s^0(
;;   SdMR e s^0 -> 
;;   allnc t^(SdtwoMR i t^ -> SdtwoMR(J(d+e+i*2))(cLAvcSatLClAuxJ s^ s^0 t^))))

;; with computation rule

;; cLAvcSatLClAuxJ eqd
;; ([s,s0,t]IntToSdtwo(J(SdToInt s+SdToInt s0+SdtwoToInt t*2)))

(deanimate "LAvcSatLClAuxJ")

;; LAvcSatLClAuxK
(set-goal "allnc d,e,i(Sd d -> Sd e -> Sdtwo i -> Sd(K(d+e+i*2)))")
(assume "d" "e" "i" "Sdd" "Sde" "Sdtwoi")
(assert "exl s1 SdInj d s1")
(use "SdInjIntro")
(use "Sdd")
(assume "ExHyp1")
(by-assume "ExHyp1" "s1" "s1Prop")
(assert "exl s2 SdInj e s2")
(use "SdInjIntro")
(use "Sde")
(assume "ExHyp2")
(by-assume "ExHyp2" "s2" "s2Prop")
(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdInjElim" (pt "IntToSd(K(SdToInt s1+SdToInt s2+SdtwoToInt t*2))"))
(simp (pf "K(SdToInt s1+SdToInt s2+SdtwoToInt t*2)=K(d+e+i*2)"))
(use "SdInjIntToSd")
;; ?^27:abs(K(d+e+i*2))<=1
(use "KProp")
;; ?^28:abs(d+e+i*2)<=6
(use "IntLeTrans" (pt "IntP 2+IntP 4"))
(use "IntLeTrans" (pt "abs(d+e)+abs(i*2)"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 1"))
(use "IntLeTrans" (pt "abs d+abs e"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "SdBound")
(use "Sdd")
(use "SdBound")
(use "Sde")
(use "Truth")
(ng #t)
(use "IntLeTrans" (pt "IntP 2*IntP 2"))
(use "IntLeMonTimes")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(use "Truth")
(simp (pf "SdToInt s1+SdToInt s2+SdtwoToInt t*2=d+e+i*2"))
(use "Truth")
;; ?^50:SdToInt s1+SdToInt s2+SdtwoToInt t*2=d+e+i*2
(inst-with-to "SdInjId" (pt "d") (pt "s1") "s1Prop" "SdInjIdInst1")
(inst-with-to "SdInjId" (pt "e") (pt "s2") "s2Prop" "SdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "SdInjIdInst1")
(simp "SdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "LAvcSatLClAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [s,s0,t]IntToSd(K(SdToInt s+SdToInt s0+SdtwoToInt t*2))

(add-sound "LAvcSatLClAuxK")

;; ok, LAvcSatLClAuxKSound has been added as a new theorem:

;; allnc d,e,i,s^(
;;  SdMR d s^ -> 
;;  allnc s^0(
;;   SdMR e s^0 -> 
;;   allnc t^(SdtwoMR i t^ -> SdMR(K(d+e+i*2))(cLAvcSatLClAuxK s^ s^0 t^))))

;; with computation rule

;; cLAvcSatLClAuxK eqd([s,s0,t]IntToSd(K(SdToInt s+SdToInt s0+SdtwoToInt t*2)))

(deanimate "LAvcSatLClAuxK")

;; LAvcSatLCl
(set-goal "allnc i,x,y,n(Sdtwo i -> L x(n+1) -> L y(n+1) ->
 exr j,d,x1,y1(Sd d andi Sdtwo j andi L x1 n andi L y1 n andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+j)+d)))")
(assume "i" "x" "y" "n" "Sdtwoi" "Lx" "Ly")
(inst-with-to "LClosure" (pt "x") (pt "n") "Lx" "LClosureInst1")
(by-assume "LClosureInst1" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(assert "L x1 n")
 (use "dx1Prop")
(assume "Lx1")
(inst-with-to "LClosure" (pt "y") (pt "n") "Ly" "LClosureInst2")
(by-assume "LClosureInst2" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
 (assert "L y1 n")
(use "ey1Prop")
(assume "Ly1")
(intro 0 (pt "J(d+e+i*2)"))
(intro 0 (pt "K(d+e+i*2)"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(assert "Real x")
(use "LToReal" (pt "n+1"))
(use "Lx")
(assume "Rx")
(assert "Real y")
(use "LToReal" (pt "n+1"))
(use "Ly")
(assume "Ry")
(assert "Real x1")
(use "LToReal" (pt "n"))
(use "Lx1")
(assume "Rx1")
(assert "Real y1")
(use "LToReal" (pt "n"))
(use "Ly1")
(assume "Ry1")
(split)
(use "LAvcSatLClAuxK")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
(use "LAvcSatLClAuxJ")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
(use "Lx1")
(split)
(use "Ly1")
(simpreal "dx1Prop")
(simpreal "ey1Prop")
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(use "RealEqSIntro")
(assume "n2")
(ng #t)
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(ng)
(use "RatEqvTrans" (pt "(1#8)*as n2+((d#8)+(1#8)*bs n2+(e#8)+(i#4))"))
(use "Truth")
(use "RatEqvTrans" (pt "(1#8)*as n2+((1#8)*bs n2+(J(d+e+i*2)#8)+(K(d+e+i*2)#2))"))
(use "RatPlusCompat")
(use "Truth")
(simp (pf "(d#8)+(1#8)*bs n2=(1#8)*bs n2+(d#8)"))
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(simprat (pf "(i#4)==(i*2#8)"))
(simprat (pf "(K(d+e+i*2)#2)==(K(d+e+i*2)*4#8)"))
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(simp (pf "J(d+e+i*2)+K(d+e+i*2)*4=K(d+e+i*2)*4+J(d+e+i*2)"))
(simp "KJProp")
(use "Truth")
(use "IntPlusComm")
(ng #t)
(simp "<-" "IntTimesAssoc")
(use "Truth")
(ng #t)
(simp "<-" "IntTimesAssoc")
(use "Truth")
(use "RatPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "LAvcSatLCl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
; (pp neterm)

;; [t,u,u0]
;;  cLAvcSatLClAuxK clft(cLClosure u)clft(cLClosure u0)t pair 
;;  cLAvcSatLClAuxJ clft(cLClosure u)clft(cLClosure u0)t pair 
;; crht(cLClosure u)pair crht(cLClosure u0)

(animate "LClosure")
(animate "LAvcSatLClAuxJ")
(animate "LAvcSatLClAuxK")
(animate "Rht")

;; (ppc (rename-variables (nt neterm)))

;; [t,u,u0]
;;  IntToSd
;;  (K
;;   (SdToInt clft[case u (U -> SdR pair U) (C s u -> s pair u)]+
;;    SdToInt clft[case u0 (U -> SdR pair U) (C s u -> s pair u)]+
;;    SdtwoToInt t*2))pair 
;;  IntToSdtwo
;;  (J
;;   (SdToInt clft[case u (U -> SdR pair U) (C s u -> s pair u)]+
;;    SdToInt clft[case u0 (U -> SdR pair U) (C s u -> s pair u)]+
;;    SdtwoToInt t*2))pair
;;  [case u (U -> U) (C s u1 -> u1)]pair[case u0 (U -> U) (C s u1 -> u1)]

;; This term can be read as follows.  Given t, u, u0, destruct the
;; latter two.  Both are composed, i.e., of the form C s v and C s0 v0.
;; Take their components s,v and s0,v0.  Then we obtain the quadruple
;; K(s,s0,t) pair J(s,s0,t) pair v pair v0.

(deanimate "LClosure")
(deanimate "LAvcSatLClAuxJ")
(deanimate "LAvcSatLClAuxK")
(deanimate "Rht")

(add-sound "LAvcSatLCl")

;; ok, LAvcSatLClSound has been added as a new theorem:

;; allnc i,x,y,n,t^(
;;  SdtwoMR i t^ -> 
;;  allnc u^(
;;   LMR x(n+1)u^ -> 
;;   allnc u^0(
;;    LMR y(n+1)u^0 -> 
;;    (ExRTMR int
;;      sd yprod sdtwo yprod al yprod al
;;      (cterm (j,(sd yprod sdtwo yprod al yprod al)^) 
;;      (ExRTMR int
;;        sd yprod sdtwo yprod al yprod al
;;        (cterm (d,(sd yprod sdtwo yprod al yprod al)^0) 
;;        (ExRTMR rea
;;          sd yprod sdtwo yprod al yprod al
;;          (cterm (x0,(sd yprod sdtwo yprod al yprod al)^1) 
;;          (ExRTMR rea
;;            sd yprod sdtwo yprod al yprod al
;;            (cterm (y0,(sd yprod sdtwo yprod al yprod al)^2) 
;;            (AndDMR (cterm (s^) SdMR d s^)
;;              (cterm (tuv^) 
;;              (AndDMR (cterm (t^0) SdtwoMR j t^0)
;;                (cterm ((al yprod al)^3) 
;;                (AndDMR (cterm (u^1) LMR x0 n u^1)
;;                  (cterm (u^1) 
;;                  (AndLMR (cterm (u^2) LMR y0 n u^2)
;;                    (cterm () (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d)))
;;                  u^1))
;;                (al yprod al)^3))
;;              tuv^))
;;            (sd yprod sdtwo yprod al yprod al)^2))
;;          (sd yprod sdtwo yprod al yprod al)^1))
;;        (sd yprod sdtwo yprod al yprod al)^0))
;;      (sd yprod sdtwo yprod al yprod al)^))
;;    (cLAvcSatLCl t^ u^ u^0))))

;; with computation rule

;; cLAvcSatLCl eqd
;; ([t,u,u0]
;;   cLAvcSatLClAuxK clft(cLClosure u)clft(cLClosure u0)t pair 
;;   cLAvcSatLClAuxJ clft(cLClosure u)clft(cLClosure u0)t pair 
;;   crht(cLClosure u)pair crht(cLClosure u0))

(deanimate "LAvcSatLCl")

(add-var-name "stuv" (py "sd yprod sdtwo yprod al yprod al"))

;; SdtwoBoundReal
(set-goal "all k(Sdtwo k -> RealAbs k<<=2)")
(assume "i" "Sdtwoi")
(use "RatLeToRealLe")
(use "SdtwoBound")
(use "Sdtwoi")
;; Proof finished.
;; (cdp)
(save "SdtwoBoundReal")

;; Putting things together

;; LAvcToL
(set-goal "allnc x,y,i all n(Sdtwo i -> L x n -> L y n  -> L((1#4)*(x+y+i))n)")
(cut " all n allnc x,y,i(Sdtwo i -> L x n -> L y n  -> L((1#4)*(x+y+i))n)")
(assume "CutHyp" "x" "y" "i" "n" "HypI" "HypII" "HypIII")
(use "CutHyp")
(auto)
(ind)
(assume "x" "y" "i" "Sdtwoi" "Lx0" "Ly0")
(assert "Real x")
(use-with "LToReal" (pt "x") (pt "Zero") "Lx0")
(assume "Rx")
(assert "Real y")
(use-with "LToReal" (pt "y") (pt "Zero") "Ly0")
(assume "Ry")
(intro 0)
(autoreal)
(assert "abs x<<=1")
(use-with "LToBd" (pt "x") (pt "Zero") "Lx0")
(assume "xBd")
(assert "abs y<<=1")
(use-with "LToBd" (pt "y") (pt "Zero") "Ly0")
(assume "yBd")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealAbs(1#4)*((RealPlus 1 1)+2)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeTrans" (pt "abs(x+y)+RealAbs i"))
;; 57,58
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "abs x+abs y"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "xBd")
(use "yBd")
(use "SdtwoBoundReal")
(use "Sdtwoi")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(assume "n" "IH" "x" "y" "i" "Sdtwoi" "Lx" "Ly")
(assert "exr j,d,x0,y0(
 Sd d andi Sdtwo j andi L x0 n andi L y0 n andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d))")
(use "LAvcSatLCl")
(use "Sdtwoi")
(use "Lx")
(use "Ly")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "LAvcSatLClInst")
(by-assume "LAvcSatLClInst" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume  "jdProp" "x2" "jdx2Prop")
(by-assume "jdx2Prop" "y2" "jdx2y2Prop")
(assert "Real x2")
(use "LToReal" (pt "n"))
(use "jdx2y2Prop")
(assume "Rx2")
(assert "Real y2")
(use "LToReal" (pt "n"))
(use "jdx2y2Prop")
(assume "Ry2")
(assert "Real x")
(use "LToReal" (pt "n+1"))
(use "Lx")
(assume "Rx")
(assert "Real y")
(use "LToReal" (pt "n+1"))
(use "Ly")
(assume "Ry")
(intro 1 (pt "d") (pt "(1#4)*(x2+y2+j)"))
(use "jdx2y2Prop")
(use "IH")
(use "jdx2y2Prop")
(use "jdx2y2Prop")
(use "jdx2y2Prop")
(use "jdx2y2Prop")
;; Proof finished.
;; (cdp)
(save "LAvcToL")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [n]
;;  (Rec nat=>sdtwo=>al=>al=>al)n([t,u,u0]U)
;;  ([n0,(sdtwo=>al=>al=>al),t,u,u0]
;;    [let stuv
;;      (cLAvcSatLCl t u u0)
;;      (C clft stuv
;;      ((sdtwo=>al=>al=>al)clft crht stuv clft crht crht stuv 
;;       crht crht crht stuv))])

;; Since let appears in the extracted term we must animate Id when
;; adding the soundness theorem.

;; (animate "Id")
(add-sound "LAvcToL")

;; ok, LAvcToLSound has been added as a new theorem:

;; allnc x,y,i,n,t^(
;;  SdtwoMR i t^ -> 
;;  allnc u^(
;;   LMR x n u^ -> 
;;   allnc u^0(LMR y n u^0 -> LMR((1#4)*(x+y+i))n(cLAvcToL n t^ u^ u^0))))

;; with computation rule

;; cLAvcToL eqd
;; ([n]
;;   (Rec nat=>sdtwo=>al=>al=>al)n([t,u,u0]U)
;;   ([n0,(sdtwo=>al=>al=>al),t,u,u0]
;;     [let stuv
;;       (cLAvcSatLCl t u u0)
;;       (C clft stuv
;;       ((sdtwo=>al=>al=>al)clft crht stuv clft crht crht stuv 
;;        crht crht crht stuv))]))

;; (deanimate "Id")
(deanimate "LAvcToL")

;; LAverage
(set-goal "allnc x,y all n(L x(n+1) -> L y(n+1) -> L((1#2)*(x+y))n)")
(assume "x" "y" "n" "Lx" "Ly")
(assert "Real x")
(use "LToReal" (pt "n+1"))
(use "Lx")
(assume "Rx")
(assert "Real y")
(use "LToReal" (pt "n+1"))
(use "Ly")
(assume "Ry")
(cut "exr i,x0,y0(Sdtwo i andd 
                  L x0 n andd L y0 n andl (1#2)*(x+y)===(1#4)*(x0+y0+i))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "LAvToAvcLnst")
(by-assume "LAvToAvcLnst" "i" "iProp")
(by-assume "iProp" "x1" "ix1Prop")
(by-assume "ix1Prop" "y1" "ix1y1Prop")
(use "LCompat" (pt "(1#4)*(x1+y1+i)"))
(use "RealEqSym")
(use "ix1y1Prop")
(use "LAvcToL")
(use "ix1y1Prop")
(use "ix1y1Prop")
(use "ix1y1Prop")
(use "LAvToAvc")
(use "Lx")
(use "Ly")
;; Proof finished.
;; (cdp)
(save "LAverage")

(define LAverage-eterm (proof-to-extracted-term))
(define LAverage-neterm (rename-variables (nt LAverage-eterm)))
;; (pp LAverage-neterm)

;; [n,u,u0]
;;  [let tuv (cLAvToAvc u u0) (cLAvcToL n clft tuv clft crht tuv crht crht tuv)]

;; (animate "Id")
(add-sound "LAverage")

;; ok, LAverageSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x(n+1)u^ -> 
;;  allnc u^0(LMR y(n+1)u^0 -> LMR((1#2)*(x+y))n(cLAverage n u^ u^0)))

;; with computation rule

;; cLAverage eqd
;; ([n,u,u0]
;;  [let tuv (cLAvToAvc u u0)
;;    (cLAvcToL n clft tuv clft crht tuv crht crht tuv)])

;; (deanimate "Id")
(deanimate "LAverage")

;; LZero
(set-goal "all n L 0 n")
(ind)
(intro 0)
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(assume "n" "IH")
(intro 1 (pt "0") (pt "RealConstr([n](0#1))([p]Zero)"))
(intro 1)
(use "IH")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LZero")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n](Rec nat=>al)n U([n0]C SdM)

(add-sound "LZero")

;; ok, LZeroSound has been added as a new theorem:

;; allnc n LMR 0 n(cLZero n)

;; with computation rule

;; cLZero eqd([n](Rec nat=>al)n U([n0]C SdM))

(deanimate "LZero")

;; LSdTimes
(set-goal "allnc d,x all n(Sd d -> L x n -> L(d*x)n)")
(assume "d" "x" "n" "Sdd")
(elim "Sdd")
;; 3-5
;; Case 1
(assume "Lx")
(assert "Real x")
(use "LToReal" (pt "n"))
(use "Lx")
(assume "Rx")
(use "LCompat" (pt "x") (pt "n"))
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "Lx")
;; 4
;; Case 0
(assume "Lx")
(assert "Real x")
(use "LToReal" (pt "n"))
(use "Lx")
(assume "Rx")
(use "LCompat" (pt "RealConstr([n](0#1))([p]Zero)") (pt "n"))
(simpreal "RealZeroTimes")
(use "RealEqRefl")
(autoreal)
(use "LZero")
;; 5
;; Case -1
(assume "Lx")
(assert "Real x")
(use "LToReal" (pt "n"))
(use "Lx")
(assume "Rx")
(inst-with-to "LUMinus" (pt "x") (pt "n") "Lx" "Lnst")
(use "LCompat" (pt "~x"))
(use "RealEqSym")
(use "RealIntNOneTimes")
(autoreal)
(use "Lnst")
;; Proof finished.
;; (cdp)
(save "LSdTimes")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,s,u][if s u (cLZero n) (cLUMinus u)]

(add-sound "LSdTimes")

;; ok, LSdTimesSound has been added as a new theorem:

;; allnc d,x,n,s^(
;;  SdMR d s^ -> allnc u^(LMR x n u^ -> LMR(d*x)n(cLSdTimes n s^ u^)))

;; with computation rule

;; cLSdTimes eqd([n,s,u][if s u (cLZero n) (cLUMinus u)])

(deanimate "LSdTimes")

;; LOne
(set-goal "all n L 1 n")
(ind)
(intro 0)
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(assume "n" "IH")
(intro 1 (pt "IntPos 1") (pt "RealConstr([n](1#1))([p]Zero)"))
(intro 0)
(use "IH")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LOne")

(define eterm (proof-to-extracted-term))
;; (pp (rename-variables (nt eterm)))
;; [n](Rec nat=>al)n U([n0]C SdR)

(add-sound "LOne")

;; ok, LOneSound has been added as a new theorem:

;; allnc n LMR 1 n(cLOne n)

;; with computation rule

;; cLOne eqd([n](Rec nat=>al)n U([n0]C SdR))

(deanimate "LOne")

;; LIntNOne
(set-goal "all n L(IntN 1)n")
(ind)
(intro 0)
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(assume "n" "IH")
(intro 1 (pt "IntNeg 1") (pt "RealConstr([n](~1#1))([p]Zero)"))
(intro 2)
(use "IH")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LIntNOne")

(define eterm (proof-to-extracted-term))
;; (pp (rename-variables (nt eterm)))
;; [n](Rec nat=>al)n U([n0]C SdL)

(add-sound "LIntNOne")

;; ok, LIntNOneSound has been added as a new theorem:

;; allnc n LMR(IntN 1)n(cLIntNOne n)

;; with computation rule

;; cLIntNOne eqd([n](Rec nat=>al)n U([n0]C SdL))

(deanimate "LIntNOne")

;; LMultcSatLClEq1
(set-goal "all x1,y,z0,d1,d0,i(Real x1 -> Real y -> Real z0 ->
 (1#4)*((1#2)*(x1+d1)*y+(1#2)*(z0+d0)+i)===
 (1#2)*((1#4)*(x1*y)+(1#4)*(z0+d1*y+i)+(1#4)*(RealPlus d0 i)))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "M0" "d" "d0" "i" "Rx1" "Ry" "Rz0")
(use "RealEqSToEq")
(autoreal)
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^13:(1#4)*((1#2)*(as n+d)*bs n+(1#2)*(cs n+d0)+i)==
;;      (1#2)*((1#4)*as n*bs n+(1#4)*(cs n+d*bs n+i)+(d0+i#4))
(use "RatEqvTrans" 
     (pt "(1#4)*((1#2)*((as n+d)*bs n)+(1#2)*(cs n+d0)+(1#2)*RatPlus i i)"))
(ng #t)
(simp (pf "2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; ?^15:(1#4)*((1#2)*((as n+d)*bs n)+(1#2)*(cs n+d0)+(1#2)*RatPlus i i)==
;;      (1#2)*((1#4)*as n*bs n+(1#4)*(cs n+d*bs n+i)+(d0+i#4))
;; Similarly replace (d0+i#4) by (1#4)*RatPlus d0 i.  Then cancel the factors
;; Finally use commutativity.
(use "RatEqvTrans"
     (pt "(1#2)*((1#4)*(as n*bs n)+(1#4)*(cs n+d*bs n+i)+(1#4)*RatPlus d0 i)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "(cs n+d*bs n)==(d*bs n+cs n)"))
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(use "RatEqvTrans" (pt "as n*bs n+d*bs n+(cs n+i+RatPlus d0 i)"))
(use "RatEqvTrans" (pt "as n*bs n+d*bs n+(cs n+d0+RatPlus i i)"))
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(simp "RatPlusAssoc")
(simp "RatPlusAssoc")
(use "RatPlusCompat")
(use "IntPlusComm")
(use "Truth")
(use "Truth")
(use "Truth")
(simp "RatPlusComm")
(use "Truth")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "LMultcSatLClEq1")

;; LMultcSatLClAvcDestr
(set-goal
 "allnc z0,d1,y,i all n(L z0(n+2) -> Sd d1 -> L y(n+2) -> Sdtwo i ->
  exr z2,e,e0(
  L z2 n andi Sd e andi Sd e0 andi (1#4)*(z0+d1*y+i)===(1#4)*(z2+e+2*e0)))")
(assume "z0" "d1" "y" "i" "n" "Lz0" "Sdd1" "Ly" "Sdtwoi")
(assert "Real z0")
(use "LToReal" (pt "n+2"))
(use "Lz0")
(assume "Rz0")
(assert "Real y")
(use "LToReal" (pt "n+2"))
(use "Ly")
(assume "Ry")
(assert "L((1#4)*(z0+d1*y+i))(n+2)")
(use "LAvcToL")
(use "Sdtwoi")
(use "Lz0")
(use "LSdTimes")
(use "Sdd1")
(use "Ly")
(assume "Lv")
(assert "exr d,x(Sd d andd (1#4)*(z0+d1*y+i)===(1#2)*(x+d) andr L x(n+1))")
(use "LClosure")
(use "Lv")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "Instv")
(by-assume "Instv" "e0" "e0Prop")
(by-assume "e0Prop" "z1" "e0z1Prop")
(assert "L z1(n+1)")
 (use "e0z1Prop")
(assume "Lz1")
(inst-with-to "LClosure" (pt "z1") (pt "n") "Lz1" "LClosureInstz1")
(by-assume "LClosureInstz1" "e" "eProp")
(by-assume "eProp" "z2" "ez2Prop")
(assert "L z2 n")
 (use "ez2Prop")
(assume "Lz2")
(assert "Real z2")
(use "LToReal" (pt "n"))
(use "Lz2")
(assume "Realz2")
(intro 0 (pt "z2"))
(intro 0 (pt "e"))
(intro 0 (pt "e0"))
(split)
(use "Lz2")
(split)
(use "ez2Prop")
(split)
(use "e0z1Prop")
;; (1#4)*(z0+d1*y+i)===(1#4)*(z2+e+2*e0)
(simpreal (pf "(1#4)*(z0+d1*y+i)===(1#2)*(z1+e0)"))
(simpreal (pf "z1===(1#2)*(z2+e)"))
;; (1#2)*((1#2)*(z2+e)+e0)===(1#4)*(z2+e+2*e0)
(assert "all z2 (1#2)*((1#2)*(z2+e)+e0)=+=(1#4)*(z2+e+2*e0)")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "m0")
(ng #t)
;; (1#2)*((1#2)*(as n+e)+e0)==(1#4)*(as n+e+2*e0)
(simprat (pf "e0==(1#2)*(2*e0)"))
(simprat "<-" "RatTimesPlusDistr")
(ng #t)
(use "Truth")
(ng #t)
(use "IntTimesComm")
;; Assertion proved.
(assume "Assertion")
(use "RealEqSToEq")
(autoreal)
(use "Assertion")
(use "ez2Prop")
(use "e0z1Prop")
;; Proof finished.
;; (cdp)
(save "LMultcSatLClAvcDestr")

(define eterm (proof-to-extracted-term))
(add-var-name "su" (py "sd yprod al"))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [n,u,s,u0,t]
;;  [let su
;;    (cLClosure(cLAvcToL(Succ(Succ n))t u(cLSdTimes(Succ(Succ n))s u0)))
;;    (crht(cLClosure crht su)pair clft(cLClosure crht su)pair clft su)]

;; (animate "Id")
(add-sound "LMultcSatLClAvcDestr")

;; ok, LMultcSatLClAvcDestrSound has been added as a new theorem:

;; allnc z,d,y,i,n,u^(
;;  LMR z(n+2)u^ -> 
;;  allnc s^(
;;   SdMR d s^ -> 
;;   allnc u^0(
;;    LMR y(n+2)u^0 -> 
;;    allnc t^(
;;     SdtwoMR i t^ -> 
;;     (ExRTMR rea
;;       al yprod sd yprod sd
;;       (cterm (z0,(al yprod sd yprod sd)^) 
;;       (ExRTMR int
;;         al yprod sd yprod sd
;;         (cterm (e,(al yprod sd yprod sd)^0) 
;;         (ExRTMR int
;;           al yprod sd yprod sd
;;           (cterm (e0,(al yprod sd yprod sd)^1) 
;;           (AndDMR (cterm (u^1) LMR z0 n u^1)
;;             (cterm ((sd yprod sd)^2) 
;;             (AndDMR (cterm (s^0) SdMR e s^0)
;;               (cterm (s^0) 
;;               (AndLMR (cterm (s^1) SdMR e0 s^1)
;;                 (cterm () (1#4)*(z+d*y+i)===(1#4)*(z0+e+2*e0)))
;;               s^0))
;;             (sd yprod sd)^2))
;;           (al yprod sd yprod sd)^1))
;;         (al yprod sd yprod sd)^0))
;;       (al yprod sd yprod sd)^))
;;     (cLMultcSatLClAvcDestr n u^ s^ u^0 t^)))))

;; with computation rule

;; cLMultcSatLClAvcDestr eqd
;; ([n,u,s,u0,t]
;;   [let su
;;     (cLClosure(cLAvcToL(Succ(Succ n))t u(cLSdTimes(Succ(Succ n))s u0)))
;;     (crht(cLClosure crht su)pair clft(cLClosure crht su)pair clft su)])

;; (deanimate "Id")
(deanimate "LMultcSatLClAvcDestr")

;; LMultcSatLClEq2
(set-goal "all x1,y,z2,e,e0,d0,i(Real x1 -> Real y -> Real z2 ->
 (1#2)*((1#4)*(x1*y)+(1#4)*(z2+e+2*e0)+(1#4)*RealPlus d0 i)===
 (1#2)*((1#4)*(x1*y+z2+J(e+2*e0+d0+i))+K(e+2*e0+d0+i)))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "M0" "e" "e0" "d0" "i" "Rx1" "Ry" "Rz2")
(use "RealEqSToEq")
(autoreal)
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "RatEqvTrans"
     (pt "(1#4)*as n*bs n+(1#4)*(cs n+e+2*e0)+(1#4)*RatPlus d0 i"))
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "RatEqvTrans" (pt "(1#4)*as n*bs n+(1#4)*(cs n+e+2*e0+d0+i)"))
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(simprat (pf "K(e+2*e0+d0+i)==(1#4)*(K(e+2*e0+d0+i)*4)"))
(simprat "<-" "RatTimesPlusDistr")
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
(simp (pf "J(e+2*e0+d0+i)+K(e+2*e0+d0+i)*4=K(e+2*e0+d0+i)*4+J(e+2*e0+d0+i)"))
(use "KJProp")
(use "IntPlusComm")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "LMultcSatLClEq2")

;; LMultcSatLClAuxJ
(set-goal "allnc e,e0,d0,i(Sd e -> Sd e0 -> Sd d0 -> Sdtwo i ->
 Sdtwo(J(e+2*e0+d0+i)))")
(assume "e" "e0" "d0" "i" "Sde" "Sde0" "Sdd0" "Sdtwoi")
(assert "exl s1 SdInj e s1")
(use "SdInjIntro")
(use "Sde")
(assume "ExHyp1")
(by-assume "ExHyp1" "s1" "s1Prop")
(assert "exl s2 SdInj e0 s2 ")
(use "SdInjIntro")
(use "Sde0")
(assume "ExHyp2")
(by-assume "ExHyp2" "s2" "s2Prop")
(assert "exl s1 SdInj d0 s1")
(use "SdInjIntro")
(use "Sdd0")
(assume "ExHyp3")
(by-assume "ExHyp3" "s3" "s3Prop")
(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")
(use "SdtwoInjElim"
     (pt "IntToSdtwo(J(SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t))"))
(simp (pf "J(SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t)=J(e+2*e0+d0+i)"))
(use "SdtwoInjIntToSdtwo")
;; ?_34:abs(J(e+2*e0+d0+i))<=2
(use "JProp")
(simp (pf "SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t=e+2*e0+d0+i"))
(use "Truth")
;; ?_36:SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t=e+2*e0+d0+i
(inst-with-to "SdInjId" (pt "e") (pt "s1") "s1Prop" "SdInjIdInst1")
(inst-with-to "SdInjId" (pt "e0") (pt "s2") "s2Prop" "SdInjIdInst2")
(inst-with-to "SdInjId" (pt "d0") (pt "s3") "s3Prop" "SdInjIdInst3")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "SdInjIdInst1")
(simp "SdInjIdInst2")
(simp "SdInjIdInst3")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "LMultcSatLClAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [s,s0,s1,t]IntToSdtwo(J(SdToInt s+2*SdToInt s0+SdToInt s1+SdtwoToInt t))

(add-sound "LMultcSatLClAuxJ")

;; ok, LMultcSatLClAuxJSound has been added as a new theorem:

;; allnc e,e0,d,i,s^(
;;  SdMR e s^ -> 
;;  allnc s^0(
;;   SdMR e0 s^0 -> 
;;   allnc s^1(
;;    SdMR d s^1 -> 
;;    allnc t^(
;;     SdtwoMR i t^ -> SdtwoMR(J(e+2*e0+d+i))(cLMultcSatLClAuxJ s^ s^0 s^1 t^)))))

;; with computation rule

;; cLMultcSatLClAuxJ eqd
;; ([s,s0,s1,t]IntToSdtwo(J(SdToInt s+2*SdToInt s0+SdToInt s1+SdtwoToInt t)))

(deanimate "LMultcSatLClAuxJ")

;; LMultcSatLClAuxK
(set-goal "allnc e,e0,d0,i(Sd e -> Sd e0 -> Sd d0 -> Sdtwo i ->
 Sd(K(e+2*e0+d0+i)))")
(assume "e" "e0" "d0" "i" "Sde" "Sde0" "Sdd0" "Sdtwoi")
(assert "exl s1 SdInj e s1")
(use "SdInjIntro")
(use "Sde")
(assume "ExHyp1")
(by-assume "ExHyp1" "s1" "s1Prop")
(assert "exl s2 SdInj e0 s2 ")
(use "SdInjIntro")
(use "Sde0")
(assume "ExHyp2")
(by-assume "ExHyp2" "s2" "s2Prop")
(assert "exl s1 SdInj d0 s1")
(use "SdInjIntro")
(use "Sdd0")
(assume "ExHyp3")
(by-assume "ExHyp3" "s3" "s3Prop")
(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")
(use "SdInjElim"
     (pt "IntToSd(K(SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t))"))
(simp (pf "K(SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t)=K(e+2*e0+d0+i)"))
(use "SdInjIntToSd")
;; ?_34:abs(K(e+2*e0+d0+i))<=1
(use "KProp")
;; ?_35:abs(e+2*e0+d0+i)<=6
(use "IntLeTrans" (pt "IntP 4+IntP 2"))
(use "IntLeTrans" (pt "abs(e+2*e0+d0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 3+IntP 1"))
(use "IntLeTrans" (pt "abs(e+2*e0)+abs d0"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs e+abs(2*e0)"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "SdBound")
(use "Sde")
(ng)
(simp "IntTimesComm")
(use "IntLeTrans" (pt "IntP 1*2"))
(use "IntLeMonTimes")
(use "Truth")
(use "SdBound")
(use "Sde0")
(use "Truth")
(use "Truth")
(use "SdBound")
(use "Sdd0")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t=e+2*e0+d0+i"))
(use "Truth")
;; ?_65:SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t=e+2*e0+d0+i
(inst-with-to "SdInjId" (pt "e") (pt "s1") "s1Prop" "SdInjIdInst1")
(inst-with-to "SdInjId" (pt "e0") (pt "s2") "s2Prop" "SdInjIdInst2")
(inst-with-to "SdInjId" (pt "d0") (pt "s3") "s3Prop" "SdInjIdInst3")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "SdInjIdInst1")
(simp "SdInjIdInst2")
(simp "SdInjIdInst3")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "LMultcSatLClAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [s,s0,s1,t]IntToSd(K(SdToInt s+2*SdToInt s0+SdToInt s1+SdtwoToInt t))

(add-sound "LMultcSatLClAuxK")

;; ok, LMultcSatLClAuxKSound has been added as a new theorem:

;; allnc e,e0,d,i,s^(
;;  SdMR e s^ -> 
;;  allnc s^0(
;;   SdMR e0 s^0 -> 
;;   allnc s^1(
;;    SdMR d s^1 -> 
;;    allnc t^(
;;     SdtwoMR i t^ -> SdMR(K(e+2*e0+d+i))(cLMultcSatLClAuxK s^ s^0 s^1 t^)))))

;; with computation rule

;; cLMultcSatLClAuxK eqd
;; ([s,s0,s1,t]IntToSd(K(SdToInt s+2*SdToInt s0+SdToInt s1+SdtwoToInt t)))

(deanimate "LMultcSatLClAuxK")

;; LMultToMultc
(set-goal "allnc x,y all n(L x(n+3) -> L y(n+3) ->
 exr i,x1,y1,z1(L y1 (n+2) andi Sdtwo i andi L x1 (n+2) andi L z1 n andi
 x*y===(1#4)*(x1*y1+z1+i)))")
(assume "x" "y" "n" "Lx" "Ly")
(inst-with-to "LClosure" (pt "x") (pt "n+2") "Lx" "ExHypx")
(by-assume "ExHypx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(inst-with-to "LClosure" (pt "y") (pt "n+2") "Ly" "ExHypy")
(by-assume "ExHypy" "e1" "e1Prop")
(by-assume "e1Prop" "y1" "e1y1Prop")
(assert "L((1#2)*(e1*x1+d1*y1)) (n+1)")
(use "LAverage")
(use "LSdTimes")
(use "e1y1Prop")
(use "d1x1Prop")
(use "LSdTimes")
(use "d1x1Prop")
(use "e1y1Prop")
(assume "LAvxy")
(inst-with-to
 "LClosure" (pt "(1#2)*(e1*x1+d1*y1)") (pt "n") "LAvxy" "ExHypAvxy")
(by-assume "ExHypAvxy" "d" "dProp")
(by-assume "dProp" "z1" "dz1Prop")
(intro 0 (pt "d+d1*e1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(intro 0 (pt "z1"))
(assert "Real x1")
(use "LToReal" (pt "n+2"))
(use "d1x1Prop")
(assume "Rx1")
(assert "Real y1")
(use "LToReal" (pt "n+2"))
(use "e1y1Prop")
(assume "Ry1")
(assert "Real z1")
(use "LToReal" (pt "n"))
(use "dz1Prop")
(assume "Rz1")
(assert "Real x")
(use "LToReal" (pt "n+3"))
(use "Lx")
(assume "Rx")
(assert "Real y")
(use "LToReal" (pt "n+3"))
(use "Ly")
(assume "Ry")
(split)
(use "e1y1Prop")
(split)
(use "IntPlusSdToSdtwo")
(use "dz1Prop")
(use "IntTimesSdToSd")
(use "d1x1Prop")
(use "e1y1Prop")
(split)
(use "d1x1Prop")
(split)
(use "dz1Prop")
(assert "Real((1#4)*(x1*y1+z1+(d+d1*e1)))")
(autoreal)
(assume "R")
(simpreal "d1x1Prop")
(simpreal (pf "y===(y1+e1)*(1#2)"))
(simpreal "RealTimesAssoc")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(ng)
(simpreal "<-" "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "<-" "RealPlusAssoc")
(use "RealEqSym")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealPlusAssoc")
(simpreal (pf "d1*y1+x1*e1===z1+d"))
(simpreal "<-" "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
(simpreal (pf "d1*y1+x1*e1===(1#2)*(e1*x1+d1*y1)*2"))
(assert "Real(z1+d)")
(autoreal)
(assume "Rzd")
(use "RealEqTrans" (pt "(1#2)*(z1+d)*2"))
(use "RealTimesCompat")
(use "dz1Prop")
(use "RealEqRefl")
(use "RealRat")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(ng)
(use "RealOneTimes")
(autoreal)
(use "RealEqSym")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(simpreal "RealPlusComm")
(ng)
(simpreal (pf "x1*e1===e1*x1"))
(use "RealOneTimes")
(autoreal)
(use "RealTimesComm")
(use "Rx1")
(use "RealRat")
(use "RealTimesReal")
(use "RealRat")
(use "Ry1")
(use "RealTimesReal")
(use "RealRat")
(use "Rx1")
(use "RealPlusReal")
(use "RealTimesReal")
(use "RealRat")
(use "Rx1")
(use "RealTimesReal")
(use "RealRat")
(use "Ry1")
(use "RealRat")
(use "RealRat")
(use "RealRat")
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "RealTimesReal")
(use "RealRat")
(use "Rx1")
(use "RealTimesReal")
(use "RealRat")
(use "Ry1")
(use "RealRat")
(use "RealTimesReal")
(use "Rx1")
(use "RealRat")
(use "RealTimesReal")
(use "RealRat")
(use "Ry1")
(use "RealRat")
(use "RealRat")
(use "Rx1")
(use "RealRat")
(autoreal)
(simpreal "RealTimesComm")
(use "e1y1Prop")
(use "RealRat")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LMultToMultc")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n,u,u0]
;;  crht(cLClosure u0)pair 
;;  cIntPlusSdToSdtwo 
;;  clft(cLClosure
;;       (cLAverage(Succ n)
;;        (cLSdTimes(Succ(Succ n))clft(cLClosure u0)crht(cLClosure u))
;;        (cLSdTimes(Succ(Succ n))clft(cLClosure u)crht(cLClosure u0))))
;;  (cIntTimesSdToSd clft(cLClosure u)clft(cLClosure u0))pair 
;;  crht(cLClosure u)pair 
;;  crht(cLClosure
;;       (cLAverage(Succ n)
;;        (cLSdTimes(Succ(Succ n))clft(cLClosure u0)crht(cLClosure u))
;;        (cLSdTimes(Succ(Succ n))clft(cLClosure u)crht(cLClosure u0))))

(add-sound "LMultToMultc")

;; ok, LMultToMultcSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x(n+3)u^ -> 
;;  allnc u^0(
;;   LMR y(n+3)u^0 -> 
;;   (ExRTMR int
;;     al yprod sdtwo yprod al yprod al
;;     (cterm (i,(al yprod sdtwo yprod al yprod al)^) 
;;     (ExRTMR rea
;;       al yprod sdtwo yprod al yprod al
;;       (cterm (x0,(al yprod sdtwo yprod al yprod al)^0) 
;;       (ExRTMR rea
;;         al yprod sdtwo yprod al yprod al
;;         (cterm (y0,(al yprod sdtwo yprod al yprod al)^1) 
;;         (ExRTMR rea
;;           al yprod sdtwo yprod al yprod al
;;           (cterm (z,(al yprod sdtwo yprod al yprod al)^2) 
;;           (AndDMR (cterm (u^1) LMR y0(n+2)u^1)
;;             (cterm (tuv^) 
;;             (AndDMR (cterm (t^) SdtwoMR i t^)
;;               (cterm ((al yprod al)^3) 
;;               (AndDMR (cterm (u^1) LMR x0(n+2)u^1)
;;                 (cterm (u^1) 
;;                 (AndLMR (cterm (u^2) LMR z n u^2)
;;                   (cterm () x*y===(1#4)*(x0*y0+z+i)))
;;                 u^1))
;;               (al yprod al)^3))
;;             tuv^))
;;           (al yprod sdtwo yprod al yprod al)^2))
;;         (al yprod sdtwo yprod al yprod al)^1))
;;       (al yprod sdtwo yprod al yprod al)^0))
;;     (al yprod sdtwo yprod al yprod al)^))
;;   (cLMultToMultc n u^ u^0)))

;; with computation rule

;; cLMultToMultc eqd
;; ([n,u,u0]
;;   crht(cLClosure u0)pair 
;;   cIntPlusSdToSdtwo 
;;   clft(cLClosure
;;        (cLAverage(Succ n)
;;         (cLSdTimes(Succ(Succ n))clft(cLClosure u0)crht(cLClosure u))
;;         (cLSdTimes(Succ(Succ n))clft(cLClosure u)crht(cLClosure u0))))
;;   (cIntTimesSdToSd clft(cLClosure u)clft(cLClosure u0))pair 
;;   crht(cLClosure u)pair 
;;   crht(cLClosure
;;        (cLAverage(Succ n)
;;         (cLSdTimes(Succ(Succ n))clft(cLClosure u0)crht(cLClosure u))
;;         (cLSdTimes(Succ(Succ n))clft(cLClosure u)crht(cLClosure u0)))))

(deanimate "LMultToMultc")

;; LMultcSatLCl
(set-goal
 "allnc y,i,x,z,m all n(L y(n+2) -> Sdtwo i andi L x(m+1) andi L z(n+3) ->
 exr d,j,x1,z1(Sd d andi Sdtwo j andi L x1 m andi L z1 n andi
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z1+j)+d)))")
(assume "y" "i" "x" "z" "m" "n" "Ly" "Conj")
(assert "L x(m+1)")
(use "Conj")
(assume "Lx")
(assert "L z(n+3)")
(use "Conj")
(assume "Lz")
(assert "exr d1,x1(Sd d1 andi L x1 m  andi x===(1#2)*(x1+d1))")
(inst-with-to "LClosure" (pt "x") (pt "m") "Lx" "ExHypx")
(by-assume "ExHypx" "d0" "ConjI")
(by-assume "ConjI" "x0" "ConjII")
(intro 0 (pt "d0"))
(intro 0 (pt "x0"))
(msplit)
(use "ConjII")
(use "ConjII")
(use "ConjII")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHypx")
(by-assume "ExHypx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(assert "exr d0,z0(Sd d0 andi L z0 (n+2) andi z===(1#2)*(z0+d0))")
(inst-with-to "LClosure" (pt "z") (pt "n+2") "Lz" "ExHypz")
(by-assume "ExHypz" "d0" "ConjI")
(by-assume "ConjI" "x0" "ConjII")
(intro 0 (pt "d0"))
(intro 0 (pt "x0"))
(msplit)
(use "ConjII")
(use "ConjII")
(use "ConjII")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHypz")
(by-assume "ExHypz" "d0" "d0Prop")
(by-assume "d0Prop" "z0" "d0z0Prop")
(assert "exr z2,e,e0(L z2 n andd 
  Sd e andd Sd e0 andl (1#4)*(z0+d1*y+i)===(1#4)*(z2+e+2*e0))")
(use "LMultcSatLClAvcDestr")
(use "d0z0Prop")
(use "d1x1Prop")
(use "Ly")
(use "Conj")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "AvcUnfolding")
(by-assume "AvcUnfolding" "z2" "z2Prop")
(by-assume "z2Prop" "e" "z2eProp")
(by-assume "z2eProp" "e0" "z2ee0Prop")
(intro 0 (pt "K(e+2*e0+d0+i)"))
(intro 0 (pt "J(e+2*e0+d0+i)"))
(intro 0 (pt "x1"))
(intro 0 (pt "z2"))
(assert "Real x1")
(use "LToReal" (pt "m"))
(use "d1x1Prop")
(assume "Rx1")
(assert "Real y")
(use "LToReal" (pt "n+2"))
(use "Ly")
(assume "Ry")
(assert "Real z0")
(use "LToReal" (pt "n+2"))
(use "d0z0Prop")
(assume "Rz0")
(assert "Real z2")
(use "LToReal" (pt "n"))
(use "z2ee0Prop")
(assume "Rz2")
(assert "Real z")
(use "LToReal" (pt "n+3"))
(use "Conj")
(assume "Rz")
(split)
(use "LMultcSatLClAuxK")
(use "z2ee0Prop")
(use "z2ee0Prop")
(use "d0z0Prop")
(use "Conj")
(split)
(use "LMultcSatLClAuxJ")
(use "z2ee0Prop")
(use "z2ee0Prop")
(use "d0z0Prop")
(use "Conj")
(split)
(use "d1x1Prop")
(split)
(use "z2ee0Prop")
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1+d1)*y+(1#2)*(z0+d0)+i)"))
(simpreal "d1x1Prop")
(simpreal "d0z0Prop")
(use "RealEqRefl")
(autoreal)
(use "RealEqTrans"
     (pt "(1#2)*((1#4)*(x1*y)+(1#4)*(z2+e+2*e0)+(1#4)*RealPlus d0 i)"))
(simpreal "<-" "z2ee0Prop")
(simpreal "LMultcSatLClEq1")
(use "RealEqRefl")
(autoreal)
(use "LMultcSatLClEq2")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LMultcSatLCl")

(define eterm (proof-to-extracted-term))
(add-var-name "uv" (py "al yprod al"))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n,u,tuv]
;;  [let su
;;    (cLClosure clft crht tuv)
;;    [let su0
;;     (cLClosure crht crht tuv)
;;     [let (al yprod sd yprod sd)
;;      (cLMultcSatLClAvcDestr n crht su0 clft su u clft tuv)
;;      (cLMultcSatLClAuxK clft crht(al yprod sd yprod sd)
;;      crht crht(al yprod sd yprod sd)
;;      clft su0 
;;      clft tuv pair 
;;      cLMultcSatLClAuxJ clft crht(al yprod sd yprod sd)
;;      crht crht(al yprod sd yprod sd)
;;      clft su0 
;;      clft tuv pair 
;;      crht su pair clft(al yprod sd yprod sd))]]]

;; (animate "Id")
(add-sound "LMultcSatLCl")

;; ok, LMultcSatLClSound has been added as a new theorem:

;; allnc y,i,x,z,m,n,u^(
;;  LMR y(n+2)u^ -> 
;;  allnc tuv^(
;;   (AndDMR (cterm (t^) SdtwoMR i t^)
;;     (cterm (uv^) 
;;     (AndDMR (cterm (u^0) LMR x(m+1)u^0) (cterm (u^0) LMR z(n+3)u^0))uv^))
;;   tuv^ -> 
;;   (ExRTMR int
;;     sd yprod sdtwo yprod al yprod al
;;     (cterm (d,stuv^) 
;;     (ExRTMR int
;;       sd yprod sdtwo yprod al yprod al
;;       (cterm (j,stuv^0) 
;;       (ExRTMR rea
;;         sd yprod sdtwo yprod al yprod al
;;         (cterm (x0,stuv^1) 
;;         (ExRTMR rea
;;           sd yprod sdtwo yprod al yprod al
;;           (cterm (z0,stuv^2) 
;;           (AndDMR (cterm (s^) SdMR d s^)
;;             (cterm (tuv^0) 
;;             (AndDMR (cterm (t^) SdtwoMR j t^)
;;               (cterm (uv^) 
;;               (AndDMR (cterm (u^0) LMR x0 m u^0)
;;                 (cterm (u^0) 
;;                 (AndLMR (cterm (u^1) LMR z0 n u^1)
;;                   (cterm () (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))
;;                 u^0))
;;               uv^))
;;             tuv^0))
;;           stuv^2))
;;         stuv^1))
;;       stuv^0))
;;     stuv^))
;;   (cLMultcSatLCl n u^ tuv^)))

;; with computation rule

;; cLMultcSatLCl eqd
;; ([n,u,tuv]
;;   [let su
;;     (cLClosure clft crht tuv)
;;     [let su0
;;      (cLClosure crht crht tuv)
;;      [let (al yprod sd yprod sd)
;;       (cLMultcSatLClAvcDestr n crht su0 clft su u clft tuv)
;;       (cLMultcSatLClAuxK clft crht(al yprod sd yprod sd)
;;       crht crht(al yprod sd yprod sd)
;;       clft su0 
;;       clft tuv pair 
;;       cLMultcSatLClAuxJ clft crht(al yprod sd yprod sd)
;;       crht crht(al yprod sd yprod sd)
;;       clft su0 
;;       clft tuv pair 
;;       crht su pair clft(al yprod sd yprod sd))]]])

(deanimate "LMultcSatLCl")

;; LMultcToL
;; (set! COMMENT-FLAL #f)
(set-goal "all n allnc x0,y0,z0,i(
 L y0(3*n--1) -> Sdtwo i -> L x0(3*n) -> L z0(3*n) -> L((1#4)*(x0*y0+z0+i))n)")
(ind)
(assume "x" "y" "z" "i" "Ly" "Sdtwoi" "Lx" "Lz")
(assert "Real x")
(use "LToReal" (pt "3*Zero"))
(use "Lx")
(assume "Rx")
(assert "Real z")
(use "LToReal" (pt "3*Zero"))
(use "Lz")
(assume "Rz")
(assert "Real y")
(use "LToReal" (pt "3*Zero--1"))
(use "Ly")
(assume "Ry")
(intro 0)
(autoreal)
(inst-with-to "LToBd" (pt "x") (pt "3*Zero") "Lx" "xBd")
(inst-with-to "LToBd" (pt "y") (pt "3*Zero--1") "Ly" "yBd")
(inst-with-to "LToBd" (pt "z") (pt "3*Zero") "Lz" "zBd")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealAbs(1#4)*(((RealTimes 1 1)+1)+2)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeTrans" (pt "abs(x*y+z)+RealAbs i"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "abs(x*y)+abs z"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(simpreal "RealAbsTimes")
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "xBd")
(use "yBd")
(autoreal)
(use "zBd")
(use "SdtwoBoundReal")
(use "Sdtwoi")
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(assume "n" "IH" "x" "y" "z" "i" "Ly" "Sdtwoi" "Lx" "Lz")
(assert "exr d,j,x0,z0(
 Sd d andi Sdtwo j andi L x0(3*n+2) andi L z0(3*n) andi
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))")
;; (pp "LMultcSatLCl")
(use "LMultcSatLCl")
(simp (pf "3*n+2=3*(Succ n)--1"))
(use "Ly")
(ng #t)
(use "Truth")
(split)
(use "Sdtwoi")
(simp (pf "3*n+3=3*(Succ n)"))
(split)
(use "Lx")
(use "Lz")
(ng #t)
(use "Truth")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "LMultcSatLClInst")
(by-assume "LMultcSatLClInst" "d" "dProp")
(by-assume "dProp" "j" "djProp")
(by-assume "djProp" "x2" "djx2Prop")
(by-assume "djx2Prop" "z2" "djx2z2Prop")
(assert "Real x2")
(use "LToReal" (pt "3*n+2"))
(use "djx2z2Prop")
(assume "Rx2")
(assert "Real z2")
(use "LToReal" (pt "3*n"))
(use "djx2z2Prop")
(assume "Rz2")
(assert "L x2 (3*n+2)")
(use "djx2z2Prop")
(assume "Lx2")
(assert "L z2 (3*n)")
(use "djx2z2Prop")
(assume "Lz2")
(intro 1 (pt "d") (pt "(1#4)*(x2*y+z2+j)"))
(use "djx2z2Prop")
(use "IH")
(ng)
(use "LToLPred")
(use "LSuccToL")
(use "LSuccToL")
(use "Ly")
(use "djx2z2Prop")
(use "LSuccToL")
(use "LSuccToL")
(use "Lx2")
(use "Lz2")
(use "djx2z2Prop")
;; Proof finished.
;; (cdp)
(save "LMultcToL")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n]
;;  (Rec nat=>al=>sdtwo=>al=>al=>al)n([u,t,u0,u1]U)
;;  ([n0,(al=>sdtwo=>al=>al=>al),u,t,u0,u1]
;;    [let stuv
;;      (cLMultcSatLCl(n0+n0+n0)u(t pair u0 pair u1))
;;      (C clft stuv
;;      ((al=>sdtwo=>al=>al=>al)
;;       (cLToLPred(n0+n0+n0)(cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u)))
;;       clft crht stuv
;;       (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))clft crht crht stuv))
;;       crht crht crht stuv))])

(add-sound "LMultcToL")

;; ok, LMultcToLSound has been added as a new theorem:

;; allnc n,x,y,z,i,u^(
;;  LMR y(3*n--1)u^ -> 
;;  allnc t^(
;;   SdtwoMR i t^ -> 
;;   allnc u^0(
;;    LMR x(3*n)u^0 -> 
;;    allnc u^1(
;;     LMR z(3*n)u^1 -> LMR((1#4)*(x*y+z+i))n(cLMultcToL n u^ t^ u^0 u^1)))))

;; with computation rule

;; cLMultcToL eqd
;; ([n]
;;   (Rec nat=>al=>sdtwo=>al=>al=>al)n([u,t,u0,u1]U)
;;   ([n0,(al=>sdtwo=>al=>al=>al),u,t,u0,u1]
;;     [let stuv
;;       (cLMultcSatLCl(n0+n0+n0)u(t pair u0 pair u1))
;;       (C clft stuv
;;       ((al=>sdtwo=>al=>al=>al)
;;        (cLToLPred(n0+n0+n0)(cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u)))
;;        clft crht stuv
;;        (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))clft crht crht stuv))
;;        crht crht crht stuv))]))

(deanimate "LMultcToL")

;; LMultOld
(set-goal "allnc x,y all n(L x(3*n+3) -> L y(3*n+3) -> L(x*y)n)")
(assume "x" "y" "n" "Lx" "Ly")
(assert "exr i,x0,y0,z(
 L y0(3*n+3--1) andi Sdtwo i andi L x0(3*n+3--1) andi L z(3*n+3--3) andi
 x*y===(1#4)*(x0*y0+z+i))")
(use "LMultToMultc")
(use "Lx")
(use "Ly")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "LMultToMultcInst")
(by-assume "LMultToMultcInst" "i" "iProp")
(by-assume "iProp" "x1" "ix1Prop")
(by-assume "ix1Prop" "y1" "ix1y1Prop")
(by-assume "ix1y1Prop" "z" "ix1y1zProp")
(use "LCompat" (pt "(1#4)*(x1*y1+z+i)"))
(use "RealEqSym")
(use "ix1y1zProp")
(use "LMultcToL")
(use "LToLPred")
(ng)
(use "LSuccToL")
(use "LSuccToL")
(use "ix1y1zProp")
(use "ix1y1zProp")
;; (use "LToLPred")
(ng)
(use "LSuccToL")
(use "LSuccToL")
(use "ix1y1zProp")
(use "ix1y1zProp")
;; Proof finished.
;; (cdp)
(save "LMultOld")

(define eterm (proof-to-extracted-term))
(add-var-name "wtuv" (py "al yprod sdtwo yprod al yprod al"))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n,u,u0]
;;  [let wtuv
;;    (cLMultToMultc(n+n+n)u u0)
;;    (cLMultcToL n
;;    (cLToLPred(n+n+n)(cLSuccToL(n+n+n)(cLSuccToL(Succ(n+n+n))clft wtuv)))
;;    clft crht wtuv
;;    (cLSuccToL(n+n+n)(cLSuccToL(Succ(n+n+n))clft crht crht wtuv))
;;    crht crht crht wtuv)]

(add-sound "LMultOld")

;; ok, LMultOldSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x(3*n+3)u^ -> 
;;  allnc u^0(LMR y(3*n+3)u^0 -> LMR(x*y)n(cLMultOld n u^ u^0)))

;; with computation rule

;; cLMultOld eqd
;; ([n,u,u0]
;;   [let wtuv
;;     (cLMultToMultc(n+n+n)u u0)
;;     (cLMultcToL n
;;     (cLToLPred(n+n+n)(cLSuccToL(n+n+n)(cLSuccToL(Succ(n+n+n))clft wtuv)))
;;     clft crht wtuv
;;     (cLSuccToL(n+n+n)(cLSuccToL(Succ(n+n+n))clft crht crht wtuv))
;;     crht crht crht wtuv)])

(deanimate "LMultOld")

;; LNegToLPlusOne
(set-goal "all n allnc x(L x n -> x<<=0 -> L(x+1)n)")
(ind)
(assume "x" "Lx1" "xBd")
(intro 0)
(autoreal)
(use "RealLeAbs")
(use "RealLeTrans" (pt "RealPlus 0 1"))
(use "RealLeMonPlus")
(autoreal)
(use "xBd")
(ng #t)
(use "RealLeRefl")
(autoreal)
(simpreal "RealUMinusPlus")
(use "RealLeTrans" (pt "RealPlus 2 ~1"))
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "RealConstr([n](1#1))([p]Zero)"))
(use "RealLeTrans" (pt "abs x"))
(simpreal "<-" "RealAbsUMinus")
(use "RealLeIdAbs")
(autoreal)
(use "LToBd" (pt "Zero"))
(use "Lx1")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeRefl")
(autoreal)
(ng #t)
(use "RealLeRefl")
(autoreal)
(assume "n" "IH" "x" "LxSn" "xBd")
(inst-with-to "LClosure" (pt "x") (pt "n") "LxSn" "LClosureInst")
(by-assume "LClosureInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(elim "dx1Prop")
(drop "dx1Prop")
(assume "Sdd" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume "xDef")
(assume "Lx1")
(assert "x===(1#2)*(x1+d)")
(use "xDef")
(drop "xDef")
(assert "abs x1<<=1")
 (use "LToBd" (pt "n"))
 (use "Lx1")
(assume "x1Bd")
(assert "Real x1")
(use "LToReal" (pt "n"))
(use "Lx1")
(assume "Rx1")
(assert "Real x")
(use "LToReal" (pt "n+1"))
(use "LxSn")
(assume "Rx")
(elim "Sdd")
;; 30-32
;; Case d=1
(assume "yDef")
(intro 1 (pt "IntP 1") (pt "RealPlus 1 0"))
(intro 0)
(use "LOne")
(assert "x1=== ~1")
(use "RealLeAntiSym")
;; 53,54
;; ?_53:x1<<= ~1
(use "RealLeTrans" (pt "x1+1+ ~1"))
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(use "RealLeTrans" (pt "RealPlus 0 ~1"))
(use "RealLeMonPlus")
(autoreal)
(use "RealLeTrans" (pt "2*((1#2)*(x1+1))"))
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
(use "RealLeTrans" (pt "RealTimes 2 0"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "<-" "yDef")
(use "xBd")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
;; ?^54:~1<<=x1
(use "RealLeTrans" (pt "~abs x1"))
(use "RealLeTrans" (pt "~(RealPlus 0 1)"))
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeUMinus")
(use "x1Bd")
(use "RealLeTrans" (pt "~ ~x1"))
(use "RealLeUMinus")
(simpreal "<-" "RealAbsUMinus")
(use "RealLeIdAbs")
(autoreal)
(simpreal "RealUMinusUMinus")
(use "RealLeRefl")
(autoreal)
;; Assertion proved.
(assume "x1=-1")
(simpreal "yDef")
(simpreal "x1=-1")
(use "RatEqvToRealEq")
(use "Truth")
;; 31
;; Case d=0
(assume "yDef")
(intro 1 (pt "IntP 1") (pt "2*x+1"))
(intro 0)
(use "IH")
(use "LCompat" (pt "2*((1#2)*(x1+0))"))
(simpreal "<-" "yDef")
(use "RealEqRefl")
(autoreal)
(use "LCompat" (pt "x1"))
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
(use "Lx1")
(use "RealLeTrans" (pt "RealTimes 2 0"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "xBd")
(ng #t)
(use "RealLeRefl")
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(assume "yDef")
(intro 1 (pt "IntP 1") (pt "x1"))
(intro 0)
(use "Lx1")
(simpreal "yDef")
(simpreal "RealTimesPlusDistr")
(ng #t)
(simpreal "RealTimesPlusDistr")
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LNegToLPlusOne")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [n]
;;  (Rec nat=>al=>al)n([u]U)
;;  ([n0,(al=>al),u]
;;    [case u
;;      (U -> C SdR(cLOne n0))
;;      (C s u0 -> 
;;      [case s
;;        (SdR -> C SdR(cLOne n0))
;;        (SdM -> C SdR((al=>al)u0))
;;        (SdL -> C SdR u0)])])

(add-sound "LNegToLPlusOne")

;; ok, LNegToLPlusOneSound has been added as a new theorem:

;; allnc n,x,u^(LMR x n u^ -> x<<=0 -> LMR(x+1)n(cLNegToLPlusOne n u^))

;; with computation rule

;; cLNegToLPlusOne eqd
;; ([n]
;;   (Rec nat=>al=>al)n([u]U)
;;   ([n0,(al=>al),u]
;;     [if (cLClosure u)
;;       ([s,u0][if s (C SdR(cLOne n0)) (C SdR((al=>al)u0)) (C SdR u0)])]))

(deanimate "LNegToLPlusOne")

;; LPosToLMinusOne
(set-goal "all n allnc x(L x n -> 0<<=x -> L(x+ ~1)n)")
(ind)
(assume "x" "Lx1" "xBd")
(intro 0)
(autoreal)
(use "RealLeAbs")
(use "RealLeTrans" (pt "RealPlus 2 ~1"))
(use "RealLeMonPlus")
(autoreal)
(use "RealLeTrans" (pt "abs x"))
(use "RealLeIdAbs")
(autoreal)
(use "RealLeTrans" (pt "RealPlus 0 1"))
(use "LToBd" (pt "Zero"))
(use "Lx1")
(use "RatLeToRealLe")
(use "Truth")
(ng #t)
(use "RealLeRefl")
(autoreal)
(simpreal "RealUMinusPlus")
(ng #t)
(use "RealLeTrans" (pt "RealPlus 0 1"))
(use "RealLeMonPlusTwo")
(use "RealLeUMinusInv")
(simpreal "RealUMinusUMinus")
(use "xBd")
(autoreal)
(use "RealLeRefl")
(autoreal)
(use "RealLeRefl")
(autoreal)
(assume "n" "IH" "x" "LxSn" "xBd")
(inst-with-to "LClosure" (pt "x") (pt "n") "LxSn" "LClosureInst")
(by-assume "LClosureInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(elim "dx1Prop")
(drop "dx1Prop")
(assume "Sdd" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume "xDef")
(assume "Lx1")
(assert "x===(1#2)*(x1+d)")
(use "xDef")
(drop "xDef")
(assert "abs x1<<=1")
 (use "LToBd" (pt "n"))
 (use "Lx1")
(assume "x1Bd")
(assert "Real x1")
(use "LToReal" (pt "n"))
(use "Lx1")
(assume "Rx1")
(assert "Real x")
(use "LToReal" (pt "n+1"))
(use "LxSn")
(assume "Rx")
(elim "Sdd")
;; Case d=1
(assume "yDef")
(intro 1 (pt "IntN 1") (pt "x1"))
(use "InitSdSdL")
(use "Lx1")
(simpreal "yDef")
(simpreal "RealTimesPlusDistr")
(ng #t)
(simpreal "RealTimesPlusDistr")
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Case d=0
(assume "yDef")
(intro 1 (pt "IntN 1") (pt "2*x+ ~1"))
(use "InitSdSdL")
(use "IH")
(use "LCompat" (pt "2*((1#2)*(x1+0))"))
(simpreal "<-" "yDef")
(use "RealEqRefl")
(autoreal)
(use "LCompat" (pt "x1"))
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
(use "Lx1")
(use "RealLeTrans" (pt "RealTimes 2 0"))
(use "RealLeRefl")
(use "RealRat")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "xBd")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(assume "yDef")
(intro 1 (pt "IntN 1") (pt "RealPlus ~1 0 "))
(use "InitSdSdL")
(use "LIntNOne")
(assert "x1===1")
(use "RealLeAntiSym")
(use "RealLeTrans" (pt "abs x1"))
(use "RealLeIdAbs")
(autoreal)
(use "x1Bd")
(use "RealLePlusCancelR" (pt "RealPlus (IntN 1) 0"))
(autoreal)
(ng #t)
(use "RealLeTimesCancelL" (pt "RealPlus (1#2) 0") (pt "1"))
(autoreal)
(ng #t)
(use "Truth")
(ng #t)
(simpreal "<-" "yDef")
(use "xBd")
(assume "x1=1")
(simpreal "yDef")
(simpreal "x1=1")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LPosToLMinusOne")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [n]
;;  (Rec nat=>al=>al)n([u]U)
;;  ([n0,(al=>al),u]
;;    [case (cLClosure u)
;;      (s pair u0 -> 
;;      [case s
;;        (SdR -> C SdL u0)
;;        (SdM -> C SdL((al=>al)u0))
;;        (SdL -> C SdL(cLIntNOne n0))])])

(add-sound "LPosToLMinusOne")

;; ok, LPosToLMinusOneSound has been added as a new theorem:

;; allnc n,x,u^(LMR x n u^ -> 0<<=x -> LMR(x+ ~1)n(cLPosToLMinusOne n u^))

;; with computation rule

;; cLPosToLMinusOne eqd
;; ([n]
;;   (Rec nat=>al=>al)n([u]U)
;;   ([n0,(al=>al),u]
;;     [if (cLClosure u)
;;       ([s,u0][if s (C SdL u0) (C SdL((al=>al)u0)) (C SdL(cLIntNOne n0))])]))

(deanimate "LPosToLMinusOne")

(set! COMMENT-FLAG #f)
(load "~/git/minlog/examples/analysis/div.scm")
(set! COMMENT-FLAG #t)

;; LToLDouble
(set-goal "allnc x all n(L x(n+1) -> abs x<<=(1#2) -> L(2*x)n)")
(assume "x" "n" "Lx" "LeHyp")
(inst-with-to "LClosure" (pt "x") (pt "n") "Lx" "LClosureInst")
(by-assume "LClosureInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(elim "dx1Prop")
(drop "dx1Prop")
(assume "Sdd" "Conj")
(elim "Conj")
(drop "Conj")
(assume "Eq" "Lx1")
(assert "abs x1<<=1")
 (use "LToBd" (pt "n"))
 (use "Lx1")
(assume "x1Bd")
(assert "x===(1#2)*(x1+d)")
(use "Eq")
(drop "Eq")
(assert "Real x")
(use "LToReal" (pt "n+1"))
(use "Lx")
(assume "Rx")
(assert "Real x1")
(use "LToReal" (pt "n"))
(use "Lx1")
(assume "Rx1")
(elim "Sdd")
;; Case d=1
(assume "xDef")
(use "LCompat" (pt "x1+1"))
(simpreal "xDef")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "LNegToLPlusOne")
(use "Lx1")
(use "RealLeTrans" (pt "2*((1#2)*(x1+1+ ~1))"))
(simpreal "RealTimesAssoc")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealPlusZero")
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
(simpreal "RealTimesPlusDistr")
(simpreal "<-" "xDef")
(simpreal "RealTimesPlusDistr")
(ng #t)
(use "RealLeTrans" (pt "RealPlus 1 ~1"))
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "RealTimes 2 abs x"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeIdAbs")
(autoreal)
(use "RealLeTrans" (pt "RealTimes 2(1#2)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "LeHyp")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; Case d=0
(assume "xDef")
(assert "2*x===x1")
 (simpreal "xDef")
 (simpreal "RealTimesAssoc")
 (ng #t)
 (simpreal "RealOneTimes")
 (simpreal "RealPlusZero")
 (use "RealEqRefl")
 (autoreal)
(assume "2x=x1")
(use "LCompat" (pt "x1"))
(simpreal "2x=x1")
(use "RealEqRefl")
(autoreal)
(use "Lx1")
;; Case d= ~1
(assume "xDef")
(use "LCompat" (pt "x1+IntN 1"))
(simpreal "xDef")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "LPosToLMinusOne")
(use "Lx1")
(use "RealLeTrans" (pt "2*((1#2)*(x1+IntN 1 + 1))"))
(simpreal "RealTimesPlusDistr")
(simpreal "<-" "xDef")
(ng #t)
(simpreal "RealTimesPlusDistr")
(use "RealLeTrans" (pt "RealPlus ~1 1"))
(use "RealLeRefl")
(autoreal)
(use "RealLeMonPlusTwo")
(use "RealLeUMinusInv")
(ng #t)
(use "RealLeTrans" (pt "abs ~(2*x)"))
(use "RealLeIdAbs")
(autoreal)
(simpreal "RealAbsUMinus")
(simpreal "RealAbsTimes")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 2 (1#2)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "LeHyp")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(simpreal "RealTimesAssoc")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealOneTimes")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LToLDouble")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [n,u]
;;  [case (cLClosure u)
;;    (s pair u0 -> 
;;    [case s
;;      (SdR -> cLNegToLPlusOne n u0)
;;      (SdM -> u0)
;;      (SdL -> cLPosToLMinusOne n u0)])]

(add-sound "LToLDouble")

;; ok, LToLDoubleSound has been added as a new theorem:

;; allnc x,n,u^(LMR x(n+1)u^ -> abs x<<=(1#2) -> LMR(2*x)n(cLToLDouble n u^))

;; with computation rule

;; cLToLDouble eqd
;; ([n,u]
;;   [if (cLClosure u)
;;     ([s,u0][if s (cLNegToLPlusOne n u0) u0 (cLPosToLMinusOne n u0)])])

(deanimate "LToLDouble")

;; LToLQuad
(set-goal "allnc x all n(L x(n+2) -> abs x<<=(1#4) -> L(4*x)n)")
(assume "x" "n" "Lx" "LeHyp")
(assert "Real x")
(use "LToReal" (pt "n+2"))
(use "Lx")
(assume "Rx")
(assert "4*x===2*(2*x)")
(simpreal "RealTimesAssoc")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Assertion proved
(assume "EqHyp")
(use "LCompat" (pt "2*(2*x)"))
(use "RealEqSym")
(use "EqHyp")
(use "LToLDouble")
(use "LToLDouble")
(use "Lx")
(use "RealLeTrans" (pt "RealPlus 0(1#4)"))
(ng #t)
(use "LeHyp")
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
(simpreal "RealAbsTimes")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 2(1#4)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "LeHyp")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LToLQuad")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,u]cLToLDouble n(cLToLDouble(Succ n)u)

(add-sound "LToLQuad")

;; ok, LToLQuadSound has been added as a new theorem:

;; allnc x,n,u^(LMR x(n+2)u^ -> abs x<<=(1#4) -> LMR(4*x)n(cLToLQuad n u^))

;; with computation rule

;; cLToLQuad eqd([n,u]cLToLDouble n(cLToLDouble(Succ n)u))

(deanimate "LToLQuad")

;; LDivSatLClAuxR
(set-goal
 "allnc x,y all n(L x(n+3) -> L y(n+2) -> (1#4)<<=y -> abs x<<=y -> 0<<=x -> 
 L(4*((1#2)*(x+ ~((1#2)*y))))n)")
(assume "x" "y" "n" "Lx" "Ly" "yLBd" "xBd" "0<<=x")
(use "LToLQuad")
(use "LAverage")
(use "Lx")
(use "LUMinus")
(intro 1 (pt "0") (pt "y"))
(intro 1)
(use "Ly")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
;; ?_4:abs((1#2)*(x+ ~((1#2)*y)))<<=(1#4)
(simpreal (pf "((1#2)*(x+ ~((1#2)*y)))===(1#4)*(4*((1#2)*(x+ ~((1#2)*y))))"))
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "abs(1#4)*y"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "DivAuxBdR")
(use "0<<=x")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeIdAbs")
(autoreal)
(use "xBd")
(ng #t)
(use "RealLeTrans" (pt "RealTimes(1#4)1"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeTrans" (pt "abs y"))
(use "RealLeIdAbs")
(autoreal)
(use "LToBd" (pt "n+2"))
(use "Ly")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; ?_18:(1#2)*(x+ ~((1#2)*y))===(1#4)*(4*((1#2)*(x+ ~((1#2)*y))))
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LDivSatLClAuxR")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n,u,u0]cIToIQuad n(cIAverage(Succ(Succ n))u(cIUMinus(C SdM u0)))

(add-sound "LDivSatLClAuxR")

;; ok, LDivSatLClAuxRSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x(n+3)u^ -> 
;;  allnc u^0(
;;   LMR y(n+2)u^0 -> 
;;   (1#4)<<=y -> 
;;   abs x<<=y -> 
;;   0<<=x -> LMR(4*((1#2)*(x+ ~((1#2)*y))))n(cLDivSatLClAuxR n u^ u^0)))

;; with computation rule

;; cLDivSatLClAuxR eqd
;; ([n,u,u0]cLToLQuad n(cLAverage(Succ(Succ n))u(cLUMinus(C SdM u0))))

(deanimate "LDivSatLClAuxR")

;; LDivSatLClAuxL
(set-goal
 "allnc x,y all n(L x(n+3) -> L y(n+2) -> (1#4)<<=y -> abs x<<=y -> x<<=0 -> 
 L(4*((1#2)*(x+(1#2)*y)))n)")
(assume "x" "y" "n" "Lx" "Ly" "yLBd" "xBd" "x<<=0")
(use "LToLQuad")
(use "LAverage")
(use "Lx")
(intro 1 (pt "0") (pt "y"))
(intro 1)
(use "Ly")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
;; ?_4:abs((1#2)*(x+(1#2)*y))<<=(1#4)
(simpreal (pf "((1#2)*(x+(1#2)*y))===(1#4)*(4*((1#2)*(x+(1#2)*y)))"))
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "abs(1#4)*y"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "DivAuxBdL")
(use "x<<=0")
(use "xBd")
;; ?^20:abs(1#4)*y<<=(1#4)
(ng #t)
(use "RealLeTrans" (pt "RealTimes(1#4) 1"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeTrans" (pt "abs y"))
(use "RealLeIdAbs")
(autoreal)
(use "LToBd" (pt "n+2"))
(use "Ly")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; ?^15:(1#2)*(x+(1#2)*y)===(1#4)*(4*((1#2)*(x+(1#2)*y)))
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LDivSatLClAuxL")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n,u,u0]cIToIQuad n(cIAverage(Succ(Succ n))u(C SdM u0))

(add-sound "LDivSatLClAuxL")

;; ok, LDivSatLClAuxLSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x(n+3)u^ -> 
;;  allnc u^0(
;;   LMR y(n+2)u^0 -> 
;;   (1#4)<<=y -> 
;;   abs x<<=y -> 
;;   x<<=0 -> LMR(4*((1#2)*(x+(1#2)*y)))n(cLDivSatLClAuxL n u^ u^0)))

;; with computation rule

;; cLDivSatLClAuxL eqd([n,u,u0]cLToLQuad n(cLAverage(Succ(Succ n))u(C SdM u0)))

(deanimate "LDivSatLClAuxL")

;; LDivSatLCl
(set-goal "allnc x,y all n(L x(n+3) -> L y(n+2) -> (1#4)<<=y -> abs x<<=y ->
 exr d0,x0(Sd d0 andi L x0 n andi abs x0<<=y andi
 x*RealUDiv y 3===(1#2)*(x0*RealUDiv y 3+d0)))")
(assume "x" "y" "n" "Lx" "Ly" "yLBd" "xBd")
;; Let d1,d2,d3 be the first three digits of x.
;; We first distinguish cases on the most significant digit d1
(inst-with-to "LClosure" (pt "x") (pt "n+2") "Lx" "LClosureInst1")
(by-assume "LClosureInst1" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(assert "Real x1")
(use "LToReal" (pt "n+2"))
(use "d1x1Prop")
(assume "Rx1")
(elim "d1x1Prop")
(assume "Sdd1")
(elim "Sdd1")
;; 17-19
;; Case d1=1
(assume "Conj11")
(elim "Conj11")
(assume "Eq1" "Lx1")
(assert "abs x1<<=1")
 (use "LToBd" (pt "n+2"))
 (use "Lx1")
(assume "x1Bd")
(drop "d1x1Prop" "Conj11")
;; Next we show 0<<=x from x===(1#2)*(x1+1) using x1Bd
(assert "0<<=x")
(simpreal "Eq1")
(use "RealLeTrans" (pt "(1#2)*(RealUMinus 1+1)"))
(ng)
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeAbsInv")
(autoreal)
(use "x1Bd")
(assume "0<<=x")
;; Now we define d and x0
(intro 0 (pt "IntP 1"))
(intro 0 (pt "4*((1#2)*(x+ ~((1#2)*y)))"))
(split)
(use "InitSdSdR")
(split)
(use "LDivSatLClAuxR")
(use "Lx")
(use "Ly")
(use "yLBd")
(use "xBd")
(use "0<<=x")
;; ?^48:abs(4*((1#2)*(x+ ~((1#2)*y))))<<=y andnc 
;;      x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(split)
(use "DivAuxBdR")
(use "0<<=x")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeIdAbs")
(autoreal)
(use "xBd")
;; ?^55:x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(use "DivAuxEqR")
(autoreal)
(use "yLBd")
;; 18
;; Case d1=0.
(assume "Conj11")
(elim "Conj11")
(assume  "Eq1" "Lx1")
(assert "abs x1<<=1")
 (use "LToBd" (pt "n+2"))
 (use "Lx1")
(assume "x1Bd")
(drop "d1x1Prop" "Conj11")
(inst-with-to "LClosure" (pt "x1") (pt "n+1") "Lx1" "LClosureInst2")
(by-assume "LClosureInst2" "d2" "d2Prop")
(by-assume "d2Prop" "x2" "d2x2Prop")
(assert "Real x2")
(use "LToReal" (pt "n+1"))
(use "d2x2Prop")
(assume "Rx2")
(elim "d2x2Prop")
(assume "Sdd2")
;; We now distinguish cases on d2
(elim "Sdd2")
;; 86-88
;; Case d1=0, d2=1
(assume "Conj21")
(elim "Conj21")
(assume  "Eq2" "Lx2")
(assert "abs x2<<=1")
 (use "LToBd" (pt "n+1"))
 (use "Lx2")
(assume "x2Bd")
(drop "d2x2Prop" "Conj21")
;; Next we show 0<<=x from x===(1#2)*(x1+0) and x1===(1#2)*(x2+1)
(assert "0<<=x")
(simpreal "Eq1")
(simpreal "Eq2")
(use "RealLeTrans" (pt "(1#2)*((1#2)*(RealUMinus 1+1)+0)"))
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeAbsInv")
(autoreal)
(use "x2Bd")
(assume "0<<=x")
;; Now we define d and x0
(intro 0 (pt "IntP 1"))
(intro 0 (pt "4*((1#2)*(x+ ~((1#2)*y)))"))
(split)
(use "InitSdSdR")
(split)
(use "LDivSatLClAuxR")
(use "Lx")
(use "Ly")
(use "yLBd")
(use "xBd")
(use "0<<=x")
;; ?^123:abs(4*((1#2)*(x+ ~((1#2)*y))))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(split)
(use "DivAuxBdR")
(use "0<<=x")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeIdAbs")
(autoreal)
(use "xBd")
;; ?^130:x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(use "DivAuxEqR")
(autoreal)
(use "yLBd")
;; 87
;; Case d1=0, d2=0
(assume "Conj21")
(elim "Conj21")
(assume "Eq2" "Lx2")
(assert "abs x2<<=1")
 (use "LToBd" (pt "n+1"))
 (use "Lx2")
(assume "x2Bd")
(drop "d2x2Prop" "Conj21")
(inst-with-to "LClosure" (pt "x2") (pt "n") "Lx2" "LClosureInst3")
(by-assume "LClosureInst3" "d3" "d3Prop")
(by-assume "d3Prop" "x3" "d3x3Prop")
(assert "Real x3")
(use "LToReal" (pt "n"))
(use "d3x3Prop")
(assume "Rx3")
(elim "d3x3Prop")
(assume "Sdd3")
;; We now distinguish cases on d3
(elim "Sdd3")
;; 161-163
;; Case d1=0, d2=0, d3=1
(assume "Conj31")
(elim "Conj31")
(assume  "Eq3" "Lx3")
(assert "abs x3<<=1")
 (use "LToBd" (pt "n"))
 (use "Lx3")
(assume "x3Bd")
(drop "d3x3Prop" "Conj31")
;; Next we show 0<<=x from x===(1#2)*(x1+0) x1===(1#2)*(x2+0) x2===(1#2)*(x3+1)
(assert "0<<=x")
(simpreal "Eq1")
(simpreal "Eq2")
(simpreal "Eq3")
(use "RealLeTrans" (pt "(1#2)*((1#2)*((1#2)*(RealUMinus 1+1)+0)+0)"))
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeAbsInv")
(autoreal)
(use "x3Bd")
(assume "0<<=x")
;; Now we define d and x0
(intro 0 (pt "IntP 1"))
(intro 0 (pt "4*((1#2)*(x+ ~((1#2)*y)))"))
(split)
(use "InitSdSdR")
(split)
(use "LDivSatLClAuxR")
(use "Lx")
(use "Ly")
(use "yLBd")
(use "xBd")
(use "0<<=x")
;; ?^204:abs(4*((1#2)*(x+ ~((1#2)*y))))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(split)
(use "DivAuxBdR")
(use "0<<=x")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeIdAbs")
(autoreal)
(use "xBd")
;; ?^211:x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(use "DivAuxEqR")
(autoreal)
(use "yLBd")
;; Case d1=0, d2=0, d3=0
(assume "Conj31")
(elim "Conj31")
(assume "Eq3" "Lx3")
(assert "abs x3<<=1")
(use "LToBd" (pt "n"))
(use "Lx3")
(assume "x3Bd")
(drop "d3x3Prop" "Conj31")
;; We can now pick d=0 and x0 as 2*x
(intro 0 (pt "0"))
(intro 0 (pt "2*x"))
(split)
(use "InitSdSdM")
(split)
(use "LToLDouble")
(use "LSuccToL")
(use "LSuccToL")
(use "Lx")
(simpreal "Eq1")
(simpreal "RealPlusZero")
(simpreal "RealAbsTimes")
(ng #t)
(use "RealLeTrans" (pt "RealTimes(1#2)1"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "x1Bd")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; ?^233:abs(2*x)<<=y andnc x*RealUDiv y 3===(1#2)*(2*x*RealUDiv y 3+0)
(split)
(simpreal "RealAbsTimes")
(ng #t)
(simpreal "Eq1")
(simpreal "RealPlusZero")
(simpreal "RealAbsTimes")
(ng #t)
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(simpreal "Eq2")
(simpreal "RealPlusZero")
(simpreal "RealAbsTimes")
(ng #t)
(simpreal "Eq3")
(simpreal "RealPlusZero")
(simpreal "RealAbsTimes")
(ng #t)
(simpreal "RealTimesAssoc")
(ng #t)
(use "RealLeTrans" (pt "RealTimes(1#4)1"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "x3Bd")
(use "yLBd")
(autoreal)
;; ?^252:x*RealUDiv y 3===(1#2)*(2*x*RealUDiv y 3+0)
(assert "Real(RealUDiv y 3)")
 (use "RealUDivReal")
 (autoreal)
 (simp (pf "3=PosS 2"))
 (use "RealLeToPos")
 (use "RealLeTrans" (pt "y")) 
 (use "yLBd")
 (use "RealLeIdAbs")
 (autoreal)
 (use "Truth")
(assume "R1/y")
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
;; 163
;; Case d1=0, d2=0, d3=IntN 1
(assume "Conj31")
(elim "Conj31")
(assume "Eq3" "Lx3")
(assert "abs x3<<=1")
(use "LToBd" (pt "n"))
(use "Lx3")
(assume "x3Bd")
(drop "d3x3Prop" "Conj31")
;; Show x<<=0 from x===(1#2)*(x1+0) x1===(1#2)*(x2+0) x2===(1#2)*(x3+IntN 1)
(assert "x<<=0")
(simpreal "Eq1")
(simpreal "Eq2")
(simpreal "Eq3")
(simpreal "RealPlusZero")
(simpreal "RealPlusZero")
(use "RealLeTrans" (pt "(1#2)*((1#2)*((1#2)*(RealPlus 1 IntN 1)))"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeTrans" (pt "abs x3"))
(use "RealLeIdAbs")
(autoreal)
(use "x3Bd")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(assume "x<<=0")
;; Now we define d and x0
(intro 0 (pt "IntN 1"))
(intro 0 (pt "4*((1#2)*(x+(1#2)*y))"))
(split)
(use "InitSdSdL")
(split)
(use "LDivSatLClAuxL")
(use "Lx")
(use "Ly")
(use "yLBd")
(use "xBd")
(use "x<<=0")
;; ?^360:abs(4*((1#2)*(x+(1#2)*y)))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+(1#2)*y))*RealUDiv y 3+IntN 1)
(split)
(use "DivAuxBdL")
(use "x<<=0")
(use "xBd")
(use "DivAuxEqL")
(autoreal)
(use "yLBd")
;; 88
;; Case d1=0, d2=IntN 1
(assume "Conj21")
(elim "Conj21")
(assume "Eq2" "Lx2")
(assert "abs x2<<=1")
(use "LToBd" (pt "n+1"))
(use "Lx2")
(assume "x2Bd")
(drop "d2x2Prop" "Conj21")
;; Next we show x<<=0 from x===(1#2)*(x1+0) and x1===(1#2)*(x2+IntN 1)
(assert "x<<=0")
(simpreal "Eq1")
(simpreal "Eq2")
(simpreal "RealPlusZero")
(use "RealLeTrans" (pt "(1#2)*((1#2)*(RealPlus 1 IntN 1))"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeTrans" (pt "abs x2"))
(use "RealLeIdAbs")
(autoreal)
(use "x2Bd")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(assume "x<<=0")
;; Now we define d and x0
(intro 0 (pt "IntN 1"))
(intro 0 (pt "4*((1#2)*(x+(1#2)*y))"))
(split)
(use "InitSdSdL")
(split)
(use "LDivSatLClAuxL")
(use "Lx")
(use "Ly")
(use "yLBd")
(use "xBd")
(use "x<<=0")
;; ?^407:abs(4*((1#2)*(x+(1#2)*y)))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+(1#2)*y))*RealUDiv y 3+IntN 1)
(split)
(use "DivAuxBdL")
(use "x<<=0")
(use "xBd")
(use "DivAuxEqL")
(autoreal)
(use "yLBd")
;; 19
;; Case d1=IntN 1
(assume "Conj11")
(elim "Conj11")
(assume "Eq1" "Lx1")
(assert "abs x1<<=1")
(use "LToBd" (pt "n+2"))
(use "Lx1")
(assume "x1Bd")
(drop "d1x1Prop" "Conj11")
;; Next we show x<<=0 from x===(1#2)*(x1+IntN 1) using x1Bd
(assert "x<<=0")
(simpreal "Eq1")
(use "RealLeTrans" (pt "(1#2)*(RealPlus 1 IntN 1)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(autoreal)
(use "RealLeTrans" (pt "abs x1"))
(use "RealLeIdAbs")
(autoreal)
(use "x1Bd")
(use "RatLeToRealLe")
(use "Truth")
(assume "x<<=0")
(intro 0 (pt "IntN 1"))
(intro 0 (pt "4*((1#2)*(x+(1#2)*y))"))
(split)
(use "InitSdSdL")
(split)
(use "LDivSatLClAuxL")
(use "Lx")
(use "Ly")
(use "yLBd")
(use "xBd")
(use "x<<=0")
;; ?^448:abs(4*((1#2)*(x+(1#2)*y)))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+(1#2)*y))*RealUDiv y 3+IntN 1)
(split)
(use "DivAuxBdL")
(use "x<<=0")
(use "xBd")
;; ?^455:x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+(1#2)*y))*RealUDiv y 3+IntN 1)
(use "DivAuxEqL")
(autoreal)
(use "yLBd")
;; Proof finished.
;; (cdp)
(save "LDivSatLCl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [n,u,u0]
;;  [case (cLClosure u)
;;    (s pair u1 -> 
;;    [case s
;;      (SdR -> SdR pair cLDivSatLClAuxR n u u0)
;;      (SdM -> 
;;      [case (cLClosure u1)
;;        (s0 pair u2 -> 
;;        [case s0
;;          (SdR -> SdR pair cLDivSatLClAuxR n u u0)
;;          (SdM -> 
;;          [case (cLClosure u2)
;;            (s1 pair u3 -> 
;;            [case s1
;;              (SdR -> SdR pair cLDivSatLClAuxR n u u0)
;;              (SdM -> 
;;              SdM pair 
;;              cLToLDouble n(cLSuccToL(Succ n)(cLSuccToL(Succ(Succ n))u)))
;;              (SdL -> SdL pair cLDivSatLClAuxL n u u0)])])
;;          (SdL -> SdL pair cLDivSatLClAuxL n u u0)])])
;;      (SdL -> SdL pair cLDivSatLClAuxL n u u0)])]

(add-sound "LDivSatLCl")

;; ok, LDivSatLClSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x(n+3)u^ -> 
;;  allnc u^0(
;;   LMR y(n+2)u^0 -> 
;;   (1#4)<<=y -> 
;;   abs x<<=y -> 
;;   (ExRTMR int
;;     sd yprod al
;;     (cterm (d,su^) 
;;     (ExRTMR rea
;;       sd yprod al
;;       (cterm (x0,su^0) 
;;       (AndDMR (cterm (s^) SdMR d s^)
;;         (cterm (u^1) 
;;         (AndLMR (cterm (u^2) LMR x0 n u^2)
;;           (cterm () 
;;           abs x0<<=y andnc x*RealUDiv y 3===(1#2)*(x0*RealUDiv y 3+d)))
;;         u^1))
;;       su^0))
;;     su^))
;;   (cLDivSatLCl n u^ u^0)))

;; with computation rule

;; cLDivSatLCl eqd
;; ([n,u,u0]
;;   [if (cLClosure u)
;;     ([s,u1]
;;      [if s
;;        (SdR pair cLDivSatLClAuxR n u u0)
;;        [if (cLClosure u1)
;;         ([s0,u2]
;;          [if s0
;;            (SdR pair cLDivSatLClAuxR n u u0)
;;            [if (cLClosure u2)
;;             ([s1,u3]
;;              [if s1
;;                (SdR pair cLDivSatLClAuxR n u u0)
;;                (SdM pair 
;;                cLToLDouble n(cLSuccToL(Succ n)(cLSuccToL(Succ(Succ n))u)))
;;                (SdL pair cLDivSatLClAuxL n u u0)])]
;;            (SdL pair cLDivSatLClAuxL n u u0)])]
;;        (SdL pair cLDivSatLClAuxL n u u0)])])

(deanimate "LDivSatLCl")

;; LDivAux
(set-goal "all n allnc x,y(L y(3*n--1) -> (1#4)<<=y -> abs x<<=y -> L x(3*n) ->
 L(x*RealUDiv y 3)n)")
(ind)
(assume "x" "y" "Ly" "yLBd" "xBd" "Lx")
(assert "Real x")
(use "LToReal" (pt "Zero"))
(use "Lx")
(assume "Rx")
(assert "Real y")
(use "LToReal" (pt "Zero"))
(use "Ly")
(assume "Ry")
(assert "RealPos y 3")
(simp (pf "3=PosS 2"))
(use "RealLeToPos")
(use "yLBd")
(use "Truth")
(assume "0<y")
(assert "Real(RealUDiv y 3)")
(use "RealUDivReal")
(realproof)
(simp (pf "3=PosS 2"))
(use "RealLeToPos")
(use "RealLeTrans" (pt "y")) 
(use "yLBd")
(use "RealLeIdAbs")
(autoreal)
(use "Truth")
(assume "R1/y")
(intro 0)
(autoreal)
(simpreal "RealAbsTimes")
(simpreal "<-" (pf "y*RealUDiv y 3===1"))
(simpreal "RealAbsUDiv")
(simpreal (pf "RealUDiv abs y 3===RealUDiv y 3"))
(use "RealLeMonTimes")
(use "RealPosToZeroLeUDiv")
(autoreal)
(use "0<y")
(use "xBd")
;; ?^41:RealUDiv abs y 3===RealUDiv y 3
(use "RealUDivCompat")
(use "RealEqAbsId")
(use "RealLeTrans" (pt "RealPlus(1#4)0"))
(use "RatLeToRealLe")
(use "Truth")
(use "yLBd")
(use "RealPosToPosAbs")
(use "RealPosToPosAbs")
(use "0<y")
(use "RealPosToPosAbs")
(use "0<y")
(use "0<y")
(autoreal)
(use "RealTimesUDivR")
(autoreal)
(use "0<y")
(use "R1/y")
(autoreal)
(assume "n" "LH" "x" "y" "Ly" "yLBd" "xBd" "Lx")
(assert "L y(3*n+2)")
(use "Ly")
(assume "LyII")
(assert "L x(3*n+3)")
(use "Lx")
(assume "LxII")
(inst-with-to "LDivSatLCl"
	      (pt "x") (pt "y") (pt "3*n") "LxII" "LyII" "yLBd" "xBd"
	      "LDivLnst")
(by-assume "LDivLnst" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(elim "dx2Prop")
(assume "Sdd")
(elim)
(assume "Lx2" "x2Props")
(drop "dx2Prop")
(intro 1 (pt "d") (pt "x2*RealUDiv y 3"))
(use "Sdd")
(use "LH")
(use "LToLPred")
(use "LSuccToL")
(use "LSuccToL")
(use "Ly")
(use "yLBd")
(use "x2Props")
(use "Lx2")
(use "x2Props")
;; Proof finished.
;; (cdp)
(save "LDivAux")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n]
;;  (Rec nat=>al=>al=>al)n([u,u0]U)
;;  ([n0,(al=>al=>al),u,u0]
;;    [if (cLDivSatLCl(n0+n0+n0)u0 u)
;;      ([s,u1]
;;       C s
;;       ((al=>al=>al)
;;        (cLToLPred(n0+n0+n0)(cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u)))
;;        u1))])

(add-sound "LDivAux")

;; ok, LDivAuxSound has been added as a new theorem:

;; allnc n,x,y,u^(
;;  LMR y(3*n--1)u^ -> 
;;  (1#4)<<=y -> 
;;  abs x<<=y -> 
;;  allnc u^0(LMR x(3*n)u^0 -> LMR(x*RealUDiv y 3)n(cLDivAux n u^ u^0)))

;; with computation rule

;; cLDivAux eqd
;; ([n]
;;   (Rec nat=>al=>al=>al)n([u,u0]U)
;;   ([n0,(al=>al=>al),u,u0]
;;     [if (cLDivSatLCl(n0+n0+n0)u0 u)
;;       ([s,u1]
;;        C s
;;        ((al=>al=>al)
;;         (cLToLPred(n0+n0+n0)
;;          (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u)))
;;         u1))]))

(deanimate "LDivAux")

;; LDiv
(set-goal "allnc x,y all n(L x(3*n) -> L y(3*n--1) -> (1#4)<<=y -> abs x<<=y ->
 L(x*(RealUDiv y 3))n)")
(assume "x" "y" "n" "Lx" "Ly" "(1#4)<<=y" "xBd")
(use "LDivAux" (pt "y"))
(use "Ly")
(use "(1#4)<<=y")
(use "xBd")
(use "Lx")
;; Proof finished.
;; (cdp)
(save "LDiv")

(add-sound "LDiv")

;; ok, LDivSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x(3*n)u^ -> 
;;  allnc u^0(
;;   LMR y(3*n--1)u^0 -> 
;;   (1#4)<<=y -> abs x<<=y -> LMR(x*RealUDiv y 3)n(cLDiv n u^ u^0)))

;; with computation rule

;; cLDiv eqd([n,u,u0]cLDivAux n u0 u)

(deanimate "LDiv")

(define LDiv-eterm (proof-to-extracted-term (theorem-name-to-proof "LDiv")))
;; (pp (rename-variables LDiv-eterm))
;; [n,u,u0]cIDivAux n u0 u
(animate "LDivAux")
(animate "LDivSatLCl")
(define LDiv-neterm (rename-variables (nt LDiv-eterm)))
;; (ppc LDiv-neterm)

;; [n,u,u0]
;;  (Rec nat=>al=>al=>al)n([u1,u2]U)
;;  ([n0,(al=>al=>al),u1,u2]
;;    [case (cLClosure u2)
;;      (s pair u3 -> 
;;      [case s
;;        (SdR -> 
;;        C SdR
;;        ((al=>al=>al)
;;         (cLToLPred(n0+n0+n0)
;;          (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u1)))
;;         (cLDivSatLClAuxR(n0+n0+n0)u2 u1)))
;;        (SdM -> 
;;        [case (cLClosure u3)
;;          (s0 pair u4 -> 
;;          [case s0
;;            (SdR -> 
;;            C SdR
;;            ((al=>al=>al)
;;             (cLToLPred(n0+n0+n0)
;;              (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u1)))
;;             (cLDivSatLClAuxR(n0+n0+n0)u2 u1)))
;;            (SdM -> 
;;            [case (cLClosure u4)
;;              (s1 pair u5 -> 
;;              [case s1
;;                (SdR -> 
;;                C SdR
;;                ((al=>al=>al)
;;                 (cLToLPred(n0+n0+n0)
;;                  (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u1)))
;;                 (cLDivSatLClAuxR(n0+n0+n0)u2 u1)))
;;                (SdM -> 
;;                C SdM
;;                ((al=>al=>al)
;;                 (cLToLPred(n0+n0+n0)
;;                  (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u1)))
;;                 (cLToLDouble(n0+n0+n0)
;;                  (cLSuccToL(Succ(n0+n0+n0))
;;                   (cLSuccToL(Succ(Succ(n0+n0+n0)))u2)))))
;;                (SdL -> 
;;                C SdL
;;                ((al=>al=>al)
;;                 (cLToLPred(n0+n0+n0)
;;                  (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u1)))
;;                 (cLDivSatLClAuxL(n0+n0+n0)u2 u1)))])])
;;            (SdL -> 
;;            C SdL
;;            ((al=>al=>al)
;;             (cLToLPred(n0+n0+n0)
;;              (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u1)))
;;             (cLDivSatLClAuxL(n0+n0+n0)u2 u1)))])])
;;        (SdL -> 
;;        C SdL
;;        ((al=>al=>al)
;;         (cLToLPred(n0+n0+n0)
;;          (cLSuccToL(n0+n0+n0)(cLSuccToL(Succ(n0+n0+n0))u1)))
;;         (cLDivSatLClAuxL(n0+n0+n0)u2 u1)))])])
;;  u0 
;;  u

(deanimate "LDivAux")
(deanimate "LDivSatLCl")

;; Square and Multiplication
;; =========================

;; RealBinom
(set-goal "allnc x,y(Real x -> Real y -> (x+y)*(x+y)===x*x+2*x*y+y*y)")
(assume "x" "y" "Rx" "Ry")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(simpreal (pf "2===RealPlus 1 1"))
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealOneTimes")
(simpreal "RealTimesPlusDistrLeft")
(use "RealPlusCompat")
(use "RealTimesComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealBinom")

;;GenLMinus
(set-goal "allnc d,x,y all n(Sd d -> L x(n--1) -> y===(1#2)*(x+d) -> L y n)")
(assume "d" "x" "y")
(ind)
(assume "Sdd" "Lx" "yDef")
(intro 0)
(autoreal)
(assert "Real x")
(use "LToReal" (pt "Zero"))
(use "Lx")
(assume "Rx")
(simpreal "yDef")
(simpreal "RealAbsTimes")
(use "RealLeTimesCancelL" (pt "RealPlus 2 0") (pt "1"))
(autoreal)
(use "Truth")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealLeTrans" (pt "abs x + RealAbs d"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeTrans" (pt "RealPlus 1 1"))
(use "RealLeMonPlusTwo")
(use "LToBd" (pt "Zero"))
(use "Lx")
(use "SdBoundReal")
(use "Sdd")
(use "RealLeRefl")
(autoreal)
(assume "n" "IH" "Sdd" "Lx" "yDef")
(ng)
(intro 1 (pt "d") (pt "x"))
(use "Sdd")
(use "Lx")
(use "yDef")
;; Proof finished.
;;(cdp)
(save "GenLMinus")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n,s,u][if n U ([n0]C s u)]

(add-sound "GenLMinus")

;; ok, GenLMinusSound has been added as a new theorem:

;; allnc d,x,y,n,s^(
;;  SdMR d s^ -> 
;;  allnc u^(LMR x(n--1)u^ -> y===(1#2)*(x+d) -> LMR y n(cGenLMinus n s^ u^)))

;; with computation rule

;; cGenLMinus eqd([n,s,u][if n U ([n0]C s u)])

(deanimate "GenLMinus")

;; The following decompostion will be used to compute the square:

;; LSquareAux
(set-goal "allnc x,n(
     L x(n+2) -> 
     exr y,d0,d1(
      L y n andd 
      Sd d0 andd 
      Sd d1 andl 
      x*x===
      (1#2)*
      ((1#2)*((1#2)*((1#2)*(y*y+d1*d1)+d0*d0)+d0*d1)+
       (1#2)*((1#2)*(d1*y+d0*d0)+d0*y))))")
(assume "x" "n" "Lx")
(inst-with-to "LClosure" (pt "x") (pt "n+1") "Lx" "xInst")
(by-assume "xInst" "d0" "d0Prop")
(by-assume "d0Prop" "x0" "d0x0Prop")
(elim "d0x0Prop")
(assume "Sdd0" "ConjI")
(drop "d0x0Prop")
(elim "ConjI")
(drop "ConjI")
(assume "xDef" "Lx0")
(inst-with-to "LClosure" (pt "x0") (pt "n") "Lx0" "x0Inst")
(by-assume "x0Inst" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(elim "d1x1Prop")
(assume "Sdd1" "ConjII")
(drop "d1x1Prop")
(elim "ConjII")
(drop "ConjII")
(assume "x0Def" "Lx1")
(intro 0 (pt "x1"))
(intro 0 (pt "d0"))
(intro 0 (pt "d1"))
(split)
(use "Lx1")
(split)
(use "Sdd0")
(split)
(use "Sdd1")
(assert "Real x")
(use "LToReal" (pt "n+2"))
(use "Lx")
(assume "Rx")
(assert "Real x0")
(use "LToReal" (pt "n+1"))
(use "Lx0")
(assume "Rx0")
(assert "Real x1")
(use "LToReal" (pt "n"))
(use "Lx1")
(assume "Rx1")
(simpreal "xDef")
(simpreal "x0Def")
(simpreal "<-" "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqTrans" (pt "(1#2)*((1#2)*(x1+d1)+d0)*((1#2)*(x1+d1)+d0)"))
(use "RealEqSym")
(simpreal "RealTimesAssoc")
(simpreal "RealTimesComm")
(simpreal "<-" "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(simpreal "<-" "RealTimesPlusDistr")
(use "RealEqSym")
(simpreal "<-" "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealBinom")
(simpreal "RealTimesAssoc")
(simpreal-with "RealTimesComm" (pt "(1#2)*(x1+d1)") (pt "RealConstr([n](1#2))([p]Zero)") "?" "?")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqSym")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesAssoc")
(ng #t)
(use "RealEqSym")
(simpreal "<-" "RealTimesAssoc")
(simpreal "RealBinom")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(simpreal-with "RealPlusComm" (pt "2*x1*d1") (pt "RealTimes d1 d1") "?" "?")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(simpreal "RealTimesPlusDistr")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(ng #t)
(use "RealEqRefl")
(autoreal)
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(ng #t)
(use "RealEqSym")
(simpreal "RealTimesPlusDistr")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(simpreal-with "RealPlusComm" (pt "RealPlus(d0*d0#2)(d0*d1)") (pt "(1#2)*(d1*x1)") "?" "?")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(simpreal "<-" "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(use "RealTimesComm")
(autoreal)
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(simpreal-with "RealPlusComm" (pt "RealPlus(d0*d0#2)(d0*d1)") (pt "RealTimes(1#2)(d0*d0)") "?" "?")
(simpreal "RealPlusAssoc")
(use "RealEqSym")
(simpreal "RealPlusComm")
(simpreal (pf "RealTimes(1#2)(d0*d0)+(d0*d0#2)===d0*d0"))
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealTimesComm")
(simpreal "RealPlusComm")
(simpreal "RealTimesPlusDistr")
(ng #t)
(use "RealEqRefl")
(autoreal)
(ng #t)
(use "RatEqvToRealEq")
(ng #t)
(simp "<-" "IntTimesPlusDistrLeft")
(simp (pf "d0*d0+d0*d0=d0
*d0*2"))
(simp "<-" "IntTimesAssoc")
(ng #t)
(use "Truth")
(simp (pf "d0*d0=d0*d0*1"))
(simp "<-" "IntTimesPlusDistr")
(ng #t)
(use "Truth")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LSquareAux")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [u]
;;  [case (cLClosure u)
;;    (s pair u0 -> [case (cLClosure u0) (s0 pair u1 -> u1 pair s pair s0)])]

(add-sound "LSquareAux")

;; ok, LSquareAuxSound has been added as a new theorem:

;; allnc x,n,u^(
;;  LMR x(n+2)u^ -> 
;;  (ExRTMR rea
;;    al yprod sd yprod sd
;;    (cterm (y,(al yprod sd yprod sd)^) 
;;    (ExRTMR int
;;      al yprod sd yprod sd
;;      (cterm (d,(al yprod sd yprod sd)^0) 
;;      (ExRTMR int
;;        al yprod sd yprod sd
;;        (cterm (d0,(al yprod sd yprod sd)^1) 
;;        (AndDMR (cterm (u^0) LMR y n u^0)
;;          (cterm ((sd yprod sd)^2) 
;;          (AndDMR (cterm (s^) SdMR d s^)
;;            (cterm (s^) 
;;            (AndLMR (cterm (s^0) SdMR d0 s^0)
;;              (cterm () 
;;              x*x===
;;              (1#2)*
;;              ((1#2)*((1#2)*((1#2)*(y*y+d0*d0)+d*d)+d*d0)+
;;               (1#2)*((1#2)*(d0*y+d*d)+d*y))))
;;            s^))
;;          (sd yprod sd)^2))
;;        (al yprod sd yprod sd)^1))
;;      (al yprod sd yprod sd)^0))
;;    (al yprod sd yprod sd)^))
;;  (cLSquareAux u^))

;; with computation rule

;; cLSquareAux eqd
;; ([u][if (cLClosure u) ([s,u0][if (cLClosure u0) ([s0,u1]u1 pair s pair s0)])])

(deanimate "LSquareAux")

;; LSquareZero
(set-goal "allnc x,n (L x n -> L(x*x) Zero)")
(assume "x" "n" "Lx")
(assert "Real x")
(use "LToReal" (pt "n"))
(use "Lx")
(assume "Rx")
(intro 0)
(autoreal)
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "LToBd" (pt "n"))
(use "Lx")
(use "LToBd" (pt "n"))
(use "Lx")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LSquareZero")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [u]U

(add-sound "LSquareZero")

;; ok, LSquareZeroSound has been added as a new theorem:

;; allnc x,n,u^(LMR x n u^ -> LMR(x*x)Zero(cLSquareZero u^))

;; with computation rule

;; cLSquareZero eqd([u]U)

;; (deanimate "LSquareZero")
;; We leave LSquareZero animated because it is simple.

;; LSquare 
(set-goal "all n allnc x(L x(n+4) -> L(x*x)n)")
(cut "all n all m allnc x(m<=n -> L x(m+4) -> L(x*x) m)")
(assume "CutHyp" "n" "x" "Lx")
(use "CutHyp" (pt "n"))
(use "Truth")
(use "Lx")
(ind)
(assume "m" "x" "0<=n" "Lx")
(ng)
(simp "0<=n")
(use "LSquareZero" (pt "m+4"))
(use "Lx")
(assume "n" "IH" "m" "x" "m<=n+1" "Lx")
(cases (pt "m<=n"))
(assume "m<=n")
(use "IH")
(use "m<=n")
(use "Lx")
(assume "n<m")
(assert "m=Succ n")
(use "NatLeAntiSym")
(use "m<=n+1")
(use "NatLtToSuccLe")
(use "NatNotLeToLt")
(use "n<m")
(assume "m=Sn")
(simp "m=Sn")
(simphyp-to "Lx" "m=Sn" "LxII")
(assert "exr y,d0,d1 (L y(n+3) andi Sd d0 andi Sd d1 andi
 x*x===(1#2)*((1#2)*((1#2)*((1#2)*(y*y+d1*d1)+d0*d0)+d0*d1)+
(1#2)*((1#2)*(d1*y+d0*d0)+d0*y)))")
(use "LSquareAux")
(use "LxII")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "y" "yProp")
(by-assume "yProp" "d0" "yd0Prop")
(by-assume "yd0Prop" "d1" "yd0d1Prop")
(use "LCompat" (pt "(1#2)*((1#2)*((1#2)*((1#2)*(y*y+d1*d1)+d0*d0)+d0*d1)+(1#2)*((1#2)*(d1*y+d0*d0)+d0*y))"))
(use "RealEqSym")
(use "yd0d1Prop")
(assert "Real y")
(use "LToReal" (pt "n+3"))
(use "yd0d1Prop")
(assume "Ry")
(use "LAverage")
(intro 1 (pt "d0*d1") (pt "(1#2)*((1#2)*(y*y+d1*d1)+d0*d0)"))
(use "IntTimesSdToSd")
(use "yd0d1Prop")
(use "yd0d1Prop")
(use "GenLMinus" (pt "d0*d0") (pt "(1#2)*(y*y+d1*d1)"))
(use "IntTimesSdToSd")
(use "yd0d1Prop")
(use "yd0d1Prop")
;; (ng #t)
(use "GenLMinus" (pt "d1*d1") (pt "y*y"))
(use "IntTimesSdToSd")
(use "yd0d1Prop")
(use "yd0d1Prop")
(ng #t)
(cases (pt "n"))
(assume "n=0")
(ng #t)
(use "LSquareZero" (pt "n+3"))
(use "yd0d1Prop")
(assume "n0" "n=Sn0")
(ng #t)
(use "IH")
(simp "n=Sn0")
(use "Truth")
(cases (pt "n0"))
(assume "n0=0")
(simphyp-to "n=Sn0" "n0=0" "n=1")
(simp (pf "Zero+4=n+3"))
(use "yd0d1Prop")
(simp "n=1")
(use "Truth")
(assume "n1" "n0=Sn1")
(simp (pf "Succ n1+4=n+3"))
(use "yd0d1Prop")
(ng #t)
(simp "<-" "n0=Sn1")
(simp "<-" "n=Sn0")
(use "Truth")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "LAverage")
(intro 1 (pt "d0*d0") (pt "d1*y"))
(use "IntTimesSdToSd")
(use "yd0d1Prop")
(use "yd0d1Prop")
(use "LSdTimes")
(use "yd0d1Prop")
(use "LSuccToL")
(use "yd0d1Prop")
(use "RealEqRefl")
(autoreal)
(use "LSdTimes")
(use "yd0d1Prop")
(use "yd0d1Prop")
;; Proof finished.
;; (cdp)
(save "LSquare")

;; ;; LSquare 
;; (set-goal "all n allnc x(L x(n+4) -> L(x*x)n)")
;; (cut "all n all m allnc x(m<=n -> L x(m+4) -> L(x*x) m)")
;; (assume "CutHyp" "n" "x" "Lx")
;; (use "CutHyp" (pt "n"))
;; (use "Truth")
;; (use "Lx")
;; (ind)
;; (assume "m" "x" "0<=n" "Lx")
;; (ng)
;; (simp "0<=n")
;; (use "LSquareZero" (pt "m+4"))
;; (use "Lx")
;; (assume "n" "IH" "m" "x" "m<=n+1" "Lx")
;; (cases (pt "m<=n"))
;; (assume "m<=n")
;; (use "IH")
;; (use "m<=n")
;; (use "Lx")
;; (assume "n<m")
;; (assert "m=Succ n")
;; (use "NatLeAntiSym")
;; (use "m<=n+1")
;; (use "NatLtToSuccLe")
;; (use "NatNotLeToLt")
;; (use "n<m")
;; (assume "m=Sn")
;; (simp "m=Sn")
;; (simphyp-to "Lx" "m=Sn" "LxII")
;; (assert "exr y,d0,d1 (L y(n+3) andi Sd d0 andi Sd d1 andi x*x===(1#2)*((1#2)*((1#2)*((1#2)*(y*y+d1*d1)+d0*d0)+d0*d1)+(1#2)*((1#2)*(d1*y+d0*d0)+d0*y)))")
;; (use "LSquareAux")
;; (use "LxII")
;; (assume "ExHyp")
;; (by-assume "ExHyp" "y" "yProp")
;; (by-assume "yProp" "d0" "yd0Prop")
;; (by-assume "yd0Prop" "d1" "yd0d1Prop")
;; (use "LCompat" (pt "(1#2)*((1#2)*((1#2)*((1#2)*(y*y+d1*d1)+d0*d0)+d0*d1)+(1#2)*((1#2)*(d1*y+d0*d0)+d0*y))"))
;; (use "RealEqSym")
;; (use "yd0d1Prop")
;; (assert "Real y")
;; (use "LToReal" (pt "n+3"))
;; (use "yd0d1Prop")
;; (assume "Ry")
;; (use "LAverage")
;; (intro 1 (pt "d0*d1") (pt "(1#2)*((1#2)*(y*y+d1*d1)+d0*d0)"))
;; (use "IntTimesSdToSd")
;; (use "yd0d1Prop")
;; (use "yd0d1Prop")
;; (use "GenLMinus" (pt "d0*d0") (pt "(1#2)*(y*y+d1*d1)"))
;; (use "IntTimesSdToSd")
;; (use "yd0d1Prop")
;; (use "yd0d1Prop")
;; ;; (ng #t)
;; (use "GenLMinus" (pt "d1*d1") (pt "y*y"))
;; (use "IntTimesSdToSd")
;; (use "yd0d1Prop")
;; (use "yd0d1Prop")
;; (ng #t)
;; (cases (pt "n"))
;; (assume "n=0")
;; (ng #t)
;; (use "LSquareZero" (pt "n+3"))
;; (use "yd0d1Prop")
;; (assume "n0" "n=Sn0")
;; (ng #t)
;; (use "IH")
;; (simp "n=Sn0")
;; (use "Truth")
;; (cases (pt "n0"))
;; (assume "n0=0")
;; (simphyp-to "n=Sn0" "n0=0" "n=1")
;; (simp (pf "Zero+4=n+3"))
;; (use "yd0d1Prop")
;; (simp "n=1")
;; (use "Truth")
;; (assume "n1" "n0=Sn1")
;; (simp (pf "Succ n1+4=n+3"))
;; (use "yd0d1Prop")
;; (ng #t)
;; (simp "<-" "n0=Sn1")
;; (simp "<-" "n=Sn0")
;; (use "Truth")
;; (use "RealEqRefl")
;; (autoreal)
;; (use "RealEqRefl")
;; (autoreal)
;; (use "RealEqRefl")
;; (autoreal)
;; (use "LAverage")
;; (intro 1 (pt "d0*d0") (pt "d1*y"))
;; (use "IntTimesSdToSd")
;; (use "yd0d1Prop")
;; (use "yd0d1Prop")
;; (use "LSdTimes")
;; (use "yd0d1Prop")
;; (use "LSuccToL")
;; (use "yd0d1Prop")
;; (use "RealEqRefl")
;; (autoreal)
;; (use "LSdTimes")
;; (use "yd0d1Prop")
;; (use "yd0d1Prop")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "LSquare")

(define eterm (proof-to-extracted-term))
(add-var-name "uss" (py "al yprod sd yprod sd"))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n]
;;  (Rec nat=>nat=>al=>al)n([n0,u]U)
;;  ([n0,(nat=>al=>al),n1,u]
;;    [if (n1<=n0)
;;      ((nat=>al=>al)n1 u)
;;      [let uss
;;       (cLSquareAux u)
;;       (cLAverage(Succ n0)
;;       (C(cIntTimesSdToSd clft crht uss crht crht uss)
;;        (cGenLMinus(Succ n0)(cIntTimesSdToSd clft crht uss clft crht uss)
;;         (cGenLMinus n0(cIntTimesSdToSd crht crht uss crht crht uss)
;;          [if n0 U ([n2](nat=>al=>al)n2 clft uss)])))
;;       (cLAverage(Succ(Succ n0))
;;        (C(cIntTimesSdToSd clft crht uss clft crht uss)
;;         (cLSdTimes(Succ(Succ n0))crht crht uss
;;          (cLSuccToL(Succ(Succ n0))clft uss)))
;;        (cLSdTimes(Succ(Succ(Succ n0)))clft crht uss clft uss)))]])
;;  n

(add-sound "LSquare")

;; ok, LSquareSound has been added as a new theorem:

;; allnc n,x,u^(LMR x(n+4)u^ -> LMR(x*x)n(cLSquare n u^))

;; with computation rule

;; cLSquare eqd
;; ([n]
;;   (Rec nat=>nat=>al=>al)n([n0,u]U)
;;   ([n0,(nat=>al=>al),n1,u]
;;     [if (n1<=n0)
;;       ((nat=>al=>al)n1 u)
;;       [let uss
;;        (cLSquareAux u)
;;        (cLAverage(Succ n0)
;;        (C(cIntTimesSdToSd clft crht uss crht crht uss)
;;         (cGenLMinus(Succ n0)(cIntTimesSdToSd clft crht uss clft crht uss)
;;          (cGenLMinus n0(cIntTimesSdToSd crht crht uss crht crht uss)
;;           [if n0 U ([n2](nat=>al=>al)n2 clft uss)])))
;;        (cLAverage(Succ(Succ n0))
;;         (C(cIntTimesSdToSd clft crht uss clft crht uss)
;;          (cLSdTimes(Succ(Succ n0))crht crht uss
;;           (cLSuccToL(Succ(Succ n0))clft uss)))
;;         (cLSdTimes(Succ(Succ(Succ n0)))clft crht uss clft uss)))]])
;;   n)

(deanimate "LSquare")

;; LMultAux
(set! COMMENT-FLAG #f)
(set-goal
 "allnc x,y,n(
     L x(n+2) -> 
     L y(n+2) -> 
     exr x0,y0,d0,d1,e0,e1(
      L x0 n andd 
      L y0 n andd 
      Sd d0 andd 
      Sd d1 andd 
      Sd e0 andd 
      Sd e1 andl 
      x*y===
      (1#2)*
      ((1#2)*((1#2)*((1#2)*(x0*y0+d1*e1)+d0*e1)+d0*e0)+
       (1#2)*((1#2)*(d0*y0+e0*x0)+(1#2)*((1#2)*(e1*x0+d1*y0)+d1*e0)))))")
(assume "x" "y" "n" "Lx" "Ly")
(inst-with-to "LClosure" (pt "x") (pt "n+1") "Lx" "xInst")
(by-assume "xInst" "d0" "d0Prop")
(by-assume "d0Prop" "x0" "d0x0Prop")
(elim "d0x0Prop")
(assume "Sdd0" "ConjI")
(drop "d0x0Prop")
(elim "ConjI")
(drop "ConjI")
(assume "xDef" "Lx0")
(inst-with-to "LClosure" (pt "x0") (pt "n") "Lx0" "x0Inst")
(by-assume "x0Inst" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(elim "d1x1Prop")
(assume "Sdd1" "ConjII")
(drop "d1x1Prop")
(elim "ConjII")
(drop "ConjII")
(assume "x0Def" "Lx1")
(inst-with-to "LClosure" (pt "y") (pt "n+1") "Ly" "yInst")
(by-assume "yInst" "e0" "e0Prop")
(by-assume "e0Prop" "y0" "e0y0Prop")
(elim "e0y0Prop")
(assume "Sde0" "yConjI")
(drop "e0y0Prop")
(elim "yConjI")
(drop "yConjI")
(assume "yDef" "Ly0")
(inst-with-to "LClosure" (pt "y0") (pt "n") "Ly0" "y0Inst")
(by-assume "y0Inst" "e1" "e1Prop")
(by-assume "e1Prop" "y1" "e1y1Prop")
(elim "e1y1Prop")
(assume "Sde1" "yConjII")
(drop "e1y1Prop")
(elim "yConjII")
(drop "yConjII")
(assume "y0Def" "Ly1")
(assert "Real x")
(use "LToReal" (pt "n+2"))
(use "Lx")
(assume "Rx")
(assert "Real x0")
(use "LToReal" (pt "n+1"))
(use "Lx0")
(assume "Rx0")
(assert "Real x1")
(use "LToReal" (pt "n"))
(use "Lx1")
(assume "Rx1")
(assert "Real y")
(use "LToReal" (pt "n+2"))
(use "Ly")
(assume "Ry")
(assert "Real y0")
(use "LToReal" (pt "n+1"))
(use "Ly0")
(assume "Ry0")
(assert "Real y1")
(use "LToReal" (pt "n"))
(use "Ly1")
(assume "Ry1")
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(intro 0 (pt "d0"))
(intro 0 (pt "d1"))
(intro 0 (pt "e0"))
(intro 0 (pt "e1"))
(split)
(use "Lx1")
(split)
(use "Ly1")
(split)
(use "Sdd0")
(split)
(use "Sdd1")
(split)
(use "Sde0")
(split)
(use "Sde1")
(simpreal "xDef")
(simpreal "x0Def")
(simpreal "yDef")
(simpreal "y0Def")
(simpreal "<-" "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqTrans" (pt "(1#2)*(((1#2)*(x1+d1)+d0)*(((1#2)*(y1+e1)+e0)))"))
(use "RealEqSym")
(simpreal "RealTimesAssoc")
(simpreal-with "RealTimesComm"
	       (pt "RealConstr([n](1#2))([p]Zero)")
	       (pt "((1#2)*(x1+d1)+d0)") "?" "?")
(simpreal "<-" "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(simpreal "<-" "RealTimesPlusDistr")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(simpreal "RealTimesPlusDistr")
(use "RealEqTrans" (pt "(1#2)*((1#2)*(x1*y1+d1*e1)+
 d0*e1)+((1#2)*d0*y1+(1#2)*((1#2)*(e1*x1+d1*y1))+((1#2)*(x1+d1)+d0)*e0)"))
(use "RealEqSym")
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqSym")
(simpreal "RealTimesPlusDistrLeft")
(simpreal (pf "(1#2)*(x1+d1)*((1#2)*(y1+e1))===
               (1#2)*((1#2)*(x1*y1+d1*e1))+(1#2)*(1#2)*(e1*x1+d1*y1)"))
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "(1#2)*(1#2)*(e1*x1+d1*y1)+d0*((1#2)*(y1+e1))===
  (RealTimes(1#2)(d0*e1))+((1#2)*(1#2)*(e1*x1+d1*y1)+(1#2)*d0*y1)"))
(simpreal "RealPlusAssoc")
(simpreal-with "<-" "RealTimesPlusDistr"
	       (pt "RealConstr([n](1#2))([p]Zero)")
	       (pt "((1#2)*(x1*y1+d1*e1))")
	       (pt "RealConstr([n](d0*e1))([p]Zero)") "?" "?" "?")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusComm")
(simpreal "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(simpreal "RealPlusComm")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
;;(ng #t)
(simpreal (pf "(1#2)*d0*y1===(1#2)*(d0*y1)"))
(simpreal "<-" "RealTimesPlusDistr")
(use "RealEqSym")
(simpreal "RealTimesAssoc")
(simpreal-with "RealTimesComm"
	       (pt "RealConstr([n]d0#1)([p]Zero)")
	       (pt "RealConstr([n]1#2)([p]Zero)") "?" "?")
(simpreal "<-" "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealTimesPlusDistr")
(use "RealEqRefl")
(autoreal)
(ng #t)
(simpreal "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
(simpreal-with "RealTimesComm"
	       (pt "RealConstr([n](1#2))([p]Zero)")
	       (pt "y1+e1") "?" "?")
(simpreal "RealTimesAssoc")
(simpreal "RealTimesComm")
(use "RealEqSym")
(simpreal "<-" "RealTimesAssoc")
(simpreal (pf "(1#2)*(1#2)*(e1*x1+d1*y1)===(1#2)*((1#2)*(e1*x1+d1*y1))"))
(simpreal "<-" "RealTimesPlusDistr")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "<-" "RealTimesPlusDistr")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusAssoc")
(simpreal "RealPlusComm")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(ng #t)
(simpreal "RealPlusComm")
(use "RealPlusCompat")
(simpreal "RealTimesComm")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
(simpreal (pf "(1#2)*(1#2)*(e1*x1+d1*y1)===(1#2)*((1#2)*(e1*x1+d1*y1))"))
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
(simpreal "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusAssoc")
(simpreal-with "RealTimesPlusDistr"
	       (pt "RealConstr([n](1#2))([p]Zero)")
	       (pt "d0*y1")
	       (pt "e0*x1") "?" "?" "?")
(simpreal "RealPlusAssoc")
(simpreal-with "RealPlusComm"
	       (pt "RealConstr([n]d0*e0#1)([p]Zero)")
	       (pt "(1#2)*(d0*y1)") "?" "?")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(simpreal "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(simpreal-with "RealTimesPlusDistrLeft"
	       (pt "(1#2)*(x1+d1)")
	       (pt "RealConstr([n]d0#1)([p]Zero)")
	       (pt "RealConstr([n]e0#1)([p]Zero)")"?" "?" "?")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusComm")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(simpreal "RealTimesPlusDistr")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusComm")
(simpreal "RealPlusAssoc")
(use "RealEqSym")
(simpreal "RealPlusComm")
(use "RealPlusCompat")
(simpreal "<-" "RealTimesPlusDistr")
(simpreal "<-" "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealPlusComm")
(ng #t)
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealTimesComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
(set! COMMENT-FLAG #t)
;; Proof finished.
;; (cp)
(save "LMultAux")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [u,u0]
;;  [case (cLClosure u)
;;    (s pair u1 -> 
;;    [case (cLClosure u1)
;;      (s0 pair u2 -> 
;;      [case (cLClosure u0)
;;        (s1 pair u3 -> 
;;        [case (cLClosure u3)
;;          (s2 pair u4 -> u2 pair u4 pair s pair s0 pair s1 pair s2)])])])]

(add-sound "LMultAux")

;; ok, LMultAuxSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x(n+2)u^ -> 
;;  allnc u^0(
;;   LMR y(n+2)u^0 -> 
;;   (ExRTMR rea
;;     al yprod al yprod sd yprod sd yprod sd yprod sd
;;     (cterm (x0,(al yprod al yprod sd yprod sd yprod sd yprod sd)^) 
;;     (ExRTMR rea
;;       al yprod al yprod sd yprod sd yprod sd yprod sd
;;       (cterm (y0,(al yprod al yprod sd yprod sd yprod sd yprod sd)^0) 
;;       (ExRTMR int
;;         al yprod al yprod sd yprod sd yprod sd yprod sd
;;         (cterm (d,(al yprod al yprod sd yprod sd yprod sd yprod sd)^1) 
;;         (ExRTMR int
;;           al yprod al yprod sd yprod sd yprod sd yprod sd
;;           (cterm (d0,(al yprod al yprod sd yprod sd yprod sd yprod sd)^2) 
;;           (ExRTMR int
;;             al yprod al yprod sd yprod sd yprod sd yprod sd
;;             (cterm (e,(al yprod al yprod sd yprod sd yprod sd yprod sd)^3) 
;;             (ExRTMR int
;;               al yprod al yprod sd yprod sd yprod sd yprod sd
;;               (cterm (e0,(al yprod al yprod sd yprod sd yprod sd yprod sd)^4) 
;;               (AndDMR (cterm (u^1) LMR x0 n u^1)
;;                 (cterm ((al yprod sd yprod sd yprod sd yprod sd)^5) 
;;                 (AndDMR (cterm (u^1) LMR y0 n u^1)
;;                   (cterm ((sd yprod sd yprod sd yprod sd)^6) 
;;                   (AndDMR (cterm (s^) SdMR d s^)
;;                     (cterm ((sd yprod sd yprod sd)^7) 
;;                     (AndDMR (cterm (s^) SdMR d0 s^)
;;                       (cterm ((sd yprod sd)^8) 
;;                       (AndDMR (cterm (s^) SdMR e s^)
;;                         (cterm (s^) 
;;                         (AndLMR (cterm (s^0) SdMR e0 s^0)
;;                           (cterm () 
;;                           x*y===
;;                           (1#2)*
;;                           ((1#2)*((1#2)*((1#2)*(x0*y0+d0*e0)+d*e0)+d*e)+
;;                            (1#2)*
;;                            ((1#2)*(d*y0+e*x0)+
;;                             (1#2)*((1#2)*(e0*x0+d0*y0)+d0*e)))))
;;                         s^))
;;                       (sd yprod sd)^8))
;;                     (sd yprod sd yprod sd)^7))
;;                   (sd yprod sd yprod sd yprod sd)^6))
;;                 (al yprod sd yprod sd yprod sd yprod sd)^5))
;;               (al yprod al yprod sd yprod sd yprod sd yprod sd)^4))
;;             (al yprod al yprod sd yprod sd yprod sd yprod sd)^3))
;;           (al yprod al yprod sd yprod sd yprod sd yprod sd)^2))
;;         (al yprod al yprod sd yprod sd yprod sd yprod sd)^1))
;;       (al yprod al yprod sd yprod sd yprod sd yprod sd)^0))
;;     (al yprod al yprod sd yprod sd yprod sd yprod sd)^))
;;   (cLMultAux u^ u^0)))

;; with computation rule

;; cLMultAux eqd
;; ([u,u0]
;;   [if (cLClosure u)
;;     ([s,u1]
;;      [if (cLClosure u1)
;;        ([s0,u2]
;;         [if (cLClosure u0)
;;           ([s1,u3]
;;            [if (cLClosure u3)
;;              ([s2,u4]u2 pair u4 pair s pair s0 pair s1 pair s2)])])])])

(deanimate "LMultAux")

;; LMultZero
(set-goal "allnc x,y,n(L x n -> L y n -> L(x*y) Zero)")
(assume "x" "y" "n" "Lx" "Ly")
(assert "Real x")
(use "LToReal" (pt "n"))
(use "Lx")
(assume "Rx")
(assert "Real y")
(use "LToReal" (pt "n"))
(use "Ly")
(assume "Ry")
(intro 0)
(autoreal)
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "LToBd" (pt "n"))
(use "Lx")
(use "LToBd" (pt "n"))
(use "Ly")
(use "RealLeRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "LMultZero")

(add-sound "LMultZero")

;; ok, LMultZeroSound has been added as a new theorem:

;; allnc x,y,n,u^(
;;  LMR x n u^ -> allnc u^0(LMR y n u^0 -> LMR(x*y)Zero(cLMultZero u^ u^0)))

;; with computation rule

;; cLMultZero eqd([u,u0]U)

;; (deanimate "LMultZero")
;; Leave LMultZero animated because it is simple.

;; LMult 
(set-goal "all n allnc x,y(L x(n+5) -> L y(n+5) -> L(x*y)n)")
(cut "all n all m allnc x,y(m<=n -> L x(m+5) -> L y(m+5) -> L(x*y)m)")
(assume "CutHyp" "n" "x" "y" "Lx" "Ly")
(use "CutHyp" (pt "n"))
(use "Truth")
(use "Lx")
(use "Ly")
(ind)
(assume "m" "x" "y" "0<=n" "Lx" "Ly")
(ng)
(simp "0<=n")
(use "LMultZero" (pt "m+5"))
(use "Lx")
(use "Ly")
(assume "n" "IH" "m" "x" "y" "m<=n+1" "Lx" "Ly")
(cases (pt "m<=n"))
(assume "m<=n")
(use "IH")
(use "m<=n")
(use "Lx")
(use "Ly")
(assume "n<m")
(assert "m=Succ n")
(use "NatLeAntiSym")
(use "m<=n+1")
(use "NatLtToSuccLe")
(use "NatNotLeToLt")
(use "n<m")
(assume "m=Sn")
(simp "m=Sn")
(simphyp-to "Lx" "m=Sn" "LxII")
(simphyp-to "Ly" "m=Sn" "LyII")
(inst-with-to "LMultAux" (pt "x") (pt "y") (pt "n+4") "LxII" "LyII" "Inst")
(by-assume "Inst" "x0" "x0Prop")
(by-assume "x0Prop" "y0" "x0y0Prop")
(by-assume "x0y0Prop" "d0" "x0y0d0Prop")
(by-assume "x0y0d0Prop" "d1" "x0y0d0d1Prop")
(by-assume "x0y0d0d1Prop" "e0" "x0y0d0d1e0Prop")
(by-assume "x0y0d0d1e0Prop" "e1" "x0y0d0d1e0e1Prop")
(assert "Real x0")
(use "LToReal" (pt "n+4"))
(use "x0y0d0d1e0e1Prop")
(assume "Rx0")
(assert "Real y0")
(use "LToReal" (pt "n+4"))
(use "x0y0d0d1e0e1Prop")
(assume "Ry0")
(use "LCompat" (pt "(1#2)*
    ((1#2)*((1#2)*((1#2)*(x0*y0+d1*e1)+d0*e1)+d0*e0)+
     (1#2)*((1#2)*(d0*y0+e0*x0)+(1#2)*((1#2)*(e1*x0+d1*y0)+d1*e0)))"))
(use "RealEqSym")
(use "x0y0d0d1e0e1Prop")
;; (assert "Real x")
;; (use "LToReal" (pt "n+3"))
;; (use "x0y0d0d1e0e1Prop")
;; (assume "Rx")
(use "LAverage")
(intro 1 (pt "d0*e0") (pt "(1#2)*((1#2)*(x0*y0+d1*e1)+d0*e1)"))
(use "IntTimesSdToSd")
(use "x0y0d0d1e0e1Prop")
(use "x0y0d0d1e0e1Prop")
(intro 1 (pt "d0*e1") (pt "(1#2)*(x0*y0+d1*e1)"))
;; (use "GenLMinus" (pt "d0*d0") (pt "(1#2)*(y*y+d1*d1)"))
(use "IntTimesSdToSd")
(use "x0y0d0d1e0e1Prop")
(use "x0y0d0d1e0e1Prop")
;; (ng #t)
(use "GenLMinus" (pt "d1*e1") (pt "x0*y0"))
(use "IntTimesSdToSd")
(use "x0y0d0d1e0e1Prop")
(use "x0y0d0d1e0e1Prop")
(ng #t)
(cases (pt "n"))
(assume "n=0")
(ng #t)
(use "LMultZero" (pt "n+4"))
(use "x0y0d0d1e0e1Prop")
(use "x0y0d0d1e0e1Prop")
(assume "n0" "n=Sn0")
(ng #t)
(use "IH")
(simp "n=Sn0")
(use "Truth")
(simp (pf "n0+5=n+4"))
(use "x0y0d0d1e0e1Prop")
(simp "n=Sn0")
(use "Truth")
(simp (pf "n0+5=n+4"))
(use "x0y0d0d1e0e1Prop")
(simp "n=Sn0")
(use "Truth")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "LAverage")
(use "LAverage")
(use "LSdTimes")
(use "x0y0d0d1e0e1Prop")
(use "x0y0d0d1e0e1Prop")
(use "LSdTimes")
(use "x0y0d0d1e0e1Prop")
(use "x0y0d0d1e0e1Prop")
(intro 1 (pt "d1*e0") (pt "(1#2)*(e1*x0+d1*y0)"))
(use "IntTimesSdToSd")
(use "x0y0d0d1e0e1Prop")
(use "x0y0d0d1e0e1Prop")
(use "LAverage")
(use "LSdTimes")
(use "x0y0d0d1e0e1Prop")
(use "LSuccToL")
(use "x0y0d0d1e0e1Prop")
(use "LSdTimes")
(use "x0y0d0d1e0e1Prop")
(use "LSuccToL")
(use "x0y0d0d1e0e1Prop")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "LMult")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n]
;;  (Rec nat=>nat=>al=>al=>al)n([n0,u,u0]U)
;;  ([n0,(nat=>al=>al=>al),n1,u,u0]
;;    [if (n1<=n0)
;;      ((nat=>al=>al=>al)n1 u u0)
;;      (cLAverage(Succ n0)
;;      (C
;;       (cIntTimesSdToSd clft crht crht(cLMultAux u u0)
;;        clft crht crht crht crht(cLMultAux u u0))
;;       (C
;;        (cIntTimesSdToSd clft crht crht(cLMultAux u u0)
;;         crht crht crht crht crht(cLMultAux u u0))
;;        (cGenLMinus n0
;;         (cIntTimesSdToSd clft crht crht crht(cLMultAux u u0)
;;          crht crht crht crht crht(cLMultAux u u0))
;;         [if n0
;;           U
;;           ([n2]
;;            (nat=>al=>al=>al)n2 clft(cLMultAux u u0)clft crht(cLMultAux u u0))])))
;;      (cLAverage(Succ(Succ n0))
;;       (cLAverage(Succ(Succ(Succ n0)))
;;        (cLSdTimes(Succ(Succ(Succ(Succ n0))))clft crht crht(cLMultAux u u0)
;;         clft crht(cLMultAux u u0))
;;        (cLSdTimes(Succ(Succ(Succ(Succ n0))))
;;         clft crht crht crht crht(cLMultAux u u0)
;;         clft(cLMultAux u u0)))
;;       (C
;;        (cIntTimesSdToSd clft crht crht crht(cLMultAux u u0)
;;         clft crht crht crht crht(cLMultAux u u0))
;;        (cLAverage(Succ(Succ n0))
;;         (cLSdTimes(Succ(Succ(Succ n0)))
;;          crht crht crht crht crht(cLMultAux u u0)
;;          (cLSuccToL(Succ(Succ(Succ n0)))clft(cLMultAux u u0)))
;;         (cLSdTimes(Succ(Succ(Succ n0)))clft crht crht crht(cLMultAux u u0)
;;          (cLSuccToL(Succ(Succ(Succ n0)))clft crht(cLMultAux u u0)))))))])
;;  n

(add-sound "LMult")

;; ok, LMultSound has been added as a new theorem:

;; allnc n,x,y,u^(
;;  LMR x(n+5)u^ -> allnc u^0(LMR y(n+5)u^0 -> LMR(x*y)n(cLMult n u^ u^0)))

;; with computation rule

;; cLMult eqd
;; ([n]
;;   (Rec nat=>nat=>al=>al=>al)n([n0,u,u0]U)
;;   ([n0,(nat=>al=>al=>al),n1,u,u0]
;;     [if (n1<=n0)
;;       ((nat=>al=>al=>al)n1 u u0)
;;       (cLAverage(Succ n0)
;;       (C
;;        (cIntTimesSdToSd clft crht crht(cLMultAux u u0)
;;         clft crht crht crht crht(cLMultAux u u0))
;;        (C
;;         (cIntTimesSdToSd clft crht crht(cLMultAux u u0)
;;          crht crht crht crht crht(cLMultAux u u0))
;;         (cGenLMinus n0
;;          (cIntTimesSdToSd clft crht crht crht(cLMultAux u u0)
;;           crht crht crht crht crht(cLMultAux u u0))
;;          [if n0
;;            U
;;            ([n2]
;;             (nat=>al=>al=>al)n2 clft(cLMultAux u u0)
;;             clft crht(cLMultAux u u0))])))
;;       (cLAverage(Succ(Succ n0))
;;        (cLAverage(Succ(Succ(Succ n0)))
;;         (cLSdTimes(Succ(Succ(Succ(Succ n0))))clft crht crht(cLMultAux u u0)
;;          clft crht(cLMultAux u u0))
;;         (cLSdTimes(Succ(Succ(Succ(Succ n0))))
;;          clft crht crht crht crht(cLMultAux u u0)
;;          clft(cLMultAux u u0)))
;;        (C
;;         (cIntTimesSdToSd clft crht crht crht(cLMultAux u u0)
;;          clft crht crht crht crht(cLMultAux u u0))
;;         (cLAverage(Succ(Succ n0))
;;          (cLSdTimes(Succ(Succ(Succ n0)))
;;           crht crht crht crht crht(cLMultAux u u0)
;;           (cLSuccToL(Succ(Succ(Succ n0)))clft(cLMultAux u u0)))
;;          (cLSdTimes(Succ(Succ(Succ n0)))clft crht crht crht(cLMultAux u u0)
;;           (cLSuccToL(Succ(Succ(Succ n0)))clft crht(cLMultAux u u0)))))))])
;;   n)

(deanimate "LMult")

;; Haskell translation
'(
  (animate "LMultOld")
  (animate "Rht")
  (animate "LMultToMultc")
  (animate "LSuccToL")
  (animate "LMultcToL")
  (animate "LToLPred")
  (animate "LMultcSatLCl")
  (animate "LMultcSatLClAvcDestr")
  (animate "LMultcSatLClAuxJ")
  (animate "LMultcSatLClAuxK")
  (animate "LAvcToL")
  (animate "LAvcSatLCl")
  (animate "LAvcSatLClAuxK")
  (animate "LAvcSatLClAuxJ")
  (animate "LSdTimes")
  (animate "LZero")
  (animate "LUMinus")
  (animate "SdUMinus")
  (animate "IntTimesSdToSd")
  (animate "Lft")
  (animate "LAverage")
  (animate "IntPlusSdToSdtwo")
  (animate "LAvToAvc")
  (animate "LClosure")

(terms-to-haskell-program
 "~/temp/l_multold_test.hs"
 (list (list (pt "cLMultOld") "multold")))

  (deanimate "LMultOld")
  (deanimate "Rht")
  (deanimate "LMultToMultc")
  (deanimate "LSuccToL")
  (deanimate "LMultcToL")
  (deanimate "LToLPred")
  (deanimate "LMultcSatLCl")
  (deanimate "LMultcSatLClAvcDestr")
  (deanimate "LMultcSatLClAuxJ")
  (deanimate "LMultcSatLClAuxK")
  (deanimate "LAvcToL")
  (deanimate "LAvcSatLCl")
  (deanimate "LAvcSatLClAuxK")
  (deanimate "LAvcSatLClAuxJ")
  (deanimate "LSdTimes")
  (deanimate "LZero")
  (deanimate "LUMinus")
  (deanimate "SdUMinus")
  (deanimate "IntTimesSdToSd")
  (deanimate "Lft")
  (deanimate "LAverage")
  (deanimate "IntPlusSdToSdtwo")
  (deanimate "LAvToAvc")
  (deanimate "LClosure")
)

'(
(animate "LMult")
(animate "LSdTimes")
(animate "LSuccToL")
(animate "GenLMinus")
(animate "IntTimesSdToSd")
(animate "LMultAux")
(animate "LUMinus")
(animate "LAverage")
(animate "LAvcToL")
(animate "LAvToAvc")
(animate "LAvcSatLCl")
(animate "LAvcSatLClAuxJ")
(animate "LAvcSatLClAuxK")
(animate "IntPlusSdToSdtwo")
(animate "LZero")
(animate "Rht")
(animate "SdUMinus")
(animate "Lft")
(animate "LClosure")

(terms-to-haskell-program
 "~/temp/l_multnew_test.hs"
 (list (list (pt "cLMult") "mult")))

(deanimate "LMult")
(deanimate "LSdTimes")
(deanimate "LSuccToL")
(deanimate "GenLMinus")
(deanimate "IntTimesSdToSd")
(deanimate "LMultAux")
(deanimate "LUMinus")
(deanimate "LAverage")
(deanimate "LAvcToL")
(deanimate "LAvToAvc")
(deanimate "LAvcSatLCl")
(deanimate "LAvcSatLClAuxJ")
(deanimate "LAvcSatLClAuxK")
(deanimate "IntPlusSdToSdtwo")
(deanimate "LZero")
(deanimate "Rht")
(deanimate "SdUMinus")
(deanimate "Lft")
(deanimate "LClosure")
)
