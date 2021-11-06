;; 2021-11-06.  examples/analysis/sdavaux.scm

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (remove-var-name "x" "y" "z")
;; (libload "rea.scm")
;; ;; (set! COMMENT-FLAG #t)

;; (load "~/git/minlog/examples/analysis/JK.scm")
;; (load "~/git/minlog/examples/analysis/digits.scm")
;; (load "~/git/minlog/examples/analysis/sdcode.scm")

(display "loading sdavaux.scm ...") (newline)

;; CoIAvToAvc
(set-goal "allnc x,y(CoI x -> CoI y -> 
 exr i,x1,y1(Sdtwo i andi CoI x1 andi CoI y1 andi
 (1#2)*(x+y)===(1#4)*(x1+y1+i)))")
(assume "x" "y" "CoIx" "CoIy")
(inst-with-to "CoIClosure" (pt "x") "CoIx" "CoIClosureInstx")
(by-assume "CoIClosureInstx" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(assert "CoI x1")
 (use "dx1Prop")
(assume "CoIx1")
(inst-with-to "CoIClosure" (pt "y") "CoIy" "CoIClosureInsty")
(by-assume "CoIClosureInsty" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
 (assert "CoI y1")
(use "ey1Prop")
(assume "CoIy1")
(intro 0 (pt "d+e"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "IntPlusSdToSdtwo")
(use "dx1Prop")
(use "ey1Prop")
(split)
(use "CoIx1")
(split)
(use "CoIy1")
;; ?^35:(1#2)*(x+y)===(1#4)*(x1+y1+(d+e))
(assert "Real((1#4)*(x1+y1+(d+e)))")
(autoreal)
(assume "R")
(simpreal "dx1Prop")
(simpreal "ey1Prop")
;; ?^40:(1#2)*((1#2)*(x1+d)+(1#2)*(y1+e))===(1#4)*(x1+y1+(d+e))
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^50:(1#2)*((1#2)*(as n+d)+(1#2)*(bs n+e))==(1#4)*(as n+bs n+(d+e))
(simprat "<-" "RatTimesPlusDistr")
;; ?^51:(1#2)*((1#2)*(as n+d+(bs n+e)))==(1#4)*(as n+bs n+(d+e))
(ng #t)
;; ?^52:(1#4)*(as n+d+bs n+e)==(1#4)*(as n+bs n+(d+e))
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?^57:d+(bs n+e)==bs n+(d+e)
(ng #t)
(simp (pf "d+bs n=bs n+d"))
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "RatPlusComm")
;; Proof finished.
;; (cdp)
;; (cp)
(save "CoIAvToAvc")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [u,u0]
;;  cIntPlusSdToSdtwo clft(cCoIClosure u)clft(cCoIClosure u0)pair 
;;  crht(cCoIClosure u)pair crht(cCoIClosure u0)

(add-var-name "tuv" (py "sdtwo yprod ai yprod ai"))

(add-sound "CoIAvToAvc")

;; ok, CoIAvToAvcSound has been added as a new theorem:

;; allnc x,y,u^(
;;  CoIMR x u^ -> 
;;  allnc u^0(
;;   CoIMR y u^0 -> 
;;   (ExRTMR int
;;     sdtwo yprod ai yprod ai
;;     (cterm (i,tuv^) 
;;     (ExRTMR rea
;;       sdtwo yprod ai yprod ai
;;       (cterm (x0,tuv^0) 
;;       (ExRTMR rea
;;         sdtwo yprod ai yprod ai
;;         (cterm (y0,tuv^1) 
;;         (AndDMR (cterm (t^) SdtwoMR i t^)
;;           (cterm ((ai yprod ai)^) 
;;           (AndDMR (cterm (u^1) CoIMR x0 u^1)
;;             (cterm (u^1) 
;;             (AndLMR (cterm (u^2) CoIMR y0 u^2)
;;               (cterm () (1#2)*(x+y)===(1#4)*(x0+y0+i)))
;;             u^1))
;;           (ai yprod ai)^))
;;         tuv^1))
;;       tuv^0))
;;     tuv^))
;;   (cCoIAvToAvc u^ u^0)))

;; with computation rule

;; cCoIAvToAvc eqd
;; ([u,u0]
;;   cIntPlusSdToSdtwo clft(cCoIClosure u)clft(cCoIClosure u0)pair 
;;   crht(cCoIClosure u)pair crht(cCoIClosure u0))

;; (cp)

(deanimate "CoIAvToAvc")

;; For CoIAvcSatCoICl we need J,K.

;; CoIAvcSatCoIClAuxJ
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
(save "CoIAvcSatCoIClAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [s,s0,t]IntToSdtwo(J(SdToInt s+SdToInt s0+SdtwoToInt t*2))

(add-sound "CoIAvcSatCoIClAuxJ")
;; ok, CoIAvcSatCoIClAuxJSound has been added as a new theorem:

;; allnc d,e,i,s^(
;;  SdMR d s^ -> 
;;  allnc s^0(
;;   SdMR e s^0 -> 
;;   allnc t^(
;;    SdtwoMR i t^ -> SdtwoMR(J(d+e+i*2))(cCoIAvcSatCoIClAuxJ s^ s^0 t^))))

;; with computation rule

;; cCoIAvcSatCoIClAuxJ eqd
;; ([s,s0,t]IntToSdtwo(J(SdToInt s+SdToInt s0+SdtwoToInt t*2)))

;; (cp)

(deanimate "CoIAvcSatCoIClAuxJ")

;; CoIAvcSatCoIClAuxK
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
(save "CoIAvcSatCoIClAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [s,s0,t]IntToSd(K(SdToInt s+SdToInt s0+SdtwoToInt t*2))

(add-sound "CoIAvcSatCoIClAuxK")
;; ok, CoIAvcSatCoIClAuxKSound has been added as a new theorem:

;; allnc d,e,i,s^(
;;  SdMR d s^ -> 
;;  allnc s^0(
;;   SdMR e s^0 -> 
;;   allnc t^(SdtwoMR i t^ -> SdMR(K(d+e+i*2))(cCoIAvcSatCoIClAuxK s^ s^0 t^))))

;; with computation rule

;; cCoIAvcSatCoIClAuxK eqd
;; ([s,s0,t]IntToSd(K(SdToInt s+SdToInt s0+SdtwoToInt t*2)))

;; (cp)

(deanimate "CoIAvcSatCoIClAuxK")

;; CoIAvcSatCoICl
(set-goal "allnc i,x,y(Sdtwo i -> CoI x -> CoI y ->
 exr j,d,x1,y1(Sdtwo j andi Sd d andi CoI x1 andi CoI y1 andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+j)+d)))")
(assume "i" "x" "y" "Sdtwoi" "CoIx" "CoIy")
(inst-with-to "CoIClosure" (pt "x") "CoIx" "CoIClosureInst1")
(by-assume "CoIClosureInst1" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(assert "CoI x1")
 (use "dx1Prop")
(assume "CoIx1")
(inst-with-to "CoIClosure" (pt "y") "CoIy" "CoIClosureInst2")
(by-assume "CoIClosureInst2" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
 (assert "CoI y1")
(use "ey1Prop")
(assume "CoIy1")
(intro 0 (pt "J(d+e+i*2)"))
(intro 0 (pt "K(d+e+i*2)"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "CoIAvcSatCoIClAuxJ")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
(use "CoIAvcSatCoIClAuxK")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
(use "CoIx1")
(split)
(use "CoIy1")
;; ?^42:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+J(d+e+i*2))+K(d+e+i*2))
(simpreal "dx1Prop")
(simpreal "ey1Prop")
;; ?^44:(1#4)*((1#2)*(x1+d)+(1#2)*(y1+e)+i)===
;;      (1#2)*((1#4)*(x1+y1+J(d+e+i*2))+K(d+e+i*2))
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^54:(1#4)*((1#2)*(as n+d)+(1#2)*(bs n+e)+i)==
;;      (1#2)*((1#4)*(as n+bs n+J(d+e+i*2))+K(d+e+i*2))
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
;; ?^66:(1#8)*as n+(d#8)+(1#8)*bs n+(e#8)+(i#4)==
;;      (1#8)*as n+(1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2)
(use "RatEqvTrans" (pt "(1#8)*as n+((d#8)+(1#8)*bs n+(e#8)+(i#4))"))
(use "Truth")
(use "RatEqvTrans" (pt "(1#8)*as n+((1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2))"))
(use "RatPlusCompat")
(use "Truth")
(simp (pf "(d#8)+(1#8)*bs n=(1#8)*bs n+(d#8)"))
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?^79:(d#8)+((e#8)+(i#4))==(J(d+e+i*2)#8)+(K(d+e+i*2)#2)
(simprat (pf "(i#4)==(i*2#8)"))
(simprat (pf "(K(d+e+i*2)#2)==(K(d+e+i*2)*4#8)"))
;; ?^82:(d#8)+((e#8)+(i*2#8))==(J(d+e+i*2)#8)+(K(d+e+i*2)*4#8)
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(simp (pf "J(d+e+i*2)+K(d+e+i*2)*4=K(d+e+i*2)*4+J(d+e+i*2)"))
(simp "KJProp")
(use "Truth")
(use "IntPlusComm")
;; ?^83:(K(d+e+i*2)#2)==(K(d+e+i*2)*4#8)
(ng #t)
(simp "<-" "IntTimesAssoc")
(use "Truth")
;; ?^81:(i#4)==(i*2#8)
(ng #t)
(simp "<-" "IntTimesAssoc")
(use "Truth")
;; ?^74:(d#8)+(1#8)*bs n=(1#8)*bs n+(d#8)
(use "RatPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "CoIAvcSatCoICl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,u,u0]
;;  cCoIAvcSatCoIClAuxJ clft(cCoIClosure u)clft(cCoIClosure u0)t pair 
;;  cCoIAvcSatCoIClAuxK clft(cCoIClosure u)clft(cCoIClosure u0)t pair 
;;  crht(cCoIClosure u)pair crht(cCoIClosure u0)

;; This term can be read as follows.  Given t, u, u0, destruct the
;; latter two.  Both are composed, i.e., of the form s1u1 and s2u2.
;; Take their components s1,u1 and s2,u2.  Then we obtain the quadruple
;; J(s1,s2,t) pair K(s1,s2,t) pair u1 pair u2.

(add-var-name "tsuv" (py "sdtwo yprod sd yprod ai yprod ai"))

(add-sound "CoIAvcSatCoICl")
;; ok, CoIAvcSatCoIClSound has been added as a new theorem:

;; allnc i,x,y,t^(
;;  SdtwoMR i t^ -> 
;;  allnc u^(
;;   CoIMR x u^ -> 
;;   allnc u^0(
;;    CoIMR y u^0 -> 
;;    (ExRTMR int
;;      sdtwo yprod sd yprod ai yprod ai
;;      (cterm (j,tsuv^) 
;;      (ExRTMR int
;;        sdtwo yprod sd yprod ai yprod ai
;;        (cterm (d,tsuv^0) 
;;        (ExRTMR rea
;;          sdtwo yprod sd yprod ai yprod ai
;;          (cterm (x0,tsuv^1) 
;;          (ExRTMR rea
;;            sdtwo yprod sd yprod ai yprod ai
;;            (cterm (y0,tsuv^2) 
;;            (AndDMR (cterm (t^0) SdtwoMR j t^0)
;;              (cterm ((sd yprod ai yprod ai)^) 
;;              (AndDMR (cterm (s^) SdMR d s^)
;;                (cterm ((ai yprod ai)^0) 
;;                (AndDMR (cterm (u^1) CoIMR x0 u^1)
;;                  (cterm (u^1) 
;;                  (AndLMR (cterm (u^2) CoIMR y0 u^2)
;;                    (cterm () (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d)))
;;                  u^1))
;;                (ai yprod ai)^0))
;;              (sd yprod ai yprod ai)^))
;;            tsuv^2))
;;          tsuv^1))
;;        tsuv^0))
;;      tsuv^))
;;    (cCoIAvcSatCoICl t^ u^ u^0))))

;; with computation rule

;; cCoIAvcSatCoICl eqd
;; ([t,u,u0]
;;   cCoIAvcSatCoIClAuxJ clft(cCoIClosure u)clft(cCoIClosure u0)t pair 
;;   cCoIAvcSatCoIClAuxK clft(cCoIClosure u)clft(cCoIClosure u0)t pair 
;;   crht(cCoIClosure u)pair crht(cCoIClosure u0))

;; (cp)

(deanimate "CoIAvcSatCoICl")

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

;; CoIAvcToCoI
(set-goal "allnc z(exr i,x,y(Sdtwo i andi CoI x andi CoI y andi
 z===(1#4)*(x+y+i)) -> CoI z)")
(assume "z" "Qz")
(coind "Qz")
(assume "x" "Qx")
(by-assume "Qx" "i" "iProp")
(by-assume "iProp" "x1" "x1iProp")
(by-assume "x1iProp" "y1" "y1x1iProp")
(cut "exr j,d,x0,y0(
 Sdtwo j andi Sd d andi CoI x0 andi CoI y0 andi
 (1#4)*(x1+y1+i)===(1#2)*((1#4)*(x0+y0+j)+d))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "CoIAvcSatCoIClInst")
(by-assume "CoIAvcSatCoIClInst" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume  "jdProp" "x2" "jdx2Prop")
(by-assume "jdx2Prop" "y2" "jdx2y2Prop")
(assert "CoI x2")
(use "jdx2y2Prop")
(assume "CoIx2")
(assert "CoI y2")
(use "jdx2y2Prop")
(assume "CoIy2")
(intro 0 (pt "d"))
(intro 0 (pt "(1#4)*(x2+y2+j)"))
(intro 0 (pt "x"))
(split)
(use "jdx2y2Prop")
(split)
(autoreal)
(split)
(inst-with-to "CoIToBd" (pt "x2") "CoIx2" "x2Bd")
(inst-with-to "CoIToBd" (pt "y2") "CoIy2" "y2Bd")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealAbs(1#4)*((RealPlus 1 1)+2)"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeTrans" (pt "abs(x2+y2)+RealAbs j"))
;; 57,58
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "RealLeTrans" (pt "abs x2+abs y2"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "x2Bd")
(use "y2Bd")
(use "SdtwoBoundReal")
(use "jdx2y2Prop")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; 44
(split)
(intro 1)
(intro 0 (pt "j"))
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "jdx2y2Prop")
(split)
(use "CoIx2")
(split)
(use "CoIy2")
(use "RealEqRefl")
(autoreal)
(split)
(simpreal "y1x1iProp")
(use "jdx2y2Prop")
(use "RealEqRefl")
(use "RealEqToReal0" (pt "(1#4)*(x1+y1+i)"))
(use "y1x1iProp")
;; Now we prove the formula cut in above
(use "CoIAvcSatCoICl")
(use "y1x1iProp")
(use "y1x1iProp")
(use "y1x1iProp")
;; Proof finished.
;; (cdp)
(save "CoIAvcToCoI")

(define eterm (proof-to-extracted-term))
;; (add-var-name "tuv" (py "sdtwo yprod ai yprod ai"))
;; (add-var-name "tsuv" (py "sdtwo yprod sd yprod ai yprod ai"))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [tuv]
;;  (CoRec sdtwo yprod ai yprod ai=>ai)tuv
;;  ([tuv0]
;;    [let tsuv
;;      (cCoIAvcSatCoICl clft tuv0 clft crht tuv0 crht crht tuv0)
;;      (clft crht tsuv pair InR(clft tsuv pair crht crht tsuv))])

(animate "Id") ;needed for add-sound since let is present
(add-sound "CoIAvcToCoI")
;; ok, CoIAvcToCoISound has been added as a new theorem:

;; allnc z,tuv^(
;;  (ExRTMR int
;;    sdtwo yprod ai yprod ai
;;    (cterm (i,tuv^0) 
;;    (ExRTMR rea
;;      sdtwo yprod ai yprod ai
;;      (cterm (x,tuv^1) 
;;      (ExRTMR rea
;;        sdtwo yprod ai yprod ai
;;        (cterm (y,tuv^2) 
;;        (AndDMR (cterm (t^) SdtwoMR i t^)
;;          (cterm ((ai yprod ai)^) 
;;          (AndDMR (cterm (u^) CoIMR x u^)
;;            (cterm (u^) 
;;           (AndLMR (cterm (u^0) CoIMR y u^0) (cterm () z===(1#4)*(x+y+i)))u^))
;;          (ai yprod ai)^))
;;        tuv^2))
;;      tuv^1))
;;    tuv^0))
;;  tuv^ -> 
;;  CoIMR z(cCoIAvcToCoI tuv^))

;; with computation rule

;; cCoIAvcToCoI eqd
;; ([tuv]
;;   (CoRec sdtwo yprod ai yprod ai=>ai)tuv
;;   ([tuv0]
;;     clft crht(cCoIAvcSatCoICl clft tuv0 clft crht tuv0 crht crht tuv0)pair
;;     (InR (sdtwo yprod ai yprod ai) ai)
;;     (clft(cCoIAvcSatCoICl clft tuv0 clft crht tuv0 crht crht tuv0)pair 
;;      crht crht(cCoIAvcSatCoICl clft tuv0 clft crht tuv0 crht crht tuv0))))

;; (cp)

(deanimate "CoIAvcToCoI")
(deanimate "Id")

;; CoIAverage
(set-goal "allnc x,y(CoI x -> CoI y -> CoI((1#2)*(x+y)))")
(assume "x" "y" "CoIx" "CoIy")
(cut "exr i,x0,y0(Sdtwo i andd 
                  CoI x0 andd CoI y0 andl (1#2)*(x+y)===(1#4)*(x0+y0+i))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "CoIAvToAvcInst")
(by-assume "CoIAvToAvcInst" "i" "iProp")
(by-assume "iProp" "x1" "ix1Prop")
(by-assume "ix1Prop" "y1" "ix1y1Prop")
(use "CoIAvcToCoI")
(intro 0 (pt "i"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "ix1y1Prop")
(split)
(use "ix1y1Prop")
(split)
(use "ix1y1Prop")
(use "ix1y1Prop")
;; Now prove the formula cut in above
(use-with "CoIAvToAvc" (pt "x") (pt "y") "CoIx" "CoIy")
;; Proof finished.
;; (cdp)
(save "CoIAverage")

(define CoIAverage-eterm (proof-to-extracted-term))
(define CoIAverage-neterm (rename-variables (nt CoIAverage-eterm)))
;; (pp CoIAverage-neterm)

;; [u,u0](cId sdtwo yprod ai yprod ai=>ai)cCoIAvcToCoI(cCoIAvToAvc u u0)

(animate "CoIAvcToCoI")
(animate "CoIAvToAvc")
(animate "CoIAvcSatCoICl")
(animate "CoIAvcSatCoIClAuxJ")
(animate "CoIAvcSatCoIClAuxK")
(animate "IntPlusSdToSdtwo")

(define CoIAverage-neterm (rename-variables (nt CoIAverage-eterm)))
;; (ppc CoIAverage-neterm)

;; [u,u0]
;;  [let tuv
;;    (IntToSdtwo(SdToInt clft(cCoIClosure u)+SdToInt clft(cCoIClosure u0))pair 
;;    crht(cCoIClosure u)pair crht(cCoIClosure u0))
;;    ((CoRec sdtwo yprod ai yprod ai=>ai)tuv
;;    ([tuv0]
;;      [let tsuv
;;        (IntToSdtwo
;;        (J
;;         (SdToInt clft(cCoIClosure clft crht tuv0)+
;;          SdToInt clft(cCoIClosure crht crht tuv0)+
;;          SdtwoToInt clft tuv0*2))pair 
;;        IntToSd
;;        (K
;;         (SdToInt clft(cCoIClosure clft crht tuv0)+
;;          SdToInt clft(cCoIClosure crht crht tuv0)+
;;          SdtwoToInt clft tuv0*2))pair 
;;        crht(cCoIClosure clft crht tuv0)pair crht(cCoIClosure crht crht tuv0))
;;        (clft crht tsuv pair InR(clft tsuv pair crht crht tsuv))]))]

(deanimate "CoIAvcToCoI")
(deanimate "CoIAvToAvc")
(deanimate "CoIAvcSatCoICl")
(deanimate "CoIAvcSatCoIClAuxJ")
(deanimate "CoIAvcSatCoIClAuxK")
(deanimate "IntPlusSdToSdtwo")

;; To check which program constants are animated evaluate
;; (display-animation)

;; (remove-theorem "CoIAverageSound")
(animate "Id") ;since let appears
(animate "Lft")
(animate "Rht")

(add-sound "CoIAverage")
;; ok, CoIAverageSound has been added as a new theorem:

;; allnc x,y,u^(
;;  CoIMR x u^ -> 
;;  allnc u^0(CoIMR y u^0 -> CoIMR((1#2)*(x+y))(cCoIAverage u^ u^0)))

;; with computation rule

;; cCoIAverage eqd
;; ([u,u0]
;;   cCoIAvcToCoI
;;   ([if (cCoIAvToAvc u u0) ([t,uv]t)]pair
;;    [if (cCoIAvToAvc u u0) ([t,uv][if uv ([u1,u2]u1)])]pair
;;    [if (cCoIAvToAvc u u0) ([t,uv][if uv ([u1,u2]u2)])]))

;; (cp)

(deanimate "CoIAverage")
(deanimate "Id")
(deanimate "Lft")
(deanimate "Rht")

