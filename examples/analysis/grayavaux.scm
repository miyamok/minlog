;; 2020-12-16.  examples/analysis/grayavaux.scm.

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (libload "str.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (remove-var-name "x" "y" "z")
;; (libload "rea.scm")
;; ;; (set! COMMENT-FLAG #t)

;; (load "~/git/minlog/examples/analysis/JK.scm")
;; (load "~/git/minlog/examples/analysis/digits.scm")
;; (load "~/git/minlog/examples/analysis/sdcode.scm")
;; (load "~/git/minlog/examples/analysis/graycode.scm")

(display "loading grayavaux.scm ...") (newline)

;; CoGAvAvcAux
(set-goal "all x,y,d,e(Real x -> Real y ->
 (1#2)*((1#2)*(x+IntN 1)* ~d+(1#2)*(y+IntN 1)* ~e)===
 (1#4)*(x* ~d+y* ~e+(d+e)))")
(assert "all x,y,d,e
 (1#2)*((1#2)*(x+IntN 1)* ~d+(1#2)*(y+IntN 1)* ~e)=+=
 (1#4)*(x* ~d+y* ~e+(d+e))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "d" "e")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?^10:(1#2)*((1#2)*(as n+IntN 1)* ~d+(1#2)*(bs n+IntN 1)* ~e)==
;;      (1#4)*(as n* ~d+bs n* ~e+(d+e))
(use "RatEqvTrans"
     (pt "(1#2)*((1#2)*((as n+IntN 1)* ~d)+(1#2)*((bs n+IntN 1)* ~e))"))
(use "RatTimesCompat")
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
;; ?^12:(1#2)*((1#2)*((as n+IntN 1)* ~d)+(1#2)*((bs n+IntN 1)* ~e))==
;;      (1#4)*(as n* ~d+bs n* ~e+(d+e))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(ng)
;; ~((as n+IntN 1)*d)+ ~((bs n+IntN 1)*e)== ~(as n*d)+ ~(bs n*e)+(d+e)
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "IntTimesIntNL")
(simp "IntTimesIntNL")
(ng)
(simp (pf "d+e=RatPlus d e"))
(simp "<-" "RatPlus2RewRule")
(simp "<-" "RatPlus2RewRule")
(simp "<-" "RatPlus2RewRule")
(simp "RatEqv4RewRule")
(simp "RatPlusAssoc")
(simp "RatPlusAssoc")
(simp "RatEqv3RewRule")
(simprat "RatEqvSym")
(use "Truth")
(simp "RatPlusComm")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "CoGAvAvcAuxEqS" "x" "y" "d" "e" "Rx" "Ry")
(use "RealEqSToEq")
(autoreal)
(use "CoGAvAvcAuxEqS")
;; Proof finished.
;; (cdp)
(save "CoGAvAvcAux")

;; CoGAvAvcPsdMid
(set-goal "all x,y,d(Real x -> Real y -> 
 (1#2)*((1#2)*(x+IntN 1)* ~d+(1#2)*y)===(1#4)*(x* ~d+y+d))")
(assert "all x,y,d
 (1#2)*((1#2)*(x+IntN 1)* ~d+(1#2)*y)=+=(1#4)*(x* ~d+y+d)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "d")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?^10:(1#2)*((1#2)*(as n+IntN 1)* ~d+(1#2)*bs n)==(1#4)*(as n* ~d+bs n+d)
(use "RatEqvTrans" (pt "(1#2)*((1#2)*((as n+IntN 1)* ~d)+(1#2)*bs n)"))
(use "RatTimesCompat")
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
;; ?^12:(1#2)*((1#2)*((as n+IntN 1)* ~d)+(1#2)*bs n)==(1#4)*(as n* ~d+bs n+d)
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(ng)
;; ?^19:~((as n+IntN 1)*d)+bs n== ~(as n*d)+bs n+d
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "IntTimesIntNL")
(ng)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp (pf "d+bs n=bs n+d"))
(use "Truth")
(use "RatPlusComm")
;; Assertion proved.
(assume "CoGAvAvcPsdMidEqS" "x" "y" "d" "Rx" "Ry")
(use "RealEqSToEq")
(autoreal)
(use "CoGAvAvcPsdMidEqS")
;; Proof finished.
;; (cdp)
(save "CoGAvAvcPsdMid")

;; CoGAvAvcMidPsd
(set-goal "all x,y,e(Real x -> Real y ->
 (1#2)*((1#2)*x+(1#2)*(y+IntN 1)* ~e)===(1#4)*(x+y* ~e+e))")
(assert "all x,y,e
 (1#2)*((1#2)*x+(1#2)*(y+IntN 1)* ~e)=+=(1#4)*(x+y* ~e+e)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "e")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?^10:(1#2)*((1#2)*as n+(1#2)*(bs n+IntN 1)* ~e)==(1#4)*(as n+bs n* ~e+e)
(use "RatEqvTrans" (pt "(1#2)*((1#2)*as n+(1#2)*((bs n+IntN 1)* ~e))"))
(use "Truth")
(simprat "<-" "RatTimesPlusDistr")
(ng)
(simp "<-" "RatPlusAssoc")
(simp "RatEqv4RewRule")
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "IntTimesIntNL")
(use "Truth")
;; Assertion proved
(assume "CoGAvAvcMidPsdEqS" "x" "y" "e" "Rx" "Ry")
(use "RealEqSToEq")
(autoreal)
(use "CoGAvAvcMidPsdEqS")
;; Proof finished.
;; (cdp)
(save "CoGAvAvcMidPsd")

;; CoGAvAvcMidMid
(set-goal "all x,y(Real x -> Real y ->
 (1#2)*((1#2)*x+(1#2)*y)===(1#4)*(x+y+0))")
(assert "all x,y (1#2)*((1#2)*x+(1#2)*y)=+=(1#4)*(x+y+0)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?^10:(1#2)*((1#2)*as n+(1#2)*bs n)==(1#4)*(as n+bs n)
(simprat "<-" "RatTimesPlusDistr")
(use "Truth")
;; Assertion proved.
(assume "CoGAvAvcMidMidEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(autoreal)
(use "CoGAvAvcMidMidEqS")
;; Proof finished.
;; (cdp)
(save "CoGAvAvcMidMid")

;; CoGAvToAvc
(set-goal "allnc x,y(CoG x -> CoG y -> 
 exr i,x1,y1(Sdtwo i andi CoG x1 andi CoG y1 andi
 (1#2)*(x+y)===(1#4)*(x1+y1+i)))")
(assume "x" "y" "CoGx" "CoGy")
(inst-with-to "CoGClosure" (pt "x") "CoGx" "xCases")
(elim "xCases")
(drop "xCases")

;; Case LRx
(assume "ExHypx")
(by-assume "ExHypx" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")

;; We distinguish cases on CoG y
(inst-with-to "CoGClosure" (pt "y") "CoGy" "yCases")
(elim "yCases")
(drop "yCases")

;; Subcase LRx, LRy
(assume "ExHypy")
(by-assume "ExHypy" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(intro 0 (pt "d+e"))
(intro 0 (pt "x1* ~d"))
(intro 0 (pt "y1* ~e"))
(split)
(use "IntPlusPsdToSdtwo")
(use "dx1Prop")
(use "ey1Prop")
(split)
(use "CoGPsdTimes")
(use "dx1Prop")
(use "PsdUMinus")
(use "dx1Prop")
(split)
(use "CoGPsdTimes")
(use "ey1Prop")
(use "PsdUMinus")
(use "ey1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?^40:(1#2)*(x+y)===(1#4)*(x1* ~d+y1* ~e+(d+e))
;; Before being able to use CoGAvAvcAux we need compatibilities.
(use "RealEqTrans" (pt "(1#2)*((1#2)*(x1+IntN 1)* ~d+(1#2)*(y1+IntN 1)* ~e)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "dx1Prop")
(use "ey1Prop")
(use "CoGAvAvcAux")
(use "CoGToReal")
(use "dx1Prop")
(use "CoGToReal")
(use "ey1Prop")
;; 18
(drop "yCases")

;; Case LRx,Midy
(assume "ExHypy")
(by-assume "ExHypy" "y1" "y1Prop")
(intro 0 (pt "d"))
(intro 0 (pt "x1* ~d"))
(intro 0 (pt "y1"))
(split)
(use "PsdToSdtwo")
(use "dx1Prop")
(split)
(use "CoGPsdTimes")
(use "dx1Prop")
(use "PsdUMinus")
(use "dx1Prop")
(split)
(use "CoHToCoG")
(use "y1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?^72:(1#2)*(x+y)===(1#4)*(x1* ~d+y1+d)
(use "RealEqTrans" (pt "(1#2)*((1#2)*(x1+IntN 1)* ~d+y)")) 
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "dx1Prop")
(use "RealEqRefl")
(use "CoGToReal")
(use "CoGy")
(use "RealEqTrans" (pt "(1#2)*((1#2)*(x1+IntN 1)* ~d+(1#2)*y1)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealEqRefl")
(use "RealTimesReal")
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "CoGToReal")
(use "dx1Prop")
(use "RealRat")
(use "RealRat")
(use "y1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?^84:(1#2)*((1#2)*(x1+IntN 1)* ~d+(1#2)*y1)===(1#4)*(x1* ~d+y1+d)
(use "CoGAvAvcPsdMid")
(use "CoGToReal")
(use "dx1Prop")
(use "CoHToReal")
(use "y1Prop")
;; 6 Case Midx
(assume "ExHypx")
(by-assume "ExHypx" "x1" "x1Prop")

;; We distinguish cases on CoG y
(inst-with-to "CoGClosure" (pt "y") "CoGy" "yCases")
(elim "yCases")
(drop "yCases")

;; Subcase Midx, LRy
(assume "ExHypy")
(by-assume "ExHypy" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(intro 0 (pt "e"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1* ~e"))
(split)
(use "PsdToSdtwo")
(use "ey1Prop")
(split)
(use "CoHToCoG")
(use "x1Prop")
(split)
(use "CoGPsdTimes")
(use "ey1Prop")
(use "PsdUMinus")
(use "ey1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?^128:(1#2)*(x+y)===(1#4)*(x1+y1* ~e+e)
(use "RealEqTrans" (pt "(1#2)*((1#2)*x1+y)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "x1Prop")
(use "RealEqRefl")
(use "CoGToReal")
(use "CoGy")
(use "RealEqTrans" (pt "(1#2)*((1#2)*x1+(1#2)*(y1+IntN 1)* ~e)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealEqRefl")
(use "RealTimesReal")
(use "RealRat")
(use "CoHToReal")
(use "x1Prop")
(use "ey1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?^142:(1#2)*((1#2)*x1+(1#2)*(y1+IntN 1)* ~e)===(1#4)*(x1+y1* ~e+e)
(use  "CoGAvAvcMidPsd")
(use "CoHToReal")
(use "x1Prop")
(use "CoGToReal")
(use "ey1Prop")

;; Subcase Midx, Midy
(assume "ExHypy")
(drop "yCases")
(by-assume "ExHypy" "y1" "y1Prop")
(intro 0 (pt "0"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "InitSdtwoMT")
(split)
(use "CoHToCoG")
(use "x1Prop")
(split)
(use "CoHToCoG")
(use "y1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?^170:(1#2)*(x+y)===(1#4)*(x1+y1+0)
(use "RealEqTrans" (pt "(1#2)*((1#2)*x1+y)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "x1Prop")
(use "RealEqRefl")
(use "CoGToReal")
(use "CoGy")
(use "RealEqTrans" (pt "(1#2)*((1#2)*x1+(1#2)*y1)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealEqRefl")
(use "RealTimesReal")
(use "RealRat")
(use "CoHToReal")
(use "x1Prop")
(use "y1Prop")
(use "CoGAvAvcMidMid")
(use "CoHToReal")
(use "x1Prop")
(use "CoHToReal")
(use "y1Prop")
;; Proof finished.
;; (cdp)
(save "CoGAvToAvc")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag,ag0][case (DesYprod ag)
;;    (InL bg -> [case (DesYprod ag0)
;;      (InL bg0 -> 
;;      cIntPlusPsdToSdtwo clft bg clft bg0 pair 
;;      cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair 
;;      cCoGPsdTimes crht bg0(cPsdUMinus clft bg0))
;;      (InR ah -> 
;;      cPsdToSdtwo clft bg pair 
;;      cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair cCoHToCoG ah)])
;;    (InR ah -> [case (DesYprod ag0)
;;      (InL bg -> 
;;      cPsdToSdtwo clft bg pair 
;;      cCoHToCoG ah pair cCoGPsdTimes crht bg(cPsdUMinus clft bg))
;;      (InR ah0 -> MT pair cCoHToCoG ah pair cCoHToCoG ah0)])]

(deanimate "CoGClosure")

;; CoGAvUMinus
(set-goal "all d,x(Real x -> (1#2)*(x+IntN 1)* ~d===(1#2)*(x* ~d+d))")
(assume "d" "x" "Rx")
(use "RealEqTrans" (pt "(1#2)*((x+IntN 1)* ~d)"))
(use "RealEqSym")
(use "RealTimesAssoc")
(use "RealRat")
(use "RealPlusReal")
(use "Rx")
(use "RealRat")
(use "RealRat")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealTimesPlusIntNOneDistrLeft")
(use "Rx")
;; Proof finished.
;; (cdp)
(save "CoGAvUMinus")

;; We now need JK.scm

;; SdDisj
(set-goal "allnc d(Sd d -> d=0 orr Psd d)")
(assume "d" "Sdd")
(elim "Sdd")
;; 3-5
(intro 1)
(use "InitPsdTrue")
;; 4
(intro 0)
(use "Truth")
;; 5
(intro 1)
(use "InitPsdFalse")
;; Proof finished.
(save "SdDisj")

;; To avoid case lengthy distinctions and achieve some clarity in the
;; usage of J,K we could employ IntToBoole, BooleToInt, PsdInj and
;; invariance axioms.  However, in the present simple case the latter
;; are easily provable.

;; CoGAvcSatCoIClAuxJ
(set-goal "allnc d,e,i(Psd d -> Psd e -> Sdtwo i -> Sdtwo(J(d+e+i*2)))")
(assume "d" "e" "i" "Psdd" "Psde" "Sdtwoi")
(assert "exl boole1 PsdInj d boole1")
(use "PsdInjIntro")
(use "Psdd")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")
(assert "exl boole2 PsdInj e boole2")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")
(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdtwoInjElim"
 (pt "IntToSdtwo(J(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2))"))
(simp (pf "J(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2)=J(d+e+i*2)"))
(use "SdtwoInjIntToSdtwo")
;; ?^27:abs(J(d+e+i*2))<=2
(use "JProp")
(simp (pf "BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2=d+e+i*2"))
(use "Truth")
;; ?^29:BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2=d+e+i*2
(inst-with-to "PsdInjId" (pt "d") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "e") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
(save "CoGAvcSatCoIClAuxJ")

;; CoGAvcSatCoIClAuxK
(set-goal "allnc d,e,i(Psd d -> Psd e -> Sdtwo i -> Sd(K(d+e+i*2)))")
(assume "d" "e" "i" "Psdd" "Psde" "Sdtwoi")
(assert "exl boole1 PsdInj d boole1")
(use "PsdInjIntro")
(use "Psdd")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")
(assert "exl boole2 PsdInj e boole2")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")
(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdInjElim"
     (pt "IntToSd(K(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2))"))
(simp (pf "K(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2)=K(d+e+i*2)"))
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
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd")
(simp "PsdToAbsOne")
(use "Truth")
(use "Psde")
(use "Truth")
(ng #t)
(use "IntLeTrans" (pt "IntP 2*IntP 2"))
(use "IntLeMonTimes")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(use "Truth")
(simp (pf "BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2=d+e+i*2"))
(use "Truth")
;; ?^52:BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2=d+e+i*2
(inst-with-to "PsdInjId" (pt "d") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "e") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
(save "CoGAvcSatCoIClAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [boole,boole0,t]
;;  IntToSd(K(BooleToInt boole+BooleToInt boole0+SdtwoToInt t*2))

;; SdtwoPsdToSdtwoJ
(set-goal "allnc i,d(Sdtwo i -> Psd d -> Sdtwo(J(d+i*2)))")
(assume "i" "d" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(assume "Psdd")
(elim "Psdd")
;; 9,10
(ng)
(use "InitSdtwoLT")
;; 10
(ng)
(use "InitSdtwoRT")
;; 4
(assume "Psdd")
(elim "Psdd")
;; 14,15
(ng)
(use "InitSdtwoRT")
;; 15
(ng)
(use "InitSdtwoLT")
;; 5
(assume "Psdd")
(elim "Psdd")
;; 19,20
(ng)
(use "InitSdtwoRT")
; 20
(ng)
(use "InitSdtwoLT")
;; 6
(assume "Psdd")
(elim "Psdd")
;; 24,25
(ng)
(use "InitSdtwoLT")
;; 25
(ng)
(use "InitSdtwoRT")
;; 7
(assume "Psdd")
(elim "Psdd")
;; 29,30
(ng)
(use "InitSdtwoRT")
;; 30
(ng)
(use "InitSdtwoLT")
;; Proof finished.
(save "SdtwoPsdToSdtwoJ")

;; SdtwoToSdtwoJ
(set-goal "allnc i(Sdtwo i -> Sdtwo(J(i*2)))")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(ng)
(use "InitSdtwoRR")
;; 4
(ng)
(use "InitSdtwoMT")
;; 5
(ng)
(use "InitSdtwoMT")
;; 6
(ng)
(use "InitSdtwoLL")
;; 7
(ng)
(use "InitSdtwoMT")
;; Proof finished.
(save "SdtwoToSdtwoJ")

;; SdtwoPsdToSdK
(set-goal "allnc i,d(Sdtwo i -> Psd d -> Sd(K(d+i*2)))")
(assume "i" "d" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(assume "Psdd")
(elim "Psdd")
;; 9,10
(ng)
(use "InitSdSdR")
;; 10
(ng)
(use "InitSdSdM")
;; 4
(assume "Psdd")
(elim "Psdd")
;; 14,15
(ng)
(use "InitSdSdR")
;; 15
(ng)
(use "InitSdSdR")
;; 5
(assume "Psdd")
(elim "Psdd")
;; 19,20
(ng)
(use "InitSdSdM")
; 20
(ng)
(use "InitSdSdM")
;; 6
(assume "Psdd")
(elim "Psdd")
;; 24,25
(ng)
(use "InitSdSdM")
;; 25
(ng)
(use "InitSdSdL")
;; 7
(assume "Psdd")
(elim "Psdd")
;; 29,30
(ng)
(use "InitSdSdL")
;; 30
(ng)
(use "InitSdSdL")
;; Proof finished.
(save "SdtwoPsdToSdK")

;; SdtwoToSdK
(set-goal "allnc i(Sdtwo i -> Sd(K(i*2)))")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(ng)
(use "InitSdSdM")
;; 4
(ng)
(use "InitSdSdR")
;; 5
(ng)
(use "InitSdSdM")
;; 6
(ng)
(use "InitSdSdM")
;; 7
(ng)
(use "InitSdSdL")
;; Proof finished.
(save "SdtwoToSdK")

;; CoIAvcSatCoIClAux 
(set-goal "all x,y,d,e,i(Real x -> Real y ->
 (1#4)*((1#2)*(x+d)+(1#2)*(y+e)+i)===
 (1#2)*((1#4)*(x+y+J(d+e+i*2))+K(d+e+i*2)))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "d" "e" "i" "Rx" "Ry")
(use "RealSeqEqToEq" (pt "Zero"))
;; 6-8
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "RealPlusReal")
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "Rx")
(use "RealRat")
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "Ry")
(use "RealRat")
(use "RealRat")
;; 9
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "RealPlusReal")
(use "Rx")
(use "Ry")
(use "RealRat")
(use "RealRat")
;; 10
(assume "n" "Useless")
(ng)
;;   n
;; -----------------------------------------------------------------------------
;; ?^34:(1#4)*((1#2)*(as n+d)+(1#2)*(bs n+e)+i)==
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
;; ?^46:(1#8)*as n+(d#8)+(1#8)*bs n+(e#8)+(i#4)==
;;      (1#8)*as n+(1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2)
(assert "(1#8)*as n+(d#8)+(1#8)*bs n+(e#8)+(i#4)=
         (1#8)*as n+((d#8)+(1#8)*bs n+(e#8)+(i#4))")
 (ng)
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(drop "EqHyp1")
(assert "(1#8)*as n+(1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2)==
         (1#8)*as n+((1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2))")
 (ng)
 (use "Truth")
(assume "EqvHyp2")
(simprat "EqvHyp2")
(drop "EqvHyp2")
(use "RatPlusCompat")
(use "Truth")
(assert "(d#8)+(1#8)*bs n=(1#8)*bs n+(d#8)")
 (use "RatPlusComm")
(assume "EqHyp3")
(simp "EqHyp3")
(drop "EqHyp3")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?^70:(d#8)+((e#8)+(i#4))==(J(d+e+i*2)#8)+(K(d+e+i*2)#2)
(assert "(i#4)==(i*2#8)")
 (ng)
 (simp "<-" "IntTimesAssoc")
 (use "Truth")
(assume "EqvHyp4")
(simprat "EqvHyp4")
(drop "EqvHyp4")
(assert "(K(d+e+i*2)#2)==(K(d+e+i*2)*4#8)")
 (ng)
 (simp "<-" "IntTimesAssoc")
 (use "Truth")
(assume "EqvHyp5")
(simprat "EqvHyp5")
(drop "EqvHyp5")
;; ?^84:(d#8)+((e#8)+(i*2#8))==(J(d+e+i*2)#8)+(K(d+e+i*2)*4#8)
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(assert "all k k=J k+K k*4")
 (assume "k")
 (simp "IntPlusComm")
 (use "KJProp")
(assume "JKProp")
(simp "<-" "JKProp")
(ng)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "CoIAvcSatCoIClAux")

;; CoGAvcSatCoICl
(set-goal "allnc i,x,y(Sdtwo i -> CoG x -> CoG y -> 
 exr j,d,x0,y0(Sdtwo j andi Sd d andi CoG x0 andi CoG y0 andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d)))")
(assume "i" "x" "y" "Sdtwoi" "CoGx" "CoGy")
(inst-with-to "CoGClosure" (pt "x") "CoGx" "CoGClosureInstx")
(elim "CoGClosureInstx")
;; 5,6
(drop "CoGClosureInstx")
(assume "CoGClosureInstxLeft")
(by-assume "CoGClosureInstxLeft" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(inst-with-to "CoGClosure" (pt "y") "CoGy" "CoGClosureInsty")
(elim "CoGClosureInsty")
;; 17,18
(drop "CoGClosureInsty")
(assume "CoGClosureInstyLeft")
(by-assume "CoGClosureInstyLeft" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(intro 0 (pt "J(d+e+i*2)"))
(intro 0 (pt "K(d+e+i*2)"))
(intro 0 (pt "x1* ~d"))
(intro 0 (pt "y1* ~e"))
(split)
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?_31:Sdtwo(J(d+e+i*2))
(use "CoGAvcSatCoIClAuxJ")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
;; same for K
(use "CoGAvcSatCoIClAuxK")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
(use "CoGPsdTimes")
(use "dx1Prop")
(use "PsdUMinus")
(use "dx1Prop")
(split)
(use "CoGPsdTimes")
(use "ey1Prop")
(use "PsdUMinus")
(use "ey1Prop")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?^47:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1* ~d+y1* ~e+J(d+e+i*2))+K(d+e+i*2))
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1* ~d+d)+(1#2)*(y1* ~e+e)+i)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqTrans" (pt "(1#2)*(x1+IntN 1)* ~d"))
(use "dx1Prop")
(use "CoGAvUMinus")
(use "CoGToReal")
(use "dx1Prop")
(use "RealEqTrans" (pt "(1#2)*(y1+IntN 1)* ~e"))
(use "ey1Prop")
(use "CoGAvUMinus")
(use "CoGToReal")
(use "ey1Prop")
(use "RealEqRefl")
(use "RealRat")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?^52:(1#4)*((1#2)*(x1* ~d+d)+(1#2)*(y1* ~e+e)+i)===
;;      (1#2)*((1#4)*(x1* ~d+y1* ~e+J(d+e+i*2))+K(d+e+i*2))
(use "CoIAvcSatCoIClAux")
(use "RealTimesReal")
(use "CoGToReal")
(use "dx1Prop")
(use "RealRat")
(use "RealTimesReal")
(use "CoGToReal")
(use "ey1Prop")
(use "RealRat")
;; 18
(drop "CoGClosureInsty")
(assume "CoGClosureInstyRight")
(by-assume "CoGClosureInstyRight" "y1" "y1Prop")
(intro 0 (pt "J(d+i*2)"))
(intro 0 (pt "K(d+i*2)"))
(intro 0 (pt "x1* ~d"))
(intro 0 (pt "y1"))
(split)
;; ?_86:Sdtwo(J(d+i*2))
(use "SdtwoPsdToSdtwoJ")
(use "Sdtwoi")
(use "dx1Prop")
(split)
;; ?_90:Sd(K(d+i*2))
(use "SdtwoPsdToSdK")
(use "Sdtwoi")
(use "dx1Prop")
(split)
(use "CoGPsdTimes")
(use "dx1Prop")
(use "PsdUMinus")
(use "dx1Prop")
(split)
(use "CoHToCoG")
(use "y1Prop")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?^100:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1* ~d+y1+J(d+i*2))+K(d+i*2))

;; We had CoIAvcSatCoIClAux
;; "all x,y,d,e,i(Real x -> Real y ->
;;  (1#4)*((1#2)*(x+d)+(1#2)*(y+e)+i)===
;;  (1#2)*((1#4)*(x+y+J(d+e+i*2))+K(d+e+i*2)))"
;; Strategy for uses of CoIAvcSatCoIClAux : using RealEqTrans bring
;; the goal in in the form required by CoIAvcSatCoIClAux .  Then use
;; CoGAvUMinus and RealPlusZero to prove the rest.
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1* ~d+d)+(1#2)*(y1+0)+i)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqTrans" (pt "(1#2)*(x1+IntN 1)* ~d"))
(use "dx1Prop")
(use "CoGAvUMinus")
(use "CoGToReal")
(use "dx1Prop")
(use "RealEqTrans" (pt "(1#2)*y1"))
(use "y1Prop")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqSym")
(use "RealPlusZero")
(use "CoHToReal")
(use "y1Prop")
(use "RealEqRefl")
(use "RealRat")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?^103:(1#4)*((1#2)*(x1* ~d+d)+(1#2)*(y1+0)+i)===
;;       (1#2)*((1#4)*(x1* ~d+y1+J(d+i*2))+K(d+i*2))
(use-with "CoIAvcSatCoIClAux" (pt "x1* ~d") (pt "y1") (pt "d")
	  (pt "0") (pt "i") "?" "?")
(use "RealTimesReal")
(use "CoGToReal")
(use "dx1Prop")
(use "RealRat")
(use "CoHToReal")
(use "y1Prop")
;; 6
(drop "CoGClosureInstx")
(assume "CoGClosureInstxRight")
(by-assume "CoGClosureInstxRight" "x1" "x1Prop")
(inst-with-to "CoGClosure" (pt "y") "CoGy" "CoGClosureInsty")
(elim "CoGClosureInsty")
;; 137,138
(drop "CoGClosureInsty")
(assume "CoGClosureInstyLeft")
(by-assume "CoGClosureInstyLeft" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(intro 0 (pt "J(e+i*2)"))
(intro 0 (pt "K(e+i*2)"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1* ~e"))
(split)
;; ?_151:Sdtwo(J(e+i*2))
(use "SdtwoPsdToSdtwoJ")
(use "Sdtwoi")
(use "ey1Prop")
(split)
;; ?_155:Sd(K(e+i*2))
(use "SdtwoPsdToSdK")
(use "Sdtwoi")
(use "ey1Prop")
(split)
(use "CoHToCoG")
(use "x1Prop")
(split)
(use "CoGPsdTimes")
(use "ey1Prop")
(use "PsdUMinus")
(use "ey1Prop")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?^163:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1* ~e+J(e+i*2))+K(e+i*2))
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1+0)+(1#2)*(y1* ~e+e)+i)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqTrans" (pt "(1#2)*x1"))
(use "x1Prop")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqSym")
(use "RealPlusZero")
(use "CoHToReal")
(use "x1Prop")
(use "RealEqTrans" (pt "(1#2)*(y1+IntN 1)* ~e"))
(use "ey1Prop")
(use "CoGAvUMinus")
(use "CoGToReal")
(use "ey1Prop")
(use "RealEqRefl")
(use "RealRat")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?^168:(1#4)*((1#2)*(x1+0)+(1#2)*(y1* ~e+e)+i)===
;;       (1#2)*((1#4)*(x1+y1* ~e+J(e+i*2))+K(e+i*2))

(use-with "CoIAvcSatCoIClAux" (pt "x1") (pt "y1* ~e") (pt "0")
	  (pt "e") (pt "i") "?" "?")
(use "CoHToReal")
(use "x1Prop")
(use "RealTimesReal")
(use "CoGToReal")
(use "ey1Prop")
(use "RealRat")
;; 138
(drop "CoGClosureInsty")
(assume  "CoGClosureInstyRight")
(by-assume  "CoGClosureInstyRight" "y1" "y1Prop")
(intro 0 (pt "J(i*2)"))
(intro 0 (pt "K(i*2)"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
;; ?_204:Sdtwo(J(i*2))
(use "SdtwoToSdtwoJ")
(use "Sdtwoi")
(split)
;; ?_207:Sd(K(i*2))
(use "SdtwoToSdK")
(use "Sdtwoi")
(split)
(use "CoHToCoG")
(use "x1Prop")
(split)
(use "CoHToCoG")
(use "y1Prop")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?^214:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+J(i*2))+K(i*2))
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1+0)+(1#2)*(y1+0)+i)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqTrans" (pt "(1#2)*x1"))
(use "x1Prop")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqSym")
(use "RealPlusZero")
(use "CoHToReal")
(use "x1Prop")
(use "RealEqTrans" (pt "(1#2)*y1"))
(use "y1Prop")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqSym")
(use "RealPlusZero")
(use "CoHToReal")
(use "y1Prop")
(use "RealEqRefl")
(use "RealRat")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; 217:(1#4)*((1#2)*(x1+0)+(1#2)*(y1+0)+i)===(1#2)*((1#4)*(x1+y1+J(i*2))+K(i*2))

(use-with "CoIAvcSatCoIClAux"  (pt "x1") (pt "y1") (pt "0") (pt "0") (pt "i")
	  "?" "?")
(use "CoHToReal")
(use "x1Prop")
(use "CoHToReal")
(use "y1Prop")
;; Proof finished.
;; (cdp)
(save "CoGAvcSatCoICl")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(animate "CoGAvcSatCoIClAuxJ")
(animate "CoGAvcSatCoIClAuxK")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,ag,ag0][case (DesYprod ag)
;;    (InL bg -> [case (DesYprod ag0)
;;      (InL bg0 -> IntToSdtwo(J(BooleToInt clft bg+
;;                               BooleToInt clft bg0+
;;                               SdtwoToInt t*2))pair 
;;                  IntToSd(K(BooleToInt clft bg+
;;                            BooleToInt clft bg0+
;;                            SdtwoToInt t*2))pair 
;;      cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair 
;;      cCoGPsdTimes crht bg0(cPsdUMinus clft bg0))
;;      (InR ah -> cSdtwoPsdToSdtwoJ t clft bg pair 
;;                 cSdtwoPsdToSdK t clft bg pair 
;;                 cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair
;;                 cCoHToCoG ah)])
;;    (InR ah -> [case (DesYprod ag0)
;;      (InL bg -> cSdtwoPsdToSdtwoJ t clft bg pair 
;;                 cSdtwoPsdToSdK t clft bg pair 
;;                 cCoHToCoG ah pair
;;                 cCoGPsdTimes crht bg(cPsdUMinus clft bg))
;;      (InR ah0 -> cSdtwoToSdtwoJ t pair 
;;                  cSdtwoToSdK t pair
;;                  cCoHToCoG ah pair
;;                  cCoHToCoG ah0)])]

(deanimate "CoGClosure")
(deanimate "CoGAvcSatCoIClAuxJ")
(deanimate "CoGAvcSatCoIClAuxK")

;; Putting things together

;; RealAvcBd
(set-goal "allnc x,y,i(Real x -> Real y -> abs x<<=1 -> abs y<<=1 ->abs i<=2 ->
                       abs((1#4)*(x+y+i))<<=1)")
(assume "x" "y" "i" "Rx" "Ry" "xBd" "yBd" "iBd")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "abs(RealConstr([n](1#4))([p]Zero))*
                        (RealConstr([n](1#1))([p]Zero)+1+2)"))
(use "RealLeMonTimes")
(use "RealNNegAbs")
(use "RealRat")
(use "RealLeTrans" (pt "abs(x+y)+abs(RealConstr([n]i)([p]Zero))"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "abs x+abs y"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlus")
(use "xBd")
(use "yBd")
(use "RatLeToRealLe")
(use "iBd")
(ng)
(use "RealLeRefl")
(use "RealRat")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealAvcBd")

;; CoGAvcToCoG
(set-goal "allnc z(
 exr i,x,y(Sdtwo i andi CoG x andi CoG y andi z===(1#4)*(x+y+i)) -> CoG z)")
(assume "z" "Qz")
(coind "Qz" (pf "exr i,x,y
          (Sdtwo i andi CoG x andi CoG y andi z===(1#4)*(x+y+i)) -> CoH z"))
;; 3,4
(assume "z1" "Qz1")
(by-assume "Qz1" "i" "iProp")
(by-assume "iProp" "x" "ixProp")
(by-assume "ixProp" "y" "ixyProp")
;; let introduction
(cut "exr j,d,x0,y0(Sdtwo j andi Sd d andi CoG x0 andi CoG y0 andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d))")
;; 15,16
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "i1" "i1Prop")
(by-assume "i1Prop" "d1" "i1d1Prop")
(by-assume "i1d1Prop" "x1" "i1d1x1Prop")
(by-assume "i1d1x1Prop" "y1" "i1d1x1y1Prop")
(assert "Sdtwo i1")
(use "i1d1x1y1Prop")
(assume "Sdtwoi1")
(assert "CoG x1")
(use "i1d1x1y1Prop")
(assume "CoGx1")
(assert "CoG y1")
(use "i1d1x1y1Prop")
(assume "CoGy1")
(assert "(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+i1)+d1)")
(use "i1d1x1y1Prop")
(assume "Eq")
(drop "i1d1x1y1Prop")
(assert "d1=0 orr Psd d1")
 (use-with "SdDisj" (pt "d1") "?")
 (use "i1d1x1y1Prop")
(assume "Disj")
(elim "Disj")
;; 48,49
(drop "Disj")
(assume "d1=0") ;case small
(intro 1)
(intro 0 (pt "(1#4)*(x1+y1+i1)"))
(intro 0 (pt "z1"))
(split)
(autoreal)
(split)
;; ?^57:abs((1#4)*(x1+y1+i1))<<=1
(use "RealAvcBd")
(autoreal)
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy1")
(use "SdtwoBound")
(use "Sdtwoi1")
;; 58
(split)
(intro 1)
(intro 0 (pt "i1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "Sdtwoi1")
(split)
(use "CoGx1")
(split)
(use "CoGy1")
(use "RealEqRefl")
(autoreal)
(split)
(simpreal "ixyProp")
(simpreal "Eq")
;; ?^83:(1#2)*((1#4)*(x1+y1+i1)+d1)===(1#2)*((1#4)*(x1+y1+i1))
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(simp "d1=0")
(use "Truth")
;; ?^81:z1===z1
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x+y+i)"))
(use "ixyProp")
;; 49
(drop "Disj")
(assume "Psdd1")
(intro 0)
(intro 0 (pt "d1"))
(intro 0 (pt "(1#4)*(x1* ~d1+y1* ~d1+RealTimes i1~d1)"))
(intro 0 (pt "z1"))
(split)
(use "Psdd1")
(split)
(autoreal)
(split)
;; ?^109:abs((1#4)*(x1* ~d1+y1* ~d1+RealTimes i1~d1))<<=1
(simpreal "<-" "RealTimesPlusDistrLeft")
(simpreal "<-" "RealTimesPlusDistrLeft")
(simpreal "RealTimesAssoc")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealConstr([n](1#1))([p]Zero)*1"))
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(autoreal)
(use "RealNNegAbs")
(autoreal)
(use "RealAvcBd")
(autoreal)
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy1")
(use "SdtwoBound")
(use "Sdtwoi1")
(use "RatLeToRealLe")
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(use "RealLeRefl")
(use "RealRat")
(use "RealRat")
(autoreal)
;; 110
(split)
(intro 1)
(intro 0 (pt "i1* ~d1"))
(intro 0 (pt "x1* ~d1"))
(intro 0 (pt "y1* ~d1"))
(split)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "PsdUMinus")
(use "Psdd1")
;; ?^164:(1#4)*(x1* ~d1+y1* ~d1+RealTimes i1~d1)===
;;       (1#4)*(x1* ~d1+y1* ~d1+i1* ~d1)
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "Truth")
;; ?^148:z1===(1#2)*((1#4)*(x1* ~d1+y1* ~d1+RealTimes i1~d1)+IntN 1)* ~d1 andnc 
;;       z1===z1
(split)
(simpreal "ixyProp")
(simpreal "Eq")
;; ?^183:(1#2)*((1#4)*(x1+y1+i1)+d1)===
;;       (1#2)*((1#4)*(x1* ~d1+y1* ~d1+RealTimes i1~d1)+IntN 1)* ~d1
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^193:(1#2)*((1#4)*(as n+bs n+i1)+d1)== 
;;       ~((1#2)*((1#4)*(~(as n*d1)+ ~(bs n*d1)+ ~(i1*d1))+IntN 1)*d1)
(simp (pf "~(i1*d1)=RatUMinus(RatTimes i1 d1)"))
(simp (pf "(IntN 1#1)= ~(1#1)"))
(simp "<-" "RatUMinus2RewRule")
(simp "<-" "RatUMinus2RewRule")
(simp "RatTimes3RewRule")
(simp "<-" "RatUMinus2RewRule")
(simp "RatTimes3RewRule")
(simp "RatTimes4RewRule")
(simp "RatUMinus1RewRule")
;; ?^204:(1#2)*((1#4)*(as n+bs n+i1)+d1)==
;;       (1#2)*((1#4)*(as n*d1+bs n*d1+RatTimes i1 d1)+1)*d1
(simp "<-" "RatTimesAssoc")
(simp "RatEqv6RewRule")
(simprat "RatTimesPlusDistrLeft")
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp (pf "RatTimes d1 d1=d1*d1"))
(assert "allnc d(Psd d -> d*d=1)")
 (assume "d" "Psdd")
 (elim "Psdd")
 (use "Truth")
 (use "Truth")
(assume "PsdSquareOne")
(simp "PsdSquareOne")
(use "Truth")
(use "Psdd1")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?^181:z1===z1
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x+y+i)"))
(use "ixyProp")

;; ?_16:exr j,d,x0,y0(
;;       Sdtwo j andd 
;;       Sd d andd 
;;       CoG x0 andd CoG y0 andl (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d))

;; Now we prove the formula cut in above, using CoGAvcSatCoICl
(use "CoGAvcSatCoICl")
(use "ixyProp")
(use "ixyProp")
(use "ixyProp")
;; 4
(assume "z1" "Qz1")
(by-assume "Qz1" "i" "iProp")
(by-assume "iProp" "x" "ixProp")
(by-assume "ixProp" "y" "ixyProp")
;; let introduction
(cut "exr j,d,x0,y0(Sdtwo j andi Sd d andi CoG x0 andi CoG y0 andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d))")
;; 240,241
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "i1" "i1Prop")
(by-assume "i1Prop" "d1" "i1d1Prop")
(by-assume "i1d1Prop" "x1" "i1d1x1Prop")
(by-assume "i1d1x1Prop" "y1" "i1d1x1y1Prop")
(assert "Sdtwo i1")
(use "i1d1x1y1Prop")
(assume "Sdtwoi1")
(assert "CoG x1")
(use "i1d1x1y1Prop")
(assume "CoGx1")
(assert "CoG y1")
(use "i1d1x1y1Prop")
(assume "CoGy1")
(assert "(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+i1)+d1)")
(use "i1d1x1y1Prop")
(assume "Eq")
(drop "i1d1x1y1Prop")
(assert "d1=0 orr Psd d1")
 (use-with "SdDisj" (pt "d1") "?")
 (use "i1d1x1y1Prop")
(assume "Disj")
(elim "Disj")
;; 273,274
(drop "Disj")
(assume "d1=0") ;case small
(intro 1)
(intro 0 (pt "(1#4)*(x1+y1+i1)"))
(intro 0 (pt "z1"))
(split)
(autoreal)
(split)
;; ?^282:abs((1#4)*(x1+y1+i1))<<=1
(use "RealAvcBd")
(autoreal)
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy1")
(use "SdtwoBound")
(use "Sdtwoi1")
(split)
(intro 1)
(intro 0 (pt "i1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "Sdtwoi1")
(split)
(use "CoGx1")
(split)
(use "CoGy1")
(use "RealEqRefl")
(autoreal)
(split)
(simpreal "ixyProp")
(simpreal "Eq")
;; ?^308:(1#2)*((1#4)*(x1+y1+i1)+d1)===(1#2)*((1#4)*(x1+y1+i1))
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(simp "d1=0")
(use "Truth")
;; ?^306:z1===z1
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x+y+i)"))
(use "ixyProp")
;; 274
(drop "Disj")
(assume "Psdd1")
(intro 0)
(intro 0 (pt "d1"))
(intro 0 (pt "(1#4)*(x1*d1+y1*d1+RealTimes i1 d1)"))
(intro 0 (pt "z1"))
(split)
(use "Psdd1")
(split)
(autoreal)
(split)
;; ?^334:abs((1#4)*(x1*d1+y1*d1+RealTimes i1 d1))<<=1
(simpreal "<-" "RealTimesPlusDistrLeft")
(simpreal "<-" "RealTimesPlusDistrLeft")
(simpreal "RealTimesAssoc")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealConstr([n](1#1))([p]Zero)*1"))
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(autoreal)
(use "RealNNegAbs")
(autoreal)
(use "RealAvcBd")
(autoreal)
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy1")
(use "SdtwoBound")
(use "Sdtwoi1")
(use "RatLeToRealLe")
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(use "RealLeRefl")
(use "RealRat")
(use "RealRat")
(autoreal)
;; 335
(split)
(intro 1)
(intro 0 (pt "i1*d1"))
(intro 0 (pt "x1*d1"))
(intro 0 (pt "y1*d1"))
(split)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "Psdd1")
;; ?^387:(1#4)*(x1*d1+y1*d1+RealTimes i1 d1)===(1#4)*(x1*d1+y1*d1+i1*d1)
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "Truth")
;; ?^_373:z1===(1#2)*((1#4)*(x1*d1+y1*d1+RealTimes i1 d1)+1)*d1 andnc z1===z1
(split)
(simpreal "ixyProp")
(simpreal "Eq")
;; ?^405:(1#2)*((1#4)*(x1+y1+i1)+d1)===
;;       (1#2)*((1#4)*(x1*d1+y1*d1+RealTimes i1 d1)+1)*d1
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?d^_415:(1#2)*((1#4)*(as n+bs n+i1)+d1)==
;;       (1#2)*((1#4)*(as n*d1+bs n*d1+i1*d1)+1)*d1
(simp "<-" "RatTimesAssoc")
(simp "RatEqv6RewRule")
;; ?^417:(1#4)*(as n+bs n+i1)+d1==((1#4)*(as n*d1+bs n*d1+i1*d1)+1)*d1
(simprat "RatTimesPlusDistrLeft")
(simp (pf "RatTimes 1 d1=(d1#1)"))
(simp "RatEqv3RewRule")
;; ?^421:(1#4)*(as n+bs n+i1)==(1#4)*(as n*d1+bs n*d1+i1*d1)*d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(ng #t)
;; ?^427:as n+bs n+i1==as n*(d1*d1)+bs n*(d1*d1)+i1*d1*d1
(simp "<-" "IntTimesAssoc")
(assert "allnc d(Psd d -> d*d=1)")
 (assume "d" "Psdd")
 (elim "Psdd")
 (use "Truth")
 (use "Truth")
(assume "PsdSquareOne")
(simp "PsdSquareOne")
(use "Truth")
(use "Psdd1")
(use "Truth")
;; ?^403:z1===z1
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x+y+i)"))
(use "ixyProp")

;; ?_241:exr j,d,x0,y0(
;;        Sdtwo j andd 
;;        Sd d andd 
;;        CoG x0 andd CoG y0 andl (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d))

;; Now we prove the formula cut in above, using CoGAvcSatCoICl
(use "CoGAvcSatCoICl")
(use "ixyProp")
(use "ixyProp")
(use "ixyProp")
;; Proof finished.
;; (cdp)
(save "CoGAvcToCoG")

;; cCoGAvcToCoG: sdtwo yprod ag yprod ag=>ag

(define eterm (proof-to-extracted-term))
(add-var-name "gg" (py "ag yprod ag"))
(add-var-name "tgg" (py "sdtwo yprod ag yprod ag"))
(add-var-name "sgg" (py "sd yprod ag yprod ag"))
(add-var-name "tsgg" (py "sdtwo yprod sd yprod ag yprod ag"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [tgg](CoRec sdtwo yprod ag yprod ag=>ag 
;;             sdtwo yprod ag yprod ag=>ah)tgg
;;  ([tgg0][let tsgg
;;      (cCoGAvcSatCoICl clft tgg0 clft crht tgg0 crht crht tgg0)
;;      [case (cSdDisj clft crht tsgg)
;;       (DummyL -> InR(InR(clft tsgg pair crht crht tsgg)))
;;       (Inr boole -> InL(boole pair InR
;;        (cIntTimesSdtwoPsdToSdtwo clft tsgg(cPsdUMinus boole)pair 
;;         cCoGPsdTimes clft crht crht tsgg(cPsdUMinus boole)pair 
;;         cCoGPsdTimes crht crht crht tsgg(cPsdUMinus boole))))]])
;;  ([tgg0][let tsgg
;;      (cCoGAvcSatCoICl clft tgg0 clft crht tgg0 crht crht tgg0)
;;      [case (cSdDisj clft crht tsgg)
;;       (DummyL -> InR(InR(clft tsgg pair crht crht tsgg)))
;;       (Inr boole -> InL(boole pair InR
;;        (cIntTimesSdtwoPsdToSdtwo clft tsgg boole pair 
;;         cCoGPsdTimes clft crht crht tsgg boole pair 
;;         cCoGPsdTimes crht crht crht tsgg boole)))]])

;; CoGAverage
(set-goal "allnc x,y(CoG x -> CoG y -> CoG((1#2)*(x+y)))")
(assume "x" "y" "CoGx" "CoGy")
(use "CoGAvcToCoG")
(use "CoGAvToAvc")
(use "CoGx")
(use "CoGy")
;; Proof finished.
;; (cdp)
(save "CoGAverage")

(define CoGAverage-eterm (proof-to-extracted-term))
(define CoGAverage-neterm (rename-variables (nt CoGAverage-eterm)))
(pp CoGAverage-neterm)

;; [ag,ag0]cCoGAvcToCoG(cCoGAvToAvc ag ag0)

