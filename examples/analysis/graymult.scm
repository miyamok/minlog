;; 2021-03-04.  examples/analysis/graymult.scm.

(load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "str.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")
;; (set! COMMENT-FLAG #t)

(load "~/git/minlog/examples/analysis/digits.scm")
(load "~/git/minlog/examples/analysis/sdcode.scm")
(load "~/git/minlog/examples/analysis/graycode.scm")
(load "~/git/minlog/examples/analysis/JK.scm")
(load "~/git/minlog/examples/analysis/grayavaux.scm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Multiplication for Gray code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CoGZero
(set-goal "CoG 0")
(assert "allnc x(exl x1(Real x1 andi x1===0 andi x===x1) -> CoG x)")
(assume "x" "CoG-ExHyp")
(coind "CoG-ExHyp" (pf "exl x1(Real x1 andi x1===0 andi x===x1) -> CoH x"))
(assume "y" "CoH-ExHyp")
(intro 1)
(by-assume "CoG-ExHyp" "x1" "x1Prop")
(by-assume "CoH-ExHyp" "y1" "y1Prop")
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "x1Prop")
(split)
(simpreal "x1Prop")
(use "RatLeToRealLe")
(use "Truth")
(split)
(intro 1)
(intro 0 (pt "x1"))
(split)
(use "x1Prop")
(split)
(use "x1Prop")
(use "RealEqRefl")
(use "x1Prop")
(split)
(assert "Real x1")
(use "x1Prop")
(assume "Rx1")
(assert "Real y1")
(use "y1Prop")
(assume "Ry1")
(simpreal "y1Prop")
(simpreal "x1Prop")
(simpreal "RealTimesZero")
(use "RatEqvToRealEq")
(use "Truth")
(autoreal)
(use "y1Prop")
;; 6
(assume "y" "CoH-ExHyp")
(intro 1)
(by-assume "CoG-ExHyp" "x1" "x1Prop")
(by-assume "CoH-ExHyp" "y1" "y1Prop")
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "x1Prop")
(split)
(simpreal "x1Prop")
(use "RatLeToRealLe")
(use "Truth")
(split)
(intro 1)
(intro 0 (pt "x1"))
(split)
(use "x1Prop")
(split)
(use "x1Prop")
(use "RealEqRefl")
(use "x1Prop")
(split)
(assert "Real x1")
(use "x1Prop")
(assume "Rx1")
(assert "Real y1")
(use "y1Prop")
(assume "Ry1")
(simpreal "y1Prop")
(simpreal "x1Prop")
(simpreal "RealTimesZero")
(use "RatEqvToRealEq")
(use "Truth")
(autoreal)
(use "y1Prop")
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(split)
(autoreal)
(split)
(use "RatEqvToRealEq")
(use "Truth")
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "CoGZero")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; (CoRec rea=>ag rea=>ah)0([x]InR(InR 0))([x]InR(InR 0))

;; CoGMultToMultcAux2
(set-goal "allnc x1,y1,d1,e1(Real x1 -> Real y1 ->
 (1#2)*(x1+IntN 1)* ~d1*((1#2)*(y1+IntN 1)* ~e1)===
 (1#4)*(x1*d1*(y1*e1)+z1+d1*e1))")

;; CoGMultToMultcAux
(set-goal "allnc x1,y1,d1,e1(Real x1 -> Real y1 ->
 (1#2)*(x1+IntN 1)* ~d1*((1#2)*(y1+IntN 1)* ~e1)===
 (1#4)*(x1*d1*(y1*e1)+2*((1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1)))+d1*e1))")
(assume "x1" "y1" "d1" "e1" "Rx1" "Ry1")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(ng #t)
(simprat (pf "(1#2)*(as n+IntN 1)*d1*(1#2)==
              (1#2)*((1#2)*(as n+IntN 1)*d1)"))
(ng #t)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "RatEqv6RewRule")
;; ?^19:(as n+IntN 1)*(d1*((bs n+IntN 1)*e1))==
;;      as n*d1*bs n*e1+ ~(as n*(d1*e1))+ ~(bs n*(d1*e1))+d1*e1
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(ng #t)
(use "RatPlusCompat")
(use "RatPlusCompat")
(simp "RatEqv4RewRule")
(simp "<-" "RatTimes3RewRule")
;; ?^31:as n*(d1*IntN 1*e1)==as n* ~(d1*e1)
(simp "IntTimesIntNR")
(use "Truth")
;; ?^29:IntN 1*d1*bs n*e1== ~(bs n*(d1*e1))
(simp "IntTimesIntNL")
(ng #t)
(simp (pf "d1*bs n=bs n*d1"))
(simp (pf "(d1*e1#1)=RatTimes d1 e1"))
(use "RatEqvSym")
(simp "RatTimesAssoc")
(use "Truth")
(use "Truth")
(use "RatTimesComm")
;; ?^27:IntN 1*d1*IntN 1*e1==d1*e1
(simp "IntTimesIntNL")
(ng #t)
(simp "<-" "IntTimesAssoc")
(simp "IntTimesIntNL")
(use "Truth")
;; ?^14:(1#2)*(as n+IntN 1)*d1*(1#2)==(1#2)*((1#2)*(as n+IntN 1)*d1)
(simp (pf "(1#2)*((1#2)*(as n+IntN 1)*d1)=((1#2)*(as n+IntN 1)*d1)*(1#2)"))
(use "Truth")
(use "RatTimesComm")
;; Proof finished.
;; (cdp)
(save "CoGMultToMultcAux")

;; CoGMultToMultc
(set-goal "allnc x,y(CoG x -> CoG y ->
 exr i,x1,y1,z1(Sdtwo i andi CoG x1 andi CoG y1 andi CoG z1 andi
 x*y===(1#4)*(x1*y1+z1+i)))")
(assume "x" "y" "CoGx" "CoGy")
(inst-with-to "CoGClosure" (pt "x") "CoGx" "xCases")
(elim "xCases")
;; 5,6
(drop "xCases")

;; Case LRx
(assume "ExHypx")
(by-assume "ExHypx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(assert "CoG x1")
(use "d1x1Prop")
(assume "CoGx1")

;; We distinguish cases on CoG y
(inst-with-to "CoGClosure" (pt "y") "CoGy" "yCases")
(elim "yCases")
;; 20,21
(drop "yCases")

;; Subcase LRx, LRy
(assume "ExHypy")
(by-assume "ExHypy" "e1" "e1Prop")
(by-assume "e1Prop" "y1" "e1y1Prop")
(assert "CoG y1")
(use "e1y1Prop")
(assume "CoGy1")

(assert "CoG((1#2)*(x1* ~(d1*e1)+ y1* ~(d1*e1)))")
(use "CoGAverage")
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "IntTimesPsdToPsd")
(use "d1x1Prop")
(use "e1y1Prop")
(use "CoGPsdTimes")
(use "CoGy1")
(use "PsdUMinus")
(use "IntTimesPsdToPsd")
(use "d1x1Prop")
(use "e1y1Prop")
(assume "CoGAvxy")

;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {d1}  {x1}  d1x1Prop:Psd d1 andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d1
;;   CoGx1:CoG x1
;;   {e1}  {y1}  e1y1Prop:Psd e1 andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e1
;;   CoGy1:CoG y1
;;   CoGAvxy:CoG((1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1)))
;; -----------------------------------------------------------------------------
;; ?_47:exr i,x0,y0,z(
;;       Sdtwo i andd 
;;       CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))

(inst-with-to "CoGClosure"
	      (pt "(1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1))") "CoGAvxy" "zCases")
(elim "zCases")
;; 50,51
(drop "zCases")

;; Case LRz
(assume "ExHypz")
(by-assume "ExHypz" "d0" "d0Prop")
(by-assume "d0Prop" "z1" "d0z1Prop")
(assert "CoG z1")
(use "d0z1Prop")
(assume "CoGz1")
(intro 0 (pt "d0+d1*e1"))
(intro 0 (pt "x1*d1"))
(intro 0 (pt "y1*e1"))
(intro 0 (pt "z1* ~d0"))
(split)
(use "IntPlusPsdToSdtwo")
(use "d0z1Prop")
(use "IntTimesPsdToPsd")
(use "d1x1Prop")
(use "e1y1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "d1x1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "e1y1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "PsdUMinus")
(use "d0z1Prop")
(assert "Real((1#4)*(x1*d1*(y1*e1)+z1* ~d0+(d0+d1*e1)))")
(realproof)
(assume "R")
(simpreal "d1x1Prop")
(simpreal "e1y1Prop")
;; ?^90:(1#2)*(x1+IntN 1)* ~d1*((1#2)*(y1+IntN 1)* ~e1)===
;;      (1#4)*(x1*d1*(y1*e1)+z1* ~d0+(d0+d1*e1))
;; RealEqTrans for simpreal with (1#2)*z1
(use "RealEqTrans"
     (pt "(1#4)*(x1*d1*(y1*e1)+2*((1#2)*(z1+IntN 1)* ~d0)+d1*e1)"))
(simpreal "<-" "d0z1Prop")
(use "CoGMultToMultcAux")
(autoreal)
;; ?^92:(1#4)*(x1*d1*(y1*e1)+2*((1#2)*(z1* ~d0+d0))+d1*e1)===
;;      (1#4)*(x1*d1*(y1*e1)+z1* ~d0+(d0+d1*e1))
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "as1" "M1" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(simprat "RatTimesPlusDistrLeft")
(ng #t)
(simp "IntTimesIntNL")
(ng #t)
(simp (pf "d0+d1*e1=RatPlus d0(d1*e1)"))
(simp "<-" "RatPlusAssoc")
(use "Truth")
(use "Truth")
;; ?_51:exr x0(CoH x0 andl (1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1))===(1#2)*x0) -> 
;;      exr i,x0,y0,z(
;;       Sdtwo i andd 
;;       CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))
(drop "zCases")
(assume "ExHypz1")
(by-assume "ExHypz1" "z1" "z1Prop")
(assert "CoH z1")
(use "z1Prop")
(assume "CoHz1")
;;   {z1}  z1Prop:CoH z1 andl (1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1))===(1#2)*z1
;;   CoHz1:CoH z1
;; -----------------------------------------------------------------------------
;; ?_122:exr i,x0,y0,z(
;;        Sdtwo i andd 
;;        CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))

(intro 0 (pt "d1*e1"))
(intro 0 (pt "x1*d1"))
(intro 0 (pt "y1*e1"))
(intro 0 (pt "z1"))
(split)
(use "PsdToSdtwo")
(use "IntTimesPsdToPsd")
(use "d1x1Prop")
(use "e1y1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "d1x1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "e1y1Prop")
(split)
(use "CoHToCoG")
(use "CoHz1")
;; ?^141:x*y===(1#4)*(x1*d1*(y1*e1)+z1+d1*e1)
(simpreal "d1x1Prop")
(simpreal "e1y1Prop")
;; ?^144:(1#2)*(x1+IntN 1)* ~d1*((1#2)*(y1+IntN 1)* ~e1)===
;;       (1#4)*(x1*d1*(y1*e1)+z1+d1*e1)
;; RealEqTrans for simpreal with (1#2)*z1
(use "RealEqTrans" (pt "(1#4)*(x1*d1*(y1*e1)+2*((1#2)*z1)+d1*e1)"))
(simpreal "<-" "z1Prop")
;; ?^147:(1#2)*(x1+IntN 1)* ~d1*((1#2)*(y1+IntN 1)* ~e1)===
;;       (1#4)*(x1*d1*(y1*e1)+2*((1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1)))+d1*e1)
(use "CoGMultToMultcAux")
(autoreal)
;; 146:(1#4)*(x1*d1*(y1*e1)+2*((1#2)*z1)+d1*e1)===(1#4)*(x1*d1*(y1*e1)+z1+d1*e1)
(simpreal (pf "2*((1#2)*z1)===z1"))
(use "RealEqRefl")
(realproof)
;; ?^151:2*((1#2)*z1)===z1
(use "RealEqSToEq")
(autoreal)
(use "RealEqSIntro")
(assume "n")
(cases (pt "z1"))
(assume "as" "M" "z1Def")
(ng #t)
(use "Truth")
;; ?_21:exr x0(CoH x0 andl y===(1#2)*x0) -> 
;;      exr i,x0,y0,z(
;;       Sdtwo i andd 
;;       CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))
(drop "yCases")

;; Subcase LRx, Uy
(assume "ExHypy")
(by-assume "ExHypy" "y1" "y1Prop")
(assert "CoH y1")
(use "y1Prop")
(assume "CoHy1")
(intro 0 (pt "0"))
(intro 0 (pt "x1* ~d1"))
(intro 0 (pt "y1"))
(intro 0 (pt "y1*d1"))
(split)
(use "InitSdtwoMT")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "d1x1Prop")
(split)
(use "CoHToCoG")
(use "CoHy1")
(split)
(use "CoGPsdTimes")
(use "CoHToCoG")
(use "CoHy1")
(use "d1x1Prop")
;; ?^268:x*y===(1#4)*(x1* ~d1*y1+y1*d1+0)
(simpreal "d1x1Prop")
(simpreal "y1Prop")
;; ?^273:(1#2)*(x1+IntN 1)* ~d1*((1#2)*y1)===(1#4)*(x1* ~d1*y1+y1*d1+0)
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(ng #t)
;; ?^283:~((1#2)*(as n+IntN 1)*d1*(1#2)*bs n)==(1#4)*(~(as n*d1*bs n)+bs n*d1)
(simp (pf "(1#2)*(as n+IntN 1)*d1*(1#2)=(1#2)*((1#2)*(as n+IntN 1)*d1)"))
(ng #t)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimes3RewRule")
(simp "RatEqv6RewRule")
(simprat "RatTimesPlusDistrLeft")
(ng #t)
(simp "IntTimesIntNL")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
;; ?^285:(1#2)*(as n+IntN 1)*d1*(1#2)=(1#2)*((1#2)*(as n+IntN 1)*d1)
(simp "RatTimesComm")
(use "Truth")
;; ?_6:exr x0(CoH x0 andl x===(1#2)*x0) -> 
;;     exr i,x0,y0,z(
;;      Sdtwo i andd CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))
(drop "xCases")

;; Case Ux
(assume "ExHypx")
(by-assume "ExHypx" "x1" "x1Prop")
(assert "CoH x1")
(use "x1Prop")
(assume "CoHx1")

;; We distinguish cases on CoG y
(inst-with-to "CoGClosure" (pt "y") "CoGy" "yCases")
(elim "yCases")
;; 307,308
(drop "yCases")

;; Subcase Ux, LRy
(assume "ExHypy")
(by-assume "ExHypy" "e1" "e1Prop")
(by-assume "e1Prop" "y1" "e1y1Prop")
(assert "CoG y1")
(use "e1y1Prop")
(assume "CoGy1")
(intro 0 (pt "0"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1* ~e1"))
(intro 0 (pt "x1*e1"))
(split)
(use "InitSdtwoMT")
(split)
(use "CoHToCoG")
(use "CoHx1")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "PsdUMinus")
(use "e1y1Prop")
(split)
(use "CoGPsdTimes")
(use "CoHToCoG")
(use "CoHx1")
(use "e1y1Prop")
;; ?^335:x*y===(1#4)*(x1*(y1* ~e1)+x1*e1+0)
(simpreal "x1Prop")
(simpreal "e1y1Prop")
;; ?^340:(1#2)*x1*((1#2)*(y1+IntN 1)* ~e1)===(1#4)*(x1*(y1* ~e1)+x1*e1+0)
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(ng #t)
;; ?^350:~((1#2)*as n*(1#2)*(bs n+IntN 1)*e1)==(1#4)*(~(as n*bs n*e1)+as n*e1)
;;         (1#2)*as n*(1#2)*(bs n+IntN 1)* ~e1==(1#4)*(as n*bs n* ~e1+as n*e1)
(simp (pf "(1#2)*as n*(1#2)=(1#2)*((1#2)*as n)"))
(ng #t)
(simp "<-" "RatTimes3RewRule")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(use "RatTimesCompat")
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistr")
(simp "RatTimesIntNL")
(use "Truth")
;; ?^352:(1#2)*as n*(1#2)=(1#2)*((1#2)*as n)
(simp "RatTimesComm")
(use "Truth")
;; ?_308:exr x0(CoH x0 andl y===(1#2)*x0) -> 
;;       exr i,x0,y0,z(
;;        Sdtwo i andd 
;;        CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))
(drop "yCases")

;; Subcase Ux, Uy
(assume "ExHypy")
(by-assume "ExHypy" "y1" "y1Prop")
(assert "CoH y1")
(use "y1Prop")
(assume "CoHy1")
(intro 0 (pt "0"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(split)
(use "InitSdtwoMT")
(split)
(use "CoHToCoG")
(use "CoHx1")
(split)
(use "CoHToCoG")
(use "CoHy1")
(split)
(use "CoGZero")
;; ?^384:x*y===(1#4)*(x1*y1+0+0)
(simpreal "x1Prop")
(simpreal "y1Prop")
;; ?^386:(1#2)*x1*((1#2)*y1)===(1#4)*(x1*y1+0+0)
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(ng #t)
;; ?^396:(1#2)*as n*(1#2)*bs n==(1#4)*as n*bs n
(simp (pf "(1#2)*as n*(1#2)=(1#2)*((1#2)*as n)"))
(use "Truth")
(use "RatTimesComm")
;; Proof finished.
;; (cdp)
(save "CoGMultToMultc")

;; cCoGMultToMultc: ag=>ag=>sdtwo yprod ag yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag,ag0][case (DesYprod ag)
;;    (InL bg -> [case (DesYprod ag0)
;;      (InL bg0 -> [case (DesYprod(cCoGAverage
;;        (cCoGPsdTimes crht bg
;;         (cPsdUMinus(cIntTimesPsdToPsd clft bg clft bg0)))
;;        (cCoGPsdTimes crht bg0
;;         (cPsdUMinus(cIntTimesPsdToPsd clft bg clft bg0)))))
;;        (InL bg1 -> 
;;        cIntPlusPsdToSdtwo 
;;          clft bg1(cIntTimesPsdToPsd clft bg clft bg0)pair 
;;        cCoGPsdTimes crht bg clft bg pair 
;;        cCoGPsdTimes crht bg0 clft bg0 pair 
;;        cCoGPsdTimes crht bg1(cPsdUMinus clft bg1))
;;        (InR ah -> 
;;        cPsdToSdtwo(cIntTimesPsdToPsd clft bg clft bg0)pair 
;;        cCoGPsdTimes crht bg clft bg pair 
;;        cCoGPsdTimes crht bg0 clft bg0 pair
;;        cCoHToCoG ah)])
;;      (InR ah -> MT pair 
;;                 cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair 
;;                 cCoHToCoG ah pair
;;                 cCoGPsdTimes(cCoHToCoG ah)clft bg)])
;;    (InR ah -> [case (DesYprod ag0)
;;      (InL bg -> MT pair 
;;                 cCoHToCoG ah pair 
;;                 cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair 
;;                 cCoGPsdTimes(cCoHToCoG ah)clft bg)
;;      (InR ah0 -> MT pair
;;                  cCoHToCoG ah pair
;;                  cCoHToCoG ah0 pair
;;                  cCoGZero)])]

(deanimate "CoGClosure")

;; We need auxiliary lemmas

;;       JKLrzLrvLr
;;       JKLrzLrvU
;;     JKLrzLrv
;;       JKLrzUvFin
;;       JKLrzUvD
;;     JKLrzUv
;;   JKLrz

;;       JKUzLrvLr
;;       JKUzLrvU
;;     JKUzLrv
;;       JKUzUvFin
;;       JKUzUvD
;;     JKUzUv
;;   JKUz

;; The previous JKLrzLrvLr asserted exnc j j=J(e* ~e0+2*e0+d0+i) leading to

;; n.c. conclusion expected
;; exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(d0+i#4)===(1#4)*(z+j)+d)
;; in the elimination axiom for an n.c. idpc formula
;; exnc k642078 k642078=J(e* ~e0+2*e0+d0+i)

;; Therefore - as in the sd case - we need an auxiliary lemma proving
;; Sdtwo(e* ~e0+2*e0+d0+i)

;; JKLrzLrvLrAuxJ
(set-goal "allnc e,e0,d0,i(Psd e -> Psd e0 -> Psd d0 -> Sdtwo i -> 
 Sdtwo(J(e* ~e0+2*e0+d0+i)))")
(assume "e" "e0" "d0" "i" "Psde" "Psde0" "Psdd0" "Sdtwoi")

(assert "exl boole1 PsdInj e boole1")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl boole2 PsdInj e0 boole2")
(use "PsdInjIntro")
(use "Psde0")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")

(assert "exl boole3 PsdInj d0 boole3")
(use "PsdInjIntro")
(use "Psdd0")
(assume "ExHyp3")
(by-assume "ExHyp3" "boole3" "boole3Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdtwoInjElim"
     (pt "IntToSdtwo(J(BooleToInt boole1* ~(BooleToInt boole2)+
                     2*BooleToInt boole2+BooleToInt boole3+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole1* ~(BooleToInt boole2)+
             2*BooleToInt boole2+BooleToInt boole3+SdtwoToInt t)=
           J(e* ~e0+2*e0+d0+i)"))
(use "SdtwoInjIntToSdtwo")
;; ?^34:abs(J(e* ~e0+2*e0+d0+i))<=2
(use "JProp")
(simp (pf "BooleToInt boole1* ~(BooleToInt boole2)+2*BooleToInt boole2+
           BooleToInt boole3+SdtwoToInt t=e* ~e0+2*e0+d0+i"))
(use "Truth")
;; ?^36:BooleToInt boole1* ~(BooleToInt boole2)+2*BooleToInt boole2+
;;      BooleToInt boole3+
;;      SdtwoToInt t=
;;      e* ~e0+2*e0+d0+i
(inst-with-to "PsdInjId" (pt "e") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "e0") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "PsdInjId" (pt "d0") (pt "boole3") "boole3Prop" "PsdInjIdInst3")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "PsdInjIdInst3")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzLrvLrAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [boole,boole0,boole1,t]IntToSdtwo(J
;;   (~(BooleToInt boole*BooleToInt boole0)+2*BooleToInt boole0+
;;    BooleToInt boole1+SdtwoToInt t))

;; JKLrzLrvLrAuxK
(set-goal "allnc e,e0,d0,i(Psd e -> Psd e0 -> Psd d0 -> Sdtwo i -> 
 Sd(K(e* ~e0+2*e0+d0+i)))")
(assume "e" "e0" "d0" "i" "Psde" "Psde0" "Psdd0" "Sdtwoi")
(assert "exl boole1 PsdInj e boole1")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl boole2 PsdInj e0 boole2")
(use "PsdInjIntro")
(use "Psde0")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")

(assert "exl boole3 PsdInj d0 boole3")
(use "PsdInjIntro")
(use "Psdd0")
(assume "ExHyp3")
(by-assume "ExHyp3" "boole3" "boole3Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdInjElim"
     (pt "IntToSd(K(BooleToInt boole1* ~(BooleToInt boole2)+
                   2*BooleToInt boole2+BooleToInt boole3+SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole1* ~(BooleToInt boole2)+
             2*BooleToInt boole2+BooleToInt boole3+SdtwoToInt t)=
           K(e* ~e0+2*e0+d0+i)"))
(use "SdInjIntToSd")
;; ?^34:abs(K(e* ~e0+2*e0+d0+i))<=1
(use "KProp")
;; ?^35:abs(e* ~e0+2*e0+d0+i)<=6
(use "IntLeTrans" (pt "IntP 4+IntP 2"))
(use "IntLeTrans" (pt "abs(e* ~e0+2*e0+d0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 3+IntP 1"))
(use "IntLeTrans" (pt "abs(e* ~e0+2*e0)+abs d0"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs(e* ~e0)+abs(2*e0)"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(ng #t)
(simp "PsdToAbsOne")
(simp "PsdToAbsOne")
(use "Truth")
(use "Psde0")
(use "Psde")
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psde0")
(use "Truth")
(use "SdBound")
(use "PsdToSd")
(use "Psdd0")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "BooleToInt boole1* ~(BooleToInt boole2)+2*BooleToInt boole2+
      BooleToInt boole3+SdtwoToInt t=e* ~e0+2*e0+d0+i"))
(use "Truth")
;; ?^66:BooleToInt boole1* ~(BooleToInt boole2)+2*BooleToInt boole2+
;;      BooleToInt boole3+
;;      SdtwoToInt t=
;;      e* ~e0+2*e0+d0+i
(inst-with-to "PsdInjId" (pt "e") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "e0") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "PsdInjId" (pt "d0") (pt "boole3") "boole3Prop" "PsdInjIdInst3")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "PsdInjIdInst3")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzLrvLrAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [boole,boole0,boole1,t]IntToSd(K
;;   (~(BooleToInt boole*BooleToInt boole0)+2*BooleToInt boole0+
;;    BooleToInt boole1+SdtwoToInt t))

;; JKLrzLrvLr
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> allnc e0,z2(
 Psd e0 -> y===(1#2)*(z2+IntN 1)* ~e0 -> allnc e,z3(
 Psd e -> CoG z3 -> z2===(1#2)*(z3+IntN 1)* ~e ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0"
	"e0" "z2" "Psde0" "e0z2Prop"
        "e" "z3" "Psde" "CoGz3" "ez3Prop")

;; (assert "exnc j j=J(e* ~e0+2*e0+d0+i)")
(assert "exr j(j=J(e* ~e0+2*e0+d0+i) andr Sdtwo j)")
(intro 0 (pt "J(e* ~e0+2*e0+d0+i)"))
(split)
(use "Truth")
(use "JKLrzLrvLrAuxJ")
(use "Psde")
(use "Psde0")
(use "Psdd0")
(use "Sdtwoi")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

;; (assert "exnc k k=K(e* ~e0+2*e0+d0+i)")
(assert "exr k(k=K(e* ~e0+2*e0+d0+i) andr Sd k)")
(intro 0 (pt "K(e* ~e0+2*e0+d0+i)"))
(split)
(use "Truth")
(use "JKLrzLrvLrAuxK")
(use "Psde")
(use "Psde0")
(use "Psdd0")
(use "Sdtwoi")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3*e*e0"))

(assert "exl boole BooleToInt boole=e")
(use "PsdToBooleToIntValue")
(use "Psde")
(assume "ExHype")
(by-assume "ExHype" "boole" "booleProp")

(assert "exl boole0 BooleToInt boole0=e0")
(use "PsdToBooleToIntValue")
(use "Psde0")
(assume "ExHype0")
(by-assume "ExHype0" "boole1" "boole1Prop")

(assert "exl boole BooleToInt boole=d0")
(use "PsdToBooleToIntValue")
(use "Psdd0")
(assume "ExHypd0")
(by-assume "ExHypd0" "boole0" "boole0Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; ?_62:Sdtwo(J(e* ~e0+2*e0+d0+i))
(use "JKLrzLrvLrAuxJ")
(use "Psde")
(use "Psde0")
(use "Psdd0")
(use "Sdtwoi")

(split)
(simp "kDef")
;; ?_69:Sdtwo(K(e* ~e0+2*e0+d0+i))
(use "JKLrzLrvLrAuxK")
(use "Psde")
(use "Psde0")
(use "Psdd0")
(use "Sdtwoi")

(split)
;; ?_74:CoG(z3*e*e0)
(use "CoGPsdTimes")
(use "CoGPsdTimes")
(use "CoGz3")
(use "Psde")
(use "Psde0")

;; ?^75:y+(d0+i#4)===(1#4)*(z3*e*e0+j)+k
(simpreal "e0z2Prop")
(simpreal "ez3Prop")
;; ?^81:(1#2)*((1#2)*(z3+IntN 1)* ~e+IntN 1)* ~e0+(d0+i#4)===(1#4)*(z3*e*e0+j)+k
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^93:~((1#2)*(~((1#2)*(cs n+IntN 1)*e)+IntN 1)*e0)+(d0+i#4)==
;;      (1#4)*(cs n*e*e0+j)+k
(use "RatEqvTrans"
     (pt "(1#2)*(((1#2)*((cs n+IntN 1)* ~e)+IntN 1)* ~e0)+(1#4)*RatPlus d0 i"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(simp "RatTimesIntNL")
(simp (pf "~(RatTimes 1~e)=(e#1)"))
(simp (pf "~(RatTimes 1~e0)=(e0#1)"))
;; ?^102:(1#2)*((1#2)*(cs n* ~e+e)* ~e0+e0)+(1#4)*RatPlus d0 i==
;;       (1#4)*(cs n*e*e0+j)+k
(use "RatEqvTrans"
     (pt "(1#2)*((1#2)*((cs n* ~e+e)* ~e0)+e0)+(1#4)*RatPlus d0 i"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat
 (pf "(1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+e0==
      (1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+(1#2)*(2*e0)"))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp (pf "(1#2)*(1#2)=(1#4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?^118:cs n* ~e* ~e0+RatTimes e~e0+2*e0+RatPlus d0 i==cs n*e*e0+j+k*4
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp (pf "RatTimes~e~e0=RatTimes e e0"))
(simprat (pf "cs n*RatTimes e e0+RatTimes e~e0+2*e0+RatPlus d0 i==
              cs n*RatTimes e e0+(RatTimes e~e0+2*e0+RatPlus d0 i)"))
(simp (pf "cs n*RatTimes e e0+j+k*4=cs n*RatTimes e e0+(j+k*4)"))
(use "RatPlusCompat")
(use "Truth")
;; ?^128:RatTimes e~e0+2*e0+RatPlus d0 i==j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J(e* ~e0+2*e0+d0+i)+K(e* ~e0+2*e0+d0+i)*4=
           K(e* ~e0+2*e0+d0+i)*4+J(e* ~e0+2*e0+d0+i)"))
(simp "<-" "KJProp")
;; ?^133:RatTimes e~e0+2*e0+RatPlus d0 i==e* ~e0+2*e0+d0+i
(use "Truth")
(use "IntPlusComm")
;; ?^126:cs n*RatTimes e e0+j+k*4=cs n*RatTimes e e0+(j+k*4)
(simp "<-" "RatPlusAssoc")
(use "Truth")
;; ?^124:cs n*RatTimes e e0+RatTimes e~e0+2*e0+RatPlus d0 i==
;;       cs n*RatTimes e e0+(RatTimes e~e0+2*e0+RatPlus d0 i)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?^108:(1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+e0==
;;       (1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+(1#2)*(2*e0)
(use "RatPlusCompat")
(use "Truth")
(use "IntTimesComm")
;; ?^103:~(RatTimes 1~e0)=e0
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzLrvLr")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,boole0,boole1,ag]
;;  cJKLrzLrvLrAuxJ boole1 boole0 boole t pair 
;;  cJKLrzLrvLrAuxK boole1 boole0 boole t pair 
;;  cCoGPsdTimes(cCoGPsdTimes ag boole1)boole0

;; The same for JKLrzLrvU

;; JKLrzLrvUAuxJ
(set-goal "allnc e0,d0,i(Psd e0 -> Psd d0 -> Sdtwo i -> Sdtwo(J(2*e0+d0+i)))")
(assume "e0" "d0" "i" "Psde0" "Psdd0" "Sdtwoi")
(assert "exl boole1 PsdInj e0 boole1")
(use "PsdInjIntro")
(use "Psde0")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl boole2 PsdInj d0 boole2")
(use "PsdInjIntro")
(use "Psdd0")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdtwoInjElim"
     (pt "IntToSdtwo(J(2*BooleToInt boole1+BooleToInt boole2+SdtwoToInt t))"))
(simp (pf "J(2*BooleToInt boole1+BooleToInt boole2+SdtwoToInt t)=
           J(2*e0+d0+i)"))
(use "SdtwoInjIntToSdtwo")
;; ?^27:abs(J(2*e0+d0+i))<=2
(use "JProp")
(simp (pf "2*BooleToInt boole1+BooleToInt boole2+SdtwoToInt t=2*e0+d0+i"))
(use "Truth")
;; ?^29:2*BooleToInt boole1+BooleToInt boole2+SdtwoToInt t=2*e0+d0+i
(inst-with-to "PsdInjId" (pt "e0") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "d0") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzLrvUAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,boole0,t]
;; IntToSdtwo(J(2*BooleToInt boole+BooleToInt boole0+SdtwoToInt t))

;; JKLrzLrvUAuxK
(set-goal "allnc e0,d0,i(Psd e0 -> Psd d0 -> Sdtwo i -> Sd(K(2*e0+d0+i)))")
(assume "e0" "d0" "i" "Psde0" "Psdd0" "Sdtwoi")
(assert "exl boole1 PsdInj e0 boole1")
(use "PsdInjIntro")
(use "Psde0")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl boole2 PsdInj d0 boole2")
(use "PsdInjIntro")
(use "Psdd0")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdInjElim"
     (pt "IntToSd(K(2*BooleToInt boole1+BooleToInt boole2+SdtwoToInt t))"))
(simp (pf "K(2*BooleToInt boole1+BooleToInt boole2+SdtwoToInt t)=
           K(2*e0+d0+i)"))
(use "SdInjIntToSd")
;; ?^27:abs(K(2*e0+d0+i))<=1
(use "KProp")
;; ?^28:abs(2*e0+d0+i)<=6
(use "IntLeTrans" (pt "IntP 3+IntP 2"))
(use "IntLeTrans" (pt "abs(2*e0+d0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 2+IntP 1"))
(use "IntLeTrans" (pt "abs(2*e0)+abs d0"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psde0")
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd0")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "2*BooleToInt boole1+ BooleToInt boole2+SdtwoToInt t=2*e0+d0+i"))
(use "Truth")
;; ?^48:2*BooleToInt boole1+BooleToInt boole2+SdtwoToInt t=2*e0+d0+i
(inst-with-to "PsdInjId" (pt "e0") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "d0") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzLrvUAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,boole0,t]
;;  IntToSd(K(2*BooleToInt boole+BooleToInt boole0+SdtwoToInt t))

;; JKLrzLrvU
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> allnc e0,z2(
 Psd e0 -> y===(1#2)*(z2+IntN 1)* ~e0 -> allnc z3(
 CoH z3 -> z2===(1#2)*z3 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0"
	"e0" "z2" "Psde0" "e0z2Prop"
        "z3" "CoHz3" "z3Prop")

(assert "exr j(j=J(2*e0+d0+i) andr Sdtwo j)")
(intro 0 (pt "J(2*e0+d0+i)"))
(split)
(use "Truth")
(use "JKLrzLrvUAuxJ")
(use "Psde0")
(use "Psdd0")
(use "Sdtwoi")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exr k(k=K(2*e0+d0+i) andr Sd k)")
(intro 0 (pt "K(2*e0+d0+i)"))
(split)
(use "Truth")
(use "JKLrzLrvUAuxK")
(use "Psde0")
(use "Psdd0")
(use "Sdtwoi")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3* ~e0"))

(assert "exl boole0 BooleToInt boole0=e0")
(use "PsdToBooleToIntValue")
(use "Psde0")
(assume "ExHype0")
(by-assume "ExHype0" "boole1" "boole1Prop")

(assert "exl boole BooleToInt boole=d0")
(use "PsdToBooleToIntValue")
(use "Psdd0")
(assume "ExHypd0")
(by-assume "ExHypd0" "boole0" "boole0Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; ?_53:Sdtwo(J(2*e0+d0+i))
(use "JKLrzLrvUAuxJ")
(use "Psde0")
(use "Psdd0")
(use "Sdtwoi")

(split)
(simp "kDef")
;; ?_59:Sd(K(2*e0+d0+i))
(use "JKLrzLrvUAuxK")
(use "Psde0")
(use "Psdd0")
(use "Sdtwoi")

(split)
;; ?_63:CoG(z3* ~e0)
(use "CoGPsdTimes")
(use "CoHToCoG")
(use "CoHz3")
(use "PsdUMinus")
(use "Psde0")

;; ?^64:y+(d0+i#4)===(1#4)*(z3* ~e0+j)+k
(simpreal "e0z2Prop")
(simpreal "z3Prop")
;; ?^70:(1#2)*((1#2)*z3+IntN 1)* ~e0+(d0+i#4)===(1#4)*(z3* ~e0+j)+k
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^82:~((1#2)*((1#2)*cs n+IntN 1)*e0)+(d0+i#4)==(1#4)*(~(cs n*e0)+j)+k
(use "RatEqvTrans"
 (pt "(1#2)*(((1#2)*cs n+IntN 1)* ~e0)+(1#4)*RatPlus d0 i"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(simp (pf "~(RatTimes 1~e0)=(e0#1)"))
;; ?^87:(1#2)*((1#2)*cs n* ~e0+e0)+(1#4)*RatPlus d0 i==(1#4)*(~(cs n*e0)+j)+k
(simp (pf "(1#2)*cs n* ~e0=(1#2)*(cs n* ~e0)"))
(simprat (pf "(1#2)*((1#2)*(cs n* ~e0)+e0)==
              (1#2)*((1#2)*(cs n* ~e0)+(1#2)*(2*e0))"))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp (pf "(1#2)*(1#2)=(1#4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?^102:cs n* ~e0+2*e0+RatPlus d0 i== ~(cs n*e0)+j+k*4
(simp (pf "cs n* ~e0+2*e0+RatPlus d0 i=cs n* ~e0+(2*e0+RatPlus d0 i)"))
(simp (pf "cs n* ~e0+j+k*4=cs n* ~e0+(j+k*4)"))
(use "RatPlusCompat")
(use "Truth")
;; ?^108:2*e0+RatPlus d0 i==j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J(2*e0+d0+i)+K(2*e0+d0+i)*4=K(2*e0+d0+i)*4+J(2*e0+d0+i)"))
(simp "<-" "KJProp")
;; ?^113:2*e0+RatPlus d0 i==2*e0+d0+i
(use "Truth")
(use "IntPlusComm")
;; ?^106:cs n* ~e0+j+k*4=acs n* ~e0+(j+k*4)
(simp "<-" "RatPlusAssoc")
(use "Truth")
;; ?^104:cs n* ~e0+2*e0+RatPlus d0 i=cs n* ~e0+(2*e0+RatPlus d0 i)
(simp "<-" "RatPlusAssoc")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?^92:(1#2)*((1#2)*(cs n* ~e0)+e0)==(1#2)*((1#2)*(cs n* ~e0)+(1#2)*(2*e0))
(use "RatTimesCompat")
(use "Truth")
;; ?^117:(1#2)*(cs n* ~e0)+e0==(1#2)*(cs n* ~e0)+(1#2)*(2*e0)
(use "RatPlusCompat")
(use "Truth")
(use "IntTimesComm")
;; ?^90:(1#2)*cs n* ~e0=(1#2)*(cs n* ~e0)
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzLrvU")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,boole0,ah]
;;  cJKLrzLrvUAuxJ boole0 boole t pair 
;;  cJKLrzLrvUAuxK boole0 boole t pair 
;;  cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole0)

(animate "JKLrzLrvUAuxJ")
(animate "JKLrzLrvUAuxK")

(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,boole0,ah]
;;  IntToSdtwo(J(2*BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;  IntToSd(K(2*BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;  cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole0)

(deanimate "JKLrzLrvUAuxJ")
(deanimate "JKLrzLrvUAuxK")

;; Next JKLrzLrv

;; JKLrzLrv
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> allnc e0,z2(
 Psd e0 -> CoG z2 -> y===(1#2)*(z2+IntN 1)* ~e0 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d)))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0"
	"e0" "z2" "Psde0" "CoGz2" "e0z2Prop")
(inst-with-to "CoGClosure" (pt "z2") "CoGz2" "z2Cases")
(elim "z2Cases")
;; 5,6
(drop "z2Cases")

;; Subcase Lrz2
(assume "ExHypz2")
(by-assume "ExHypz2" "e" "eProp")
(by-assume "eProp" "z3" "ez3Prop")
(use-with "JKLrzLrvLr"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0"
 (pt "e0") (pt "z2") "Psde0" "e0z2Prop" (pt "e") (pt "z3") "?" "?" "?")
(use "ez3Prop")
(use "ez3Prop")
(use "ez3Prop")

;; ?_6:exr x(CoH x andl z2===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(d0+i#4)===(1#4)*(z+j)+d)

(drop "z2Cases")

;; Subcase Uz2
(assume "ExHypz2")
(by-assume "ExHypz2" "z3" "z3Prop")

(use-with "JKLrzLrvU"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0"
 (pt "e0") (pt "z2") "Psde0" "e0z2Prop"
 (pt "z3") "?" "?")
(use "z3Prop")
(use "z3Prop")
;; Proof finished.
;; (cdp)
(save "JKLrzLrv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [t,boole,boole0,ag]
;;  [case (cCoGClosure ag)
;;    (InL bg -> cJKLrzLrvLr t boole boole0 clft bg crht bg)
;;    (InR ah -> cJKLrzLrvU t boole boole0 ah)]

(animate "CoGClosure")
(animate "JKLrzLrvLr")
(animate "JKLrzLrvLrAuxJ")
(animate "JKLrzLrvLrAuxK")
(animate "JKLrzLrvU")
(animate "JKLrzLrvUAuxJ")
(animate "JKLrzLrvUAuxK")

(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [t,boole,boole0,ag]
;;  [case (DesYprod ag)
;;    (InL bg -> 
;;    IntToSdtwo
;;    (J
;;     (~(BooleToInt clft bg*BooleToInt boole0)+2*BooleToInt boole0+
;;      BooleToInt boole+
;;      SdtwoToInt t))pair 
;;    IntToSd
;;    (K
;;     (~(BooleToInt clft bg*BooleToInt boole0)+2*BooleToInt boole0+
;;      BooleToInt boole+
;;      SdtwoToInt t))pair 
;;    cCoGPsdTimes(cCoGPsdTimes crht bg clft bg)boole0)
;;    (InR ah -> 
;;    IntToSdtwo(J(2*BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd(K(2*BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;    cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole0))]

(deanimate "CoGClosure")
(deanimate "JKLrzLrvLr")
(deanimate "JKLrzLrvLrAuxJ")
(deanimate "JKLrzLrvLrAuxK")
(deanimate "JKLrzLrvU")
(deanimate "JKLrzLrvUAuxJ")
(deanimate "JKLrzLrvUAuxK")

;; Next JKLrzUvFin

;; JKLrzUvFinAuxJ
(set-goal "allnc e,d0,i(Psd e -> Psd d0 -> Sdtwo i -> Sdtwo(J(e+d0+i)))")
(assume "e" "d0" "i" "Psde" "Psdd0" "Sdtwoi")

(assert "exl boole1 PsdInj e boole1")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl boole2 PsdInj d0 boole2")
(use "PsdInjIntro")
(use "Psdd0")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdtwoInjElim"
     (pt "IntToSdtwo(J(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t)=J(e+d0+i)"))
(use "SdtwoInjIntToSdtwo")
;; ?^27:abs(J(e+d0+i))<=2
(use "JProp")
(simp (pf "BooleToInt boole1+BooleToInt boole2+SdtwoToInt t=e+d0+i"))
(use "Truth")
;; ?^29:BooleToInt boole1+BooleToInt boole2+SdtwoToInt t=e+d0+i
(inst-with-to "PsdInjId" (pt "e") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "d0") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzUvFinAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,boole0,t]
;;  IntToSdtwo(J(BooleToInt boole+BooleToInt boole0+SdtwoToInt t))

;; JKLrzUvFinAuxK
(set-goal "allnc e,d0,i(Psd e -> Psd d0 -> Sdtwo i -> Sd(K(e+d0+i)))")
(assume "e" "d0" "i" "Psde" "Psdd0" "Sdtwoi")

(assert "exl boole1 PsdInj e boole1")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl boole2 PsdInj d0 boole2")
(use "PsdInjIntro")
(use "Psdd0")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdInjElim"
     (pt "IntToSd(K(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t)=K(e+d0+i)"))
(use "SdInjIntToSd")
;; ?^27:abs(K(e+d0+i))<=1
(use "KProp")
(use "IntLeTrans" (pt "IntP 2+IntP 2"))
(use "IntLeTrans" (pt "abs(e+d0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 1"))
(use "IntLeTrans" (pt "abs e+abs d0"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(simp "PsdToAbsOne")
(use "Truth")
(use "Psde")
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd0")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "BooleToInt boole1+ BooleToInt boole2+SdtwoToInt t=e+d0+i"))
(use "Truth")
;; ?^47:BooleToInt boole1+BooleToInt boole2+SdtwoToInt t=e+d0+i
(inst-with-to "PsdInjId" (pt "e") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "d0") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzUvFinAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [boole,boole0,t]IntToSd(K(BooleToInt boole+BooleToInt boole0+SdtwoToInt t))

;; JKLrzUvFin
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> allnc z2(
 CoH z2 --> y===(1#2)*z2 -> allnc e,z3(
 Psd e -> CoG z3 -> z2===(1#2)*(z3+1)*e ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0"
	"z2" "CoHz2" "z2Prop"
        "e" "z3" "Psde" "CoGz3" "ez3Prop")

;; (assert "exnc j j=J(e+d0+i)")
(assert "exr j(j=J(e+d0+i) andr Sdtwo j)")
(intro 0 (pt "J(e+d0+i)"))
(split)
(use "Truth")
(use "JKLrzUvFinAuxJ")
(use "Psde")
(use "Psdd0")
(use "Sdtwoi")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

;; (assert "exnc k k=K(e+d0+i)")
(assert "exr k(k=K(e+d0+i) andr Sd k)")
(intro 0 (pt "K(e+d0+i)"))
(split)
(use "Truth")
(use "JKLrzUvFinAuxK")
(use "Psde")
(use "Psdd0")
(use "Sdtwoi")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3*e"))

(assert "exl boole BooleToInt boole=e")
(use "PsdToBooleToIntValue")
(use "Psde")
(assume "ExHype")
(by-assume "ExHype" "boole" "booleProp")

(assert "exl boole BooleToInt boole=d0")
(use "PsdToBooleToIntValue")
(use "Psdd0")
(assume "ExHypd0")
(by-assume "ExHypd0" "boole0" "boole0Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(use "jDef")

(split)
(use "kDef")

(split)
(use "CoGPsdTimes")
(use "CoGz3")
(use "Psde")

;; ?^56:y+(d0+i#4)===(1#4)*(z3*e+j)+k
(simpreal "z2Prop")
(simpreal "ez3Prop")
;; ?^60:(1#2)*((1#2)*(z3+1)*e)+(d0+i#4)===(1#4)*(z3*e+j)+k
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^72:(1#4)*(cs n+1)*e+(d0+i#4)==(1#4)*(cs n*e+j)+k
(use "RatEqvTrans" (pt "(1#4)*(cs n+1)*e+(1#4)*RatPlus d0 i"))
(use "Truth")
;; ?^74:(1#4)*(cs n+1)*e+(1#4)*RatPlus d0 i==(1#4)*(cs n*e+j)+k
(simp (pf "(1#4)*(cs n+1)*e=(1#4)*((cs n+1)*e)"))
(simprat "RatTimesPlusDistrLeft")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?^83:cs n*e+RatTimes 1 e+RatPlus d0 i==cs n*e+j+k*4
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?^87:RatTimes 1 e+RatPlus d0 i==RatPlus j(k*4)
(simp "jDef")
(simp "kDef")
(simp (pf "RatPlus(J(e+d0+i))(K(e+d0+i)*4)=K(e+d0+i)*4+J(e+d0+i)"))
(simp "<-" "KJProp")
;; ?^92:RatTimes 1 e+RatPlus d0 i==e+d0+i
(use "Truth")
(use "IntPlusComm")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzUvFin")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,boole0,ag]
;;  cJKLrzUvFinAuxJ boole0 boole t pair 
;;  cJKLrzUvFinAuxK boole0 boole t pair cCoGPsdTimes ag boole0

(animate "JKLrzUvFinAuxJ")
(animate "JKLrzUvFinAuxK")

(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,boole0,ag]
;;  IntToSdtwo(J(BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;  IntToSd(K(BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;  cCoGPsdTimes ag boole0

(deanimate "JKLrzUvFinAuxJ")
(deanimate "JKLrzUvFinAuxK")

;; Next JKLrzUvD

;; JKLrzUvDAuxJ
(set-goal "allnc d0,i(Psd d0 -> Sdtwo i -> Sdtwo(J(d0+i)))")
(assume "d0" "i" "Psdd0" "Sdtwoi")

(assert "exl boole1 PsdInj d0 boole1")
(use "PsdInjIntro")
(use "Psdd0")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp2")
(by-assume "ExHyp2" "t" "tProp")

(use "SdtwoInjElim"
     (pt "IntToSdtwo(J(BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole1+SdtwoToInt t)=J(d0+i)"))
(use "SdtwoInjIntToSdtwo")
;; ?^20:abs(J(d0+i))<=2
(use "JProp")
(simp (pf "BooleToInt boole1+SdtwoToInt t=d0+i"))
(use "Truth")
;; ?^22:BooleToInt boole1+SdtwoToInt t=d0+i
(inst-with-to "PsdInjId" (pt "d0") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzUvDAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,t]IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))

;; JKLrzUvDAuxK
(set-goal "allnc d0,i(Psd d0 -> Sdtwo i -> Sd(K(d0+i)))")
(assume "d0" "i" "Psdd0" "Sdtwoi")

(assert "exl boole1 PsdInj d0 boole1")
(use "PsdInjIntro")
(use "Psdd0")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp2")
(by-assume "ExHyp2" "t" "tProp")

(use "SdInjElim" (pt "IntToSd(K(BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole1+SdtwoToInt t)=K(d0+i)"))
(use "SdInjIntToSd")
;; ?^20:abs(K(d0+i))<=1
(use "KProp")
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs d0+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd0")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "BooleToInt boole1+SdtwoToInt t=d0+i"))
(use "Truth")
;; ?^32:BooleToInt boole1+SdtwoToInt t=d0+i
(inst-with-to "PsdInjId" (pt "d0") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzUvDAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,t]IntToSd(K(BooleToInt boole+SdtwoToInt t))

;; JKLrzUvD
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> allnc z2(
 y===(1#2)*z2 -> allnc z3(CoH z3 -> z2===(1#2)*z3 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0"
	"z2" "z2Prop"
        "z3" "CoHz3" "z3Prop")

;; (assert "exnc j j=J(d0+i)")
(assert "exr j(j=J(d0+i) andr Sdtwo j)")
(intro 0 (pt "J(d0+i)"))
(split)
(use "Truth")
(use "JKLrzUvDAuxJ")
(use "Psdd0")
(use "Sdtwoi")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

;; (assert "exnc k k=K(d0+i)")
(assert "exr k(k=K(d0+i) andr Sd k)")
(intro 0 (pt "K(d0+i)"))
(split)
(use "Truth")
(use "JKLrzUvDAuxK")
(use "Psdd0")
(use "Sdtwoi")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3"))

(assert "exl boole BooleToInt boole=d0")
(use "PsdToBooleToIntValue")
(use "Psdd0")
(assume "ExHypd0")
(by-assume "ExHypd0" "boole0" "boole0Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(use "jDef")

(split)
(use "kDef")

(split)
(use "CoHToCoG")
(use "CoHz3")

;; ?^47:y+(d0+i#4)===(1#4)*(z3+j)+k
(simpreal "z2Prop")
(simpreal "z3Prop")
;; ?^50:(1#2)*((1#2)*z3)+(d0+i#4)===(1#4)*(z3+j)+k
(use "RealEqSToEq")
(autoreal)
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^58:(1#4)*cs n+(d0+i#4)==(1#4)*(cs n+j)+k
(use "RatEqvTrans" (pt "(1#4)*cs n+(1#4)*RatPlus d0 i"))
(use "Truth")
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?^66:cs n+RatPlus d0 i==cs n+j+k*4
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
;; ?^70:d0+i=j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J(d0+i)+K(d0+i)*4=K(d0+i)*4+J(d0+i)"))
(use "KJProp")
(use "IntPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKLrzUvD")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,ah]
;;  cJKLrzUvDAuxJ boole t pair cJKLrzUvDAuxK boole t pair cCoHToCoG ah

(animate "JKLrzUvDAuxJ")
(animate "JKLrzUvDAuxK")

(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,ah]
;;  IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))pair 
;;  IntToSd(K(BooleToInt boole+SdtwoToInt t))pair cCoHToCoG ah

(deanimate "JKLrzUvDAuxJ")
(deanimate "JKLrzUvDAuxK")

;; Next JKLrzUv

;; JKLrzUv
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> allnc z2(
 CoH z2 -> y===(1#2)*z2 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d)))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0" "z2" "CoHz2" "z2Prop")
(inst-with-to "CoHClosure" (pt "z2") "CoHz2" "z2Cases")
(elim "z2Cases")
;; 5,6
(drop "z2Cases")

;; Subcase Lrz2
(assume "ExHypz2")
(by-assume "ExHypz2" "e" "eProp")
(by-assume "eProp" "z3" "ez3Prop")

(use-with "JKLrzUvFin"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0"
 (pt "z2") "CoHz2" "z2Prop"
 (pt "e") (pt "z3") "?" "?" "?")
(use "ez3Prop")
(use "ez3Prop")
(use "ez3Prop")

;; ?_6:exr x(CoH x andl z2===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(d0+i#4)===(1#4)*(z+j)+d)

(drop "z2Cases")

;; Subcase Uz2
(assume "ExHypz2")
(by-assume "ExHypz2" "z3" "z3Prop")

(use-with "JKLrzUvD"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0"
 (pt "z2") "z2Prop"
 (pt "z3") "?" "?")
(use "z3Prop")
(use "z3Prop")
;; Proof finished.
;; (cdp)
(save "JKLrzUv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [t,boole,ah]
;;  [case (cCoHClosure ah)
;;    (InL bg -> cJKLrzUvFin t boole clft bg crht bg)
;;    (InR ah -> cJKLrzUvD t boole ah)]

(animate "CoHClosure")
(animate "JKLrzUvFin")
(animate "JKLrzUvFinAuxJ")
(animate "JKLrzUvFinAuxK")
(animate "JKLrzUvD")

(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [t,boole,ah]
;;  [case (DesYprod ah)
;;    (InL bg -> 
;;    IntToSdtwo(J(BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd(K(BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;    cCoGPsdTimes crht bg clft bg)
;;    (InR ah0 -> 
;;    IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd(K(BooleToInt boole+SdtwoToInt t))pair cCoHToCoG ah0)]

(deanimate "CoHClosure")
(deanimate "JKLrzUvFin")
(deanimate "JKLrzUvFinAuxJ")
(deanimate "JKLrzUvFinAuxK")
(deanimate "JKLrzUvD")

;; Next JKLrz

;; JKLrz
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> CoG y ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0" "CoGy")
(inst-with-to "CoGClosure" (pt "y") "CoGy" "vCases")
(elim "vCases")
;; 5,6
(drop "vCases")

;; Case Lrv
(assume "ExHyp")
(by-assume "ExHyp" "e0" "e0Prop")
(by-assume "e0Prop" "z2" "e0z2Prop")

;; (pp "JKLrzLrv")
(use-with "JKLrzLrv"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0"
 (pt "e0") (pt "z2") "?" "?" "?")
(use "e0z2Prop")
(use "e0z2Prop")
(use "e0z2Prop")

;; ?_6:exr x(CoH x andl y===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(d0+i#4)===(1#4)*(z+j)+d)

(drop "vCases")

;; Case Uv
(assume "ExHyp")
(by-assume "ExHyp" "z2" "z2Prop")

;; (pp "JKLrzUv")
(use "JKLrzUv" (pt "z2"))
(use "Sdtwoi")
(use "Psdd0")
(use "z2Prop")
(use "z2Prop")
;; Proof finished.
;; (cdp)
(save "JKLrz")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [t,boole,ag]
;;  [case (cCoGClosure ag)
;;    (InL bg -> cJKLrzLrv t boole clft bg crht bg)
;;    (InR ah -> cJKLrzUv t boole ah)]

(animate "CoGClosure")
(animate "CoHClosure")
(animate "JKLrzLrvLr")
(animate "JKLrzLrvLrAuxJ")
(animate "JKLrzLrvLrAuxK")
(animate "JKLrzLrvU")
(animate "JKLrzLrvUAuxJ")
(animate "JKLrzLrvUAuxK")
(animate "JKLrzLrv")
(animate "JKLrzUvFin")
(animate "JKLrzUvFinAuxJ")
(animate "JKLrzUvFinAuxK")
(animate "JKLrzUvD")
(animate "JKLrzUv")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,ag]
;;  [case (DesYprod ag)
;;    (InL bg -> 
;;    [case (DesYprod crht bg)
;;      (InL bg0 -> 
;;      IntToSdtwo
;;      (J
;;       (~(BooleToInt clft bg0*BooleToInt clft bg)+2*BooleToInt clft bg+
;;        BooleToInt boole+
;;        SdtwoToInt t))pair 
;;      IntToSd
;;      (K
;;       (~(BooleToInt clft bg0*BooleToInt clft bg)+2*BooleToInt clft bg+
;;        BooleToInt boole+
;;        SdtwoToInt t))pair 
;;      cCoGPsdTimes(cCoGPsdTimes crht bg0 clft bg0)clft bg)
;;      (InR ah -> 
;;      IntToSdtwo(J(2*BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;      IntToSd(K(2*BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;      cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus clft bg))])
;;    (InR ah -> 
;;    [case (DesYprod ah)
;;      (InL bg -> 
;;      IntToSdtwo(J(BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;      IntToSd(K(BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;      cCoGPsdTimes crht bg clft bg)
;;      (InR ah0 -> 
;;      IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))pair 
;;      IntToSd(K(BooleToInt boole+SdtwoToInt t))pair cCoHToCoG ah0)])]

(deanimate "CoGClosure")
(deanimate "CoHClosure")
(deanimate "JKLrzLrvLr")
(deanimate "JKLrzLrvLrAuxJ")
(deanimate "JKLrzLrvLrAuxK")
(deanimate "JKLrzLrvU")
(deanimate "JKLrzLrvUAuxJ")
(deanimate "JKLrzLrvUAuxK")
(deanimate "JKLrzLrv")
(deanimate "JKLrzUvFin")
(deanimate "JKLrzUvFinAuxJ")
(deanimate "JKLrzUvFinAuxK")
(deanimate "JKLrzUvD")
(deanimate "JKLrzUv")

;; Next JKUzLrvLr

;; JKUzLrvLrAuxJ
(set-goal "allnc e,e0,i(
 Psd e -> Psd e0 -> Sdtwo i -> Sdtwo(J(e* ~e0+2*e0+i)))")
(assume "e" "e0" "i" "Psde" "Psde0" "Sdtwoi")

(assert "exl boole1 PsdInj e boole1")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl boole2 PsdInj e0 boole2")
(use "PsdInjIntro")
(use "Psde0")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdtwoInjElim"
     (pt "IntToSdtwo(J(BooleToInt boole1* ~(BooleToInt boole2)+
                     2*BooleToInt boole2+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole1* ~(BooleToInt boole2)+
             2*BooleToInt boole2+SdtwoToInt t)=
           J(e* ~e0+2*e0+i)"))
(use "SdtwoInjIntToSdtwo")
;; ?^27:abs(J(e* ~e0+2*e0+i))<=2
(use "JProp")
(simp (pf "BooleToInt boole1* ~(BooleToInt boole2)+2*BooleToInt boole2+
           SdtwoToInt t=e* ~e0+2*e0+i"))
(use "Truth")
;; ?^29:BooleToInt boole1* ~(BooleToInt boole2)+2*BooleToInt boole2+
;;      SdtwoToInt t=
;;      e* ~e0+2*e0+i
(inst-with-to "PsdInjId" (pt "e") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "e0") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzLrvLrAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,boole0,t]
;;  IntToSdtwo
;;  (J(~(BooleToInt boole*BooleToInt boole0)+2*BooleToInt boole0+SdtwoToInt t))

;; JKUzLrvLrAuxK
(set-goal "allnc e,e0,i(
 Psd e -> Psd e0 -> Sdtwo i -> Sd(K(e* ~e0+2*e0+i)))")
(assume "e" "e0" "i" "Psde" "Psde0" "Sdtwoi")

(assert "exl boole1 PsdInj e boole1")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl boole2 PsdInj e0 boole2")
(use "PsdInjIntro")
(use "Psde0")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdInjElim"
     (pt "IntToSd(K(BooleToInt boole1* ~(BooleToInt boole2)+
                     2*BooleToInt boole2+SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole1* ~(BooleToInt boole2)+
             2*BooleToInt boole2+SdtwoToInt t)=
           K(e* ~e0+2*e0+i)"))
(use "SdInjIntToSd")
;; ?^27:abs(K(e* ~e0+2*e0+i))<=1
(use "KProp")
(use "IntLeTrans" (pt "IntP 3+IntP 2"))
(use "IntLeTrans" (pt "abs(e* ~e0+2*e0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs(e* ~e0)+abs(2*e0)"))
(use "IntLeAbsPlus")
(ng #t)
(simp "PsdToAbsOne")
(simp "PsdToAbsOne")
(use "Truth")
(use "Psde0")
(use "Psde")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "BooleToInt boole1* ~(BooleToInt boole2)+2*BooleToInt boole2+
      SdtwoToInt t=e* ~e0+2*e0+i"))
(use "Truth")
;; ?^46:BooleToInt boole1* ~(BooleToInt boole2)+2*BooleToInt boole2+
;;      SdtwoToInt t=
;;      e* ~e0+2*e0+i
(inst-with-to "PsdInjId" (pt "e") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "PsdInjId" (pt "e0") (pt "boole2") "boole2Prop" "PsdInjIdInst2")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "PsdInjIdInst2")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzLrvLrAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,boole0,t]
;;  IntToSd
;;  (K(~(BooleToInt boole*BooleToInt boole0)+2*BooleToInt boole0+SdtwoToInt t))

;; JKUzLrvLr
(set-goal "allnc i,y(Sdtwo i -> allnc e0,z2(
 Psd e0 -> y===(1#2)*(z2+IntN 1)* ~e0 -> allnc e,z3(
 Psd e -> CoG z3 -> z2===(1#2)*(z3+IntN 1)* ~e ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))))")
(assume "i" "y" "Sdtwoi"
	"e0" "z2" "Psde0" "e0z2Prop"
        "e" "z3" "Psde" "CoGz3" "ez3Prop")

;; (assert "exnc j j=J(e* ~e0+2*e0+i)")
(assert "exr j(j=J(e* ~e0+2*e0+i) andr Sdtwo j)")
(intro 0 (pt "J(e* ~e0+2*e0+i)"))
(split)
(use "Truth")
(use "JKUzLrvLrAuxJ")
(use "Psde")
(use "Psde0")
(use "Sdtwoi")

;; (assert "exnc k k=K(e* ~e0+2*e0+i)")
(assert "exr k(k=K(e* ~e0+2*e0+i) andr Sd k)")
(intro 0 (pt "K(e* ~e0+2*e0+i)"))
(split)
(use "Truth")
(use "JKUzLrvLrAuxK")
(use "Psde")
(use "Psde0")
(use "Sdtwoi")

(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3*e*e0"))

(assert "exl boole BooleToInt boole=e")
(use "PsdToBooleToIntValue")
(use "Psde")
(assume "ExHype")
(by-assume "ExHype" "boole" "booleProp")

(assert "exl boole BooleToInt boole=e0")
(use "PsdToBooleToIntValue")
(use "Psde0")
(assume "ExHype0")
(by-assume "ExHype0" "boole1" "boole1Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(use "jDef")

(split)
(use "kDef")

(split)
(use "CoGPsdTimes")
(use "CoGPsdTimes")
(use "CoGz3")
(use "Psde")
(use "Psde0")

;; ?^56:y+(i#4)===(1#4)*(z3*e*e0+j)+k
(simpreal "e0z2Prop")
(simpreal "ez3Prop")

;; ?^62:(1#2)*((1#2)*(z3+IntN 1)* ~e+IntN 1)* ~e0+(i#4)===(1#4)*(z3*e*e0+j)+k
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^74:(1#2)*((1#2)*(cs n+IntN 1)* ~e+IntN 1)* ~e0+(i#4)==
;;      (1#4)*(cs n*e*e0+j)+k
(use "RatEqvTrans"
 (pt "(1#2)*(((1#2)*((cs n+IntN 1)* ~e)+IntN 1)* ~e0)+(i#4)"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(simp "RatTimesIntNL")
(simp (pf "~(RatTimes 1~e)=(e#1)"))
(simp (pf "~(RatTimes 1~e0)=(e0#1)"))
;; ?^83:(1#2)*((1#2)*(cs n* ~e+e)* ~e0+e0)+(i#4)==(1#4)*(cs n*e*e0+j)+k
(use "RatEqvTrans" (pt "(1#2)*((1#2)*((cs n* ~e+e)* ~e0)+e0)+(i#4)"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat
 (pf "(1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+e0==
      (1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+(1#2)*(2*e0)"))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp (pf "(1#2)*(1#2)=(1#4)"))
(simp (pf "(i#4)=(1#4)*i"))
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?^101:cs n* ~e* ~e0+RatTimes e~e0+2*e0+i==cs n*e*e0+j+k*4
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp (pf "RatTimes~e~e0=RatTimes e e0"))
(simprat (pf "cs n*RatTimes e e0+RatTimes e~e0+2*e0+i==
              cs n*RatTimes e e0+(RatTimes e~e0+2*e0+i)"))
(simp (pf "cs n*RatTimes e e0+j+k*4=cs n*RatTimes e e0+(j+k*4)"))
(use "RatPlusCompat")
(use "Truth")
;; ?^111:RatTimes e~e0+2*e0+i==j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J(e* ~e0+2*e0+i)+K(e* ~e0+2*e0+i)*4=
           K(e* ~e0+2*e0+i)*4+J(e* ~e0+2*e0+i)"))
(simp "<-" "KJProp")
;; ?_116:RatTimes e~e0+2*e0+i==e* ~e0+2*e0+i
(use "Truth")
(use "IntPlusComm")
;; ?^109:cs n*RatTimes e e0+j+k*4=cs n*RatTimes e e0+(j+k*4)
(simp "<-" "RatPlusAssoc")
(use "Truth")
;; ?^107:cs n*RatTimes e e0+RatTimes e~e0+2*e0+i==
;;       cs n*RatTimes e e0+(RatTimes e~e0+2*e0+i)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?^89:(1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+e0==
;;      (1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+(1#2)*(2*e0)
(use "RatPlusCompat")
(use "Truth")
(use "IntTimesComm")
;; ?^84:~(RatTimes 1~e0)=e0
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzLrvLr")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

(animate "JKUzLrvLrAuxJ")
(animate "JKUzLrvLrAuxK")

(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,boole0,ag]
;;  IntToSdtwo
;;  (J(~(BooleToInt boole0*BooleToInt boole)+2*BooleToInt boole+SdtwoToInt t))pair 
;;  IntToSd
;;  (K(~(BooleToInt boole0*BooleToInt boole)+2*BooleToInt boole+SdtwoToInt t))pair 
;;  cCoGPsdTimes(cCoGPsdTimes ag boole0)boole

(deanimate "JKUzLrvLrAuxJ")
(deanimate "JKUzLrvLrAuxK")

;; Next JKUzLrvU

;; JKUzLrvUAuxJ
(set-goal "allnc e0,i(Psd e0 -> Sdtwo i -> Sdtwo(J(2*e0+i)))")
(assume "e0" "i" "Psde0" "Sdtwoi")

(assert "exl boole1 PsdInj e0 boole1")
(use "PsdInjIntro")
(use "Psde0")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdtwoInjElim" (pt "IntToSdtwo(J(2*BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "J(2*BooleToInt boole1+SdtwoToInt t)=J(2*e0+i)"))
(use "SdtwoInjIntToSdtwo")
;; ?^20:abs(J(2*e0+i))<=2
(use "JProp")
(simp (pf "2*BooleToInt boole1+SdtwoToInt t=2*e0+i"))
(use "Truth")
;; ?^22:2*BooleToInt boole1+SdtwoToInt t=2*e0+i
(inst-with-to "PsdInjId" (pt "e0") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzLrvUAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,t]IntToSdtwo(J(2*BooleToInt boole+SdtwoToInt t))

;; JKUzLrvUAuxK
(set-goal "allnc e0,i(Psd e0 -> Sdtwo i -> Sd(K(2*e0+i)))")
(assume "e0" "i" "Psde0" "Sdtwoi")

(assert "exl boole1 PsdInj e0 boole1")
(use "PsdInjIntro")
(use "Psde0")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdInjElim" (pt "IntToSd(K(2*BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "K(2*BooleToInt boole1+SdtwoToInt t)=K(2*e0+i)"))
(use "SdInjIntToSd")
;; ?^20:abs(K(2*e0+i))<=1
(use "KProp")
;; ?^21:abs(2*e0+i)<=6
(use "IntLeTrans" (pt "IntP 2+IntP 2"))
(use "IntLeTrans" (pt "abs(2*e0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psde0")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "2*BooleToInt boole1+SdtwoToInt t=2*e0+i"))
(use "Truth")
;; ?^33:2*BooleToInt boole1+SdtwoToInt t=2*e0+i
(inst-with-to "PsdInjId" (pt "e0") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzLrvUAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,t]IntToSd(K(2*BooleToInt boole+SdtwoToInt t))

;; JKUzLrvU
(set-goal "allnc i,y(Sdtwo i -> allnc e0,z2(
 Psd e0 -> y===(1#2)*(z2+IntN 1)* ~e0 -> allnc z3(
 CoH z3 -> z2===(1#2)*z3 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))))")
(assume "i" "y" "Sdtwoi"
	"e0" "z2" "Psde0" "e0z2Prop"
        "z3" "CoHz3" "z3Prop")

;; (assert "exnc j j=J(2*e0+i)")
(assert "exr j(j=J(2*e0+i) andr Sdtwo j)")
(intro 0 (pt "J(2*e0+i)"))
(split)
(use "Truth")
(use "JKUzLrvUAuxJ")
(use "Psde0")
(use "Sdtwoi")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exr k(k=K(2*e0+i) andr Sd k)")
(intro 0 (pt "K(2*e0+i)"))
(split)
(use "Truth")
(use "JKUzLrvUAuxK")
(use "Psde0")
(use "Sdtwoi")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3* ~e0"))

(assert "exl boole0 BooleToInt boole0=e0")
(use "PsdToBooleToIntValue")
(use "Psde0")
(assume "ExHype0")
(by-assume "ExHype0" "boole1" "boole1Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(use "jDef")

(split)
(use "kDef")

(split)
;; ?_46:CoG(z3* ~e0)
(use "CoGPsdTimes")
(use "CoHToCoG")
(use "CoHz3")
(use "PsdUMinus")
(use "Psde0")

;; ?47:y+(i#4)===(1#4)*(z3* ~e0+j)+k
(simpreal "e0z2Prop")
(simpreal "z3Prop")
;; ?^53:(1#2)*((1#2)*z3+IntN 1)* ~e0+(i#4)===(1#4)*(z3* ~e0+j)+k
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^65:~((1#2)*((1#2)*cs n+IntN 1)*e0)+(i#4)==(1#4)*(~(cs n*e0)+j)+k
(use "RatEqvTrans" (pt "(1#2)*(((1#2)*cs n+IntN 1)* ~e0)+(1#4)*i")) ;or (i#4)
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(simp (pf "~(RatTimes 1~e0)=(e0#1)"))
;; ?^70:(1#2)*((1#2)*cs n* ~e0+e0)+(1#4)*i==(1#4)*(~(cs n*e0)+j)+k
(simp (pf "(1#2)*cs n* ~e0=(1#2)*(cs n* ~e0)"))
(simprat (pf "(1#2)*((1#2)*(cs n* ~e0)+e0)==
              (1#2)*((1#2)*(cs n* ~e0)+(1#2)*(2*e0))"))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp (pf "(1#2)*(1#2)=(1#4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?^85:cs n* ~e0+2*e0+i== ~(cs n*e0)+j+k*4
(simp (pf "cs n* ~e0+2*e0+i=cs n* ~e0+(RatPlus(2*e0)i)"))
(simp (pf "cs n* ~e0+j+k*4=cs n* ~e0+(RatPlus j(k*4))"))
(use "RatPlusCompat")
(use "Truth")
;; ?^91:2*e0+i==j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J(2*e0+i)+K(2*e0+i)*4=K(2*e0+i)*4+J(2*e0+i)"))
(simp "<-" "KJProp")
(use "Truth")
;; ?^95:J(2*e0+i)+K(2*e0+i)*4=K(2*e0+i)*4+J(2*e0+i)
(use "IntPlusComm")
;; ?^89:cs n* ~e0+j+k*4=cs n* ~e0+RatPlus j(k*4)
(simp "RatPlusAssoc")
(use "Truth")
;; ?^87:cs n* ~e0+2*e0+i=cs n* ~e0+RatPlus(2*e0)i
(simp "RatPlusAssoc")
(use "Truth")
;; ?^82:k==(1#4)*(k*4)
(ng #t)
(use "Truth")
(use "Truth")
;; ?^75:(1#2)*((1#2)*(cs n* ~e0)+e0)==(1#2)*((1#2)*(cs n* ~e0)+(1#2)*(2*e0))
(use "RatTimesCompat")
(use "Truth")
;; ?^101:(1#2)*(cs n* ~e0)+e0==(1#2)*(cs n* ~e0)+(1#2)*(2*e0)
(ng #t)
(use "IntTimesComm")
;; ?^73:(1#2)*cs n* ~e0=(1#2)*(cs n* ~e0)
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzLrvU")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,ah]
;;  cJKUzLrvUAuxJ boole t pair 
;;  cJKUzLrvUAuxK boole t pair cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole)

(animate "JKUzLrvUAuxJ")
(animate "JKUzLrvUAuxK")

(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,ah]
;;  IntToSdtwo(J(2*BooleToInt boole+SdtwoToInt t))pair 
;;  IntToSd(K(2*BooleToInt boole+SdtwoToInt t))pair 
;;  cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole)

(deanimate "JKUzLrvUAuxJ")
(deanimate "JKUzLrvUAuxK")

;; Next JKUzLrv

;; JKUzLrv
(set-goal "allnc i,y(Sdtwo i -> allnc e0,z2(
 Psd e0 -> CoG z2 -> y===(1#2)*(z2+IntN 1)* ~e0 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d)))")
(assume "i" "y" "Sdtwoi"
	"e0" "z2" "Psde0" "CoGz2" "e0z2Prop")
(inst-with-to "CoGClosure" (pt "z2") "CoGz2" "z2Cases")
(elim "z2Cases")
;; 5,6
(drop "z2Cases")

;; Subcase Lrz2
(assume "ExHypz2")
(by-assume "ExHypz2" "e" "eProp")
(by-assume "eProp" "z3" "ez3Prop")
(use-with "JKUzLrvLr"
 (pt "i") (pt "y") "Sdtwoi"
 (pt "e0") (pt "z2") "Psde0" "e0z2Prop"
 (pt "e") (pt "z3") "?" "?" "?")
(use "ez3Prop")
(use "ez3Prop")
(use "ez3Prop")

;; ?_6:exr x(CoH x andl z2===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(i#4)===(1#4)*(z+j)+d)

(drop "z2Cases")

;; Subcase Uz2
(assume "ExHypz2")
(by-assume "ExHypz2" "z3" "z3Prop")

(use-with "JKUzLrvU"
 (pt "i") (pt "y") "Sdtwoi"
 (pt "e0") (pt "z2") "Psde0" "e0z2Prop"
 (pt "z3") "?" "?")
(use "z3Prop")
(use "z3Prop")
;; Proof finished.
;; (cdp)
(save "JKUzLrv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,ag]
;;  [case (cCoGClosure ag)
;;    (InL bg -> cJKUzLrvLr t boole clft bg crht bg)
;;    (InR ah -> cJKUzLrvU t boole ah)]

(animate "JKUzLrvLr")
(animate "JKUzLrvLrAuxJ")
(animate "JKUzLrvLrAuxK")
(animate "JKUzLrvU")
(animate "JKUzLrvUAuxJ")
(animate "JKUzLrvUAuxK")

(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [t,boole,ag]
;;  [case (cCoGClosure ag)
;;    (InL bg -> 
;;    IntToSdtwo
;;    (J
;;     (~(BooleToInt clft bg*BooleToInt boole)+2*BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd
;;    (K
;;     (~(BooleToInt clft bg*BooleToInt boole)+2*BooleToInt boole+SdtwoToInt t))pair 
;;    cCoGPsdTimes(cCoGPsdTimes crht bg clft bg)boole)
;;    (InR ah -> 
;;    IntToSdtwo(J(2*BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd(K(2*BooleToInt boole+SdtwoToInt t))pair 
;;    cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole))]

(deanimate "JKUzLrvLr")
(deanimate "JKUzLrvLrAuxJ")
(deanimate "JKUzLrvLrAuxK")
(deanimate "JKUzLrvU")
(deanimate "JKUzLrvUAuxJ")
(deanimate "JKUzLrvUAuxK")

;; Next JKUzUvFin

;; JKUzUvFinAuxJ
(set-goal "allnc e,i(Psd e -> Sdtwo i -> Sdtwo(J(e+i)))")
(assume "e" "i" "Psde" "Sdtwoi")

(assert "exl boole1 PsdInj e boole1")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdtwoInjElim" (pt "IntToSdtwo(J(BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole1+SdtwoToInt t)=J(e+i)"))
(use "SdtwoInjIntToSdtwo")
;; ?^20:abs(J(e+i))<=2
(use "JProp")
(simp (pf "BooleToInt boole1+SdtwoToInt t=e+i"))
(use "Truth")
;; ?^22:BooleToInt boole1+SdtwoToInt t=e+i
(inst-with-to "PsdInjId" (pt "e") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzUvFinAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [boole,t]IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))

;; JKUzUvFinAuxK
(set-goal "allnc e,i(Psd e -> Sdtwo i -> Sd(K(e+i)))")
(assume "e" "i" "Psde" "Sdtwoi")

(assert "exl boole1 PsdInj e boole1")
(use "PsdInjIntro")
(use "Psde")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")

(use "SdInjElim" (pt "IntToSd(K(BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole1+SdtwoToInt t)=K(e+i)"))
(use "SdInjIntToSd")
;; ?^20:abs(K(e+i))<=1
(use "KProp")
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs e+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(simp "PsdToAbsOne")
(use "Truth")
(use "Psde")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "BooleToInt boole1+SdtwoToInt t=e+i"))
(use "Truth")
;; ?^32:BooleToInt boole1+SdtwoToInt t=e+i
(inst-with-to "PsdInjId" (pt "e") (pt "boole1") "boole1Prop" "PsdInjIdInst1")
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "PsdInjIdInst1")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzUvFinAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [boole,t]IntToSd(K(BooleToInt boole+SdtwoToInt t))

;; JKUzUvFin
(set-goal "allnc i,y(Sdtwo i -> allnc z2(
 y===(1#2)*z2 -> allnc e,z3(
 Psd e -> CoG z3 -> z2===(1#2)*(z3+1)*e ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))))")
(assume "i" "y" "Sdtwoi"
	"z2" "z2Prop"
        "e" "z3" "Psde" "CoGz3" "ez3Prop")

;; (assert "exnc j j=J(e+i)")
(assert "exr j(j=J(e+i) andr Sdtwo j)")
(intro 0 (pt "J(e+i)"))
(split)
(use "Truth")
(use "JKUzUvFinAuxJ")
(use "Psde")
(use "Sdtwoi")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

;; (assert "exnc k k=K(e+i)")
(assert "exr k(k=K(e+i) andr Sd k)")
(intro 0 (pt "K(e+i)"))
(split)
(use "Truth")
(use "JKUzUvFinAuxK")
(use "Psde")
(use "Sdtwoi")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3*e"))

(assert "exl boole BooleToInt boole=e")
(use "PsdToBooleToIntValue")
(use "Psde")
(assume "ExHype")
(by-assume "ExHype" "boole" "booleProp")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(use "jDef")

(split)
(use "kDef")

(split)
(use "CoGPsdTimes")
(use "CoGz3")
(use "Psde")

;; ?^47:y+(i#4)===(1#4)*(z3*e+j)+k
(simpreal "z2Prop")
(simpreal "ez3Prop")
;; ?^51:(1#2)*((1#2)*(z3+1)*e)+(i#4)===(1#4)*(z3*e+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^63:(1#4)*(cs n+1)*e+(i#4)==(1#4)*(cs n*e+j)+k
(use "RatEqvTrans" (pt "(1#4)*(cs n+1)*e+(1#4)*i"))
(use "Truth")
;; ?^65:(1#4)*(cs n+1)*e+(1#4)*i==(1#4)*(cs n*e+j)+k
(simp (pf "(1#4)*(cs n+1)*e=(1#4)*((cs n+1)*e)"))
(simprat "RatTimesPlusDistrLeft")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?^74:cs n*e+RatTimes 1 e+i==cs n*e+j+k*4
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?^78:RatTimes 1 e+i==RatPlus j(k*4)
(simp "jDef")
(simp "kDef")
(simp (pf "RatPlus(J(e+i))(K(e+i)*4)=K(e+i)*4+J(e+i)"))
(simp "<-" "KJProp")
;; ?^83:RatTimes 1 e+i==e+i
(use "Truth")
(use "IntPlusComm")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzUvFin")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,ag]
;;  cJKUzUvFinAuxJ boole t pair 
;;  cJKUzUvFinAuxK boole t pair cCoGPsdTimes ag boole

(animate "JKUzUvFinAuxJ")
(animate "JKUzUvFinAuxK")

(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,boole,ag]
;;  IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))pair 
;;  IntToSd(K(BooleToInt boole+SdtwoToInt t))pair cCoGPsdTimes ag boole

(deanimate "JKUzUvFinAuxJ")
(deanimate "JKUzUvFinAuxK")

;; Next JKUzUvD

;; JKUzUvDAuxJ
(set-goal "allnc i(Sdtwo i -> Sdtwo(J i))")
(assume "i" "Sdtwoi")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp2")
(by-assume "ExHyp2" "t" "tProp")

(use "SdtwoInjElim" (pt "IntToSdtwo(J(SdtwoToInt t))"))
(simp (pf "J(SdtwoToInt t)=J i"))
(use "SdtwoInjIntToSdtwo")
;; ?^13:abs(J i)<=2
(use "JProp")
(simp (pf "SdtwoToInt t=i"))
(use "Truth")
;; ?^15:SdtwoToInt t=i
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzUvDAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t]IntToSdtwo(J(SdtwoToInt t))

;; JKUzUvDAuxK
(set-goal "allnc i(Sdtwo i -> Sd(K i))")
(assume "i" "Sdtwoi")

(assert "exl t SdtwoInj i t")
(use "SdtwoInjIntro")
(use "Sdtwoi")
(assume "ExHyp2")
(by-assume "ExHyp2" "t" "tProp")

(use "SdInjElim" (pt "IntToSd(K(SdtwoToInt t))"))
(simp (pf "K(SdtwoToInt t)=K i"))
(use "SdInjIntToSd")
;; ?^13:abs(K i)<=1
(use "KProp")
(use "IntLeTrans" (pt "IntP 2"))
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "SdtwoToInt t=i"))
(use "Truth")
;; ?^19:SdtwoToInt t=i
(inst-with-to "SdtwoInjId" (pt "i") (pt "t") "tProp" "SdtwoInjIdInst")
(simp "SdtwoInjIdInst")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzUvDAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t]IntToSd(K(SdtwoToInt t))

;; JKUzUvD
(set-goal "allnc i,y(Sdtwo i -> allnc z2(
 y===(1#2)*z2 -> allnc z3(
 CoH z3 -> z2===(1#2)*z3 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))))")
(assume "i" "y" "Sdtwoi"
	"z2" "z2Prop"
        "z3" "CoHz3" "z3Prop")

;; (assert "exnc j j=J(i)")
(assert "exr j(j=J(i) andr Sdtwo j)")
(intro 0 (pt "J i"))
(split)
(use "Truth")
(use "JKUzUvDAuxJ")
(use "Sdtwoi")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

;; (assert "exnc k k=K(i)")
(assert "exr k(k=K i andr Sd k)")
(intro 0 (pt "K i"))
(split)
(use "Truth")
(use "JKUzUvDAuxK")
(use "Sdtwoi")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3"))

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(use "jDef")

(split)
(use "kDef")

(split)
(use "CoHToCoG")
(use "CoHz3")

;; ?^38:y+(i#4)===(1#4)*(z3+j)+k
(simpreal "z2Prop")
(simpreal "z3Prop")
;; ?^41:(1#2)*((1#2)*z3)+(i#4)===(1#4)*(z3+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^49:(1#4)*cs n+(i#4)==(1#4)*(cs n+j)+k
(use "RatEqvTrans" (pt "(1#4)*cs n+(1#4)*i"))
(use "Truth")
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?^57:cs n+i==cs n+j+k*4
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
;; ?^61:i=j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J i+K i*4=K i*4+J i"))
(use "KJProp")
(use "IntPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "JKUzUvD")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,ah]cJKUzUvDAuxJ t pair cJKUzUvDAuxK t pair cCoHToCoG ah

(animate "JKUzUvDAuxJ")
(animate "JKUzUvDAuxK")

(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [t,ah]
;;  IntToSdtwo(J(SdtwoToInt t))pair IntToSd(K(SdtwoToInt t))pair cCoHToCoG ah

;; Next JKUzUv

;; JKUzUv
(set-goal "allnc i,y(Sdtwo i -> allnc z2(
 CoH z2 -> y===(1#2)*z2 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d)))")
(assume "i" "y" "Sdtwoi" "z2" "CoHz2" "z2Prop")
(inst-with-to "CoHClosure" (pt "z2") "CoHz2" "z2Cases")
(elim "z2Cases")
;; 5,6
(drop "z2Cases")

;; Subcase Lrz2
(assume "ExHypz2")
(by-assume "ExHypz2" "e" "eProp")
(by-assume "eProp" "z3" "ez3Prop")

(use-with "JKUzUvFin"
 (pt "i") (pt "y") "Sdtwoi"
 (pt "z2") "z2Prop"
 (pt "e") (pt "z3") "?" "?" "?")
(use "ez3Prop")
(use "ez3Prop")
(use "ez3Prop")

;; ?_6:exr x(CoH x andl z2===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(i#4)===(1#4)*(z+j)+d)

(drop "z2Cases")

;; Subcase Uz2
(assume "ExHypz2")
(by-assume "ExHypz2" "z3" "z3Prop")

(use-with "JKUzUvD"
 (pt "i") (pt "y") "Sdtwoi"
 (pt "z2") "z2Prop"
 (pt "z3") "?" "?")
(use "z3Prop")
(use "z3Prop")
;; Proof finished.
;; (cdp)
(save "JKUzUv")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [t,ah]
;;  [case (cCoHClosure ah)
;;    (InL bg -> cJKUzUvFin t clft bg crht bg)
;;    (InR ah -> cJKUzUvD t ah)]

(animate "CoHClosure")
(animate "JKUzUvFin")
(animate "JKUzUvFinAuxJ")
(animate "JKUzUvFinAuxK")
(animate "JKUzUvD")
(animate "JKUzUvDAuxJ")
(animate "JKUzUvDAuxK")

(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [t,ah]
;;  [case (DesYprod ah)
;;    (InL bg -> 
;;    IntToSdtwo(J(BooleToInt clft bg+SdtwoToInt t))pair 
;;    IntToSd(K(BooleToInt clft bg+SdtwoToInt t))pair 
;;    cCoGPsdTimes crht bg clft bg)
;;    (InR ah0 -> 
;;    IntToSdtwo(J(SdtwoToInt t))pair 
;;    IntToSd(K(SdtwoToInt t))pair cCoHToCoG ah0)]

(deanimate "CoHClosure")
(deanimate "JKUzUvFin")
(deanimate "JKUzUvFinAuxJ")
(deanimate "JKUzUvFinAuxK")
(deanimate "JKUzUvD")
(deanimate "JKUzUvDAuxJ")
(deanimate "JKUzUvDAuxK")

;; Next JKUz

;; JKUz
(set-goal "allnc i,y(Sdtwo i -> CoG y ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))")
(assume "i" "y" "Sdtwoi" "CoGy")
(inst-with-to "CoGClosure" (pt "y") "CoGy" "vCases")
(elim "vCases")
;; 5,6
(drop "vCases")

;; Case Lrv
(assume "ExHyp")
(by-assume "ExHyp" "e0" "e0Prop")
(by-assume "e0Prop" "z2" "e0z2Prop")

(use-with "JKUzLrv"
 (pt "i") (pt "y") "Sdtwoi"
 (pt "e0") (pt "z2") "?" "?" "?")
(use "e0z2Prop")
(use "e0z2Prop")
(use "e0z2Prop")

;; ?_6:exr x(CoH x andl y===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(i#4)===(1#4)*(z+j)+d)

(drop "vCases")

;; Case Uv
(assume "ExHyp")
(by-assume "ExHyp" "z2" "z2Prop")

;; (pp "JKUzUv")
(use "JKUzUv" (pt "z2"))
(use "Sdtwoi")
(use "z2Prop")
(use "z2Prop")
;; Proof finished.
;; (cdp)
(save "JKUz")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [t,ag][case (cCoGClosure ag)
;;    (InL bg -> cJKUzLrv t clft bg crht bg)
;;    (InR ah -> cJKUzUv t ah)]

(animate "CoGClosure")
(animate "CoHClosure")
(animate "JKUzLrvLr")
(animate "JKUzLrvLrAuxJ")
(animate "JKUzLrvLrAuxK")
(animate "JKUzLrvU")
(animate "JKUzLrvUAuxJ")
(animate "JKUzLrvUAuxK")
(animate "JKUzLrv")
(animate "JKUzUvFin")
(animate "JKUzUvFinAuxJ")
(animate "JKUzUvFinAuxK")
(animate "JKUzUvD")
(animate "JKUzUvDAuxJ")
(animate "JKUzUvDAuxK")
(animate "JKUzUv")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,ag][case (DesYprod ag)
;;    (InL bg -> [case (DesYprod crht bg)
;;      (InL bg0 -> IntToSdtwo(J(~(BooleToInt clft bg0*
;;                                 BooleToInt clft bg)+
;;                               2*BooleToInt clft bg+
;;                               SdtwoToInt t))pair 
;;                  IntToSd(K(~(BooleToInt clft bg0*
;;                              BooleToInt clft bg)+
;;                            2*BooleToInt clft bg+
;;                            SdtwoToInt t))pair 
;;                  cCoGPsdTimes
;;                   (cCoGPsdTimes crht bg0 clft bg0)clft bg)
;;      (InR ah -> IntToSdtwo(J(2*BooleToInt clft bg+
;;                              SdtwoToInt t))pair 
;;                 IntToSd(K(2*BooleToInt clft bg+
;;                           SdtwoToInt t))pair 
;;                 cCoGPsdTimes(cCoHToCoG ah)
;; 		            (cPsdUMinus clft bg))])
;;    (InR ah -> [case (DesYprod ah)
;;      (InL bg -> IntToSdtwo(J(BooleToInt clft bg+
;;                              SdtwoToInt t))pair 
;;                 IntToSd(K(BooleToInt clft bg+
;;                           SdtwoToInt t))pair 
;;                 cCoGPsdTimes crht bg clft bg)
;;      (InR ah0 -> IntToSdtwo(J(SdtwoToInt t))pair 
;;                  IntToSd(K(SdtwoToInt t))pair
;;                  cCoHToCoG ah0)])]

(deanimate "CoGClosure")
(deanimate "CoHClosure")
(deanimate "JKUzLrvLr")
(deanimate "JKUzLrvLrAuxJ")
(deanimate "JKUzLrvLrAuxK")
(deanimate "JKUzLrvU")
(deanimate "JKUzLrvUAuxJ")
(deanimate "JKUzLrvUAuxK")
(deanimate "JKUzLrv")
(deanimate "JKUzUvFin")
(deanimate "JKUzUvFinAuxJ")
(deanimate "JKUzUvFinAuxK")
(deanimate "JKUzUvD")
(deanimate "JKUzUvDAuxJ")
(deanimate "JKUzUvDAuxK")
(deanimate "JKUzUv")

;; 2019-08-19.  Done up to this point.
;; We show CoGMultcSatCoICl, using JKLrz and JKUz.  This is split into
;; CoGMultcSatCoIClLrxLrz using JKLrz
;; CoGMultcSatCoIClLrxUz  using JKUz
;; CoGMultcSatCoIClUxLrz  using JKLrz
;; CoGMultcSatCoIClUxUz   using JKUz

;; CoGMultcSatCoIClLrxLrz
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> allnc d1,x1(
 Psd d1 -> CoG x1 -> x===(1#2)*(x1+IntN 1)* ~d1 -> allnc d0,z1(
 Psd d0 -> CoG z1 -> z===(1#2)*(z1+IntN 1)* ~d0 ->
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi"
	"d1" "x1" "Psdd1" "CoGx1" "d1x1Prop"
	"d0" "z1" "Psdd0" "CoGz1" "d0z1Prop")

;; Substitute x===(1#2)*(x1+IntN 1)* ~d1 and z===(1#2)*(z1+IntN 1)* ~d0
(assert "(1#4)*(x*y+z+i)===
(1#4)*(((1#2)*(x1+IntN 1)* ~d1)*y+((1#2)*(z1+IntN 1)* ~d0)+i)")
(simpreal "d1x1Prop")
(simpreal "d0z1Prop")
(use "RealEqRefl")
(realproof)
(assume "Eq1")
;; Prepare for application of CoGAvcToCoG and JKLrz
(assert "(1#4)*(((1#2)*(x1+IntN 1)* ~d1)*y+((1#2)*(z1+IntN 1)* ~d0)+i)===
         (1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1* ~d0+i)+(d0+i#4)))")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^22:(1#4)*(~((1#2)*(as n+IntN 1)*d1*bs n)+ ~((1#2)*(cs n+IntN 1)*d0)+i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+(d0+i#4))
;; Replace first i by (1#2)*RatPlus i i, and prepare for taking (1#2) out
(use "RatEqvTrans" 
 (pt "(1#4)*(~((1#2)*(as n+IntN 1)*d1*bs n)+ ~(1#2)*((cs n+IntN 1)*d0)+
      (1#2)*RatPlus i i)"))
(ng #t)
(simp (pf "IntP 2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; Similarly replace (d0+i#4) by (1#4)*RatPlus d0 i.
(use "RatEqvTrans" 
  (pt "(1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+
       (1#4)*RatPlus d0 i)"))
;; ?^29:(1#4)*
;;      (~((1#2)*(as n+IntN 1)*d1*bs n)+ ~(1#2)*((cs n+IntN 1)*d0)+
;;       (1#2)*RatPlus i i)==
;;      (1#2)*
;;      (~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+(1#4)*RatPlus d0 i)
(simp "<-" "RatTimes3RewRule")
(simp "<-" "RatTimes3RewRule")
(simp "<-" "RatTimes3RewRule")
(simp (pf "~(1#2)*((cs n+IntN 1)*d0)= (1#2)* ~((cs n+IntN 1)*d0)"))
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
;; ?^50:(as n+IntN 1)*d1* ~(bs n)+ ~((cs n+IntN 1)*d0)+RatPlus i i==
;;      as n*(d1* ~(bs n))+(bs n*d1+cs n* ~d0+i)+RatPlus d0 i
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
;; ?^53:as n*d1* ~(bs n)+RatTimes IntN 1 d1* ~(bs n)+ 
;;      ~(cs n*d0+RatTimes IntN 1 d0)+
;;      RatPlus i i==
;;      as n*(d1* ~(bs n))+(bs n*d1+cs n* ~d0+i)+RatPlus d0 i
(assert "all k RatTimes IntN 1 k= ~k")
 (assume "k")
 (ng #t)
 (simp "IntTimesIntNL")
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
(simp "Assertion")
;; ?^61:as n*d1* ~(bs n)+ ~d1* ~(bs n)+ ~(cs n*d0+ ~d0)+RatPlus i i==
;;      as n*(d1* ~(bs n))+(bs n*d1+cs n* ~d0+i)+RatPlus d0 i
(simp "<-" (pf "d1*bs n=bs n*d1"))
(use "RatEqvTrans" (pt "as n* ~d1*bs n+bs n*d1+(cs n* ~d0+i+RatPlus d0 i)"))
(use "RatEqvTrans" (pt "as n* ~d1*bs n+bs n*d1+(cs n* ~d0+d0+RatPlus i i)"))
(ng #t)
(simp "RatTimesComm")
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
;; ?^65:as n* ~d1*bs n+bs n*d1+(cs n* ~d0+i+RatPlus d0 i)==
;;      as n*(d1* ~(bs n))+(d1*bs n+cs n* ~d0+i)+RatPlus d0 i
(ng #t)
(simp "RatTimesComm")
(use "Truth")
(use "RatTimesComm")
(use "Truth")
;; ?^35:~(1#2)*((cs n+IntN 1)*d0)=(1#2)* ~((cs n+IntN 1)*d0)
(use "Truth")
;; ?^30:(1#2)*
;;      (~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+(1#4)*RatPlus d0 i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+(d0+i#4))
(use "Truth")
;; ?_9:(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*(z1+IntN 1)* ~d0+i)===
;;     (1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1* ~d0+i)+(d0+i#4))) -> 
;;     exr d,j,x0,z0(
;;      Sd d andd 
;;      Sdtwo j andd 
;;      CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))
(assume "Eq2")
;;   Eq1:(1#4)*(x*y+z+i)===
;;       (1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*(z1+IntN 1)* ~d0+i)
;;   Eq2:(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*(z1+IntN 1)* ~d0+i)===
;;       (1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1* ~d0+i)+(d0+i#4)))
;; -----------------------------------------------------------------------------
;; ?_82:exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

;; Now we aim for using JKLrz
(cut "exr j,d,z(Sdtwo j andi Sd d andi CoG z andi
                (1#4)*(y*d1+z1* ~d0+i)+(d0+i#4)===(1#4)*(z+j)+d)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume "jdProp" "z0" "jdz0Prop")

(intro 0 (pt "d"))
(intro 0 (pt "j"))
(intro 0 (pt "x1* ~d1"))
(intro 0 (pt "z0"))

(split)
(use "jdz0Prop")
(split)
(use "jdz0Prop")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "jdz0Prop")

;; ?^110:(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1* ~d1*y+z0+j)+d)
(use "RealEqTrans" 
     (pt "(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*(z1+IntN 1)* ~d0+i)"))
(use "Eq1")
(use "RealEqTrans" 
     (pt "(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1* ~d0+i)+(d0+i#4)))"))
(use "Eq2")
(drop "Eq1" "Eq2")
(assert "CoG z0")
(use "jdz0Prop")
(assume "CoGz0")

(assert "Real((1#2)*((1#4)*(x1* ~d1*y+z0+j)+d))")
(realproof)
(assume "R")
(simpreal "jdz0Prop")
;; ?^122:(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(z0+j)+d))===
;;       (1#2)*((1#4)*(x1* ~d1*y+z0+j)+d)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z0"))
(assume "cs" "L" "z0Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^134:~((1#4)*as n*d1*bs n)+(1#4)*(cs n+j)==(1#4)*(~(as n*d1*bs n)+cs n+j)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimes3RewRule")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(use "Truth")

;; Now we prove the formula cut in above
(use "JKLrz")
(use "Sdtwoi")
(use "Psdd0")
(use "CoGAvcToCoG")

(intro 0 (pt "i"))
(intro 0 (pt "y*d1"))
(intro 0 (pt "z1* ~d0"))
(split)
(use "Sdtwoi")
(split)
(use "CoGPsdTimes")
(use "CoGy")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "PsdUMinus")
(use "Psdd0")
(use "RealEqRefl")
(realproof)
;; Proof finished.
;; (cdp)
(save "CoGMultcSatCoIClLrxLrz")

;; cCoGMultcSatCoIClLrxLrz:
;; ag=>sdtwo=>boole=>ag=>boole=>ag=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(add-var-name "tsg" (py "sdtwo yprod sd yprod ag"))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [ag,t,boole,ag0,boole0,ag1]
;;  [let tsg
;;    (cJKLrz t boole0
;;    (cCoGAvcToCoG
;;     (t pair cCoGPsdTimes ag boole pair cCoGPsdTimes ag1(cPsdUMinus boole0))))
;;    (clft crht tsg pair 
;;    clft tsg pair cCoGPsdTimes ag0(cPsdUMinus boole)pair crht crht tsg)]

;; CoGMultcSatCoIClLrxUz
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> allnc d1,x1(
 Psd d1 -> CoG x1 -> x===(1#2)*(x1+IntN 1)* ~d1 -> allnc z1(
 CoH z1 -> z===(1#2)*z1 ->
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi"
	"d1" "x1" "Psdd1" "CoGx1" "d1x1Prop"
	"z1" "CoHz1" "z1Prop")
;; Substitute x===(1#2)*(x1+IntN 1)* ~d1 and z===(1#2)*(z1+IntN 1)* ~d0
(assert "(1#4)*(x*y+z+i)===(1#4)*(((1#2)*(x1+IntN 1)* ~d1)*y+((1#2)*z1)+i)")
(simpreal "d1x1Prop")
(simpreal "z1Prop")
(use "RealEqRefl")
(realproof)
(assume "Eq1")
;; Prepare for application of CoGAvcToCoG and JKLrz
(assert "(1#4)*(((1#2)*(x1+IntN 1)* ~d1)*y+((1#2)*z1)+i)===
(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1+i)+(i#4)))")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^22:(1#4)*(~((1#2)*(as n+IntN 1)*d1*bs n)+(1#2)*cs n+i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(i#4))
;; Replace first i by (1#2)*RatPlus i i, and prepare for taking (1#2) out

(use "RatEqvTrans" 
 (pt "(1#4)*(~(1#2)*((as n+IntN 1)*d1*bs n)+(1#2)*cs n+(1#2)*RatPlus i i)"))
(ng #t)
(simp (pf "2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; Similarly replace (i#4) by (1#4)*i.
(use "RatEqvTrans" 
  (pt "(1#2)*(~(1#4)*(as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(1#4)*i)"))
;; ?^29:(1#4)*(~(1#2)*((as n+IntN 1)*d1*bs n)+(1#2)*cs n+(1#2)*RatPlus i i)==
;;      (1#2)*(~(1#4)*(as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(1#4)*i)
;; Cancel rational factors
(simp (pf "~(1#2)*((as n+IntN 1)*d1*bs n)=(1#2)* ~((as n+IntN 1)*d1*bs n)"))
(simp (pf "~(1#4)*(as n*d1*bs n)=(1#4)* ~(as n*d1*bs n)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
;; ?^44:~((as n+IntN 1)*d1*bs n)+cs n+RatPlus i i== 
;;      ~(as n*d1*bs n)+(bs n*d1+cs n+i)+i
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
;; ?^46:~(as n*d1*bs n+RatTimes IntN 1 d1*bs n)+cs n+RatPlus i i== 
;;      ~(as n*d1*bs n)+(bs n*d1+cs n+i)+i
(assert "all k (IntN 1#1)*k= ~k")
 (assume "k")
 (ng #t)
 (simp "IntTimesIntNL")
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
;; ?^53:~(as n*d1*bs n+ ~d1*bs n)+cs n+RatPlus i i== 
;;      ~(as n*d1*bs n)+(bs n*d1+cs n+i)+i
(simp "RatUMinus2RewRule")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
(use "Truth")
;; ?^34:~(1#2)*((as n+IntN 1)*d1*bs n)=(1#2)* ~((as n+IntN 1)*d1*bs n)
(use "Truth")
;; ?^32:(1#2)*(~(1#4)*(as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(1#4)*i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(i#4))
(use "Truth")
;; ?^30:(1#2)*(~(1#4)*(as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(1#4)*i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(i#4))
(use "Truth")
(assume "Eq2")

;;   Eq1:(1#4)*(x*y+z+i)===(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*z1+i)
;;   Eq2:(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*z1+i)===
;;       (1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1+i)+(i#4)))
;; -----------------------------------------------------------------------------
;; ?_64:exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))
;; Now we aim for using JKUz
(cut "exr j,d,z(Sdtwo j andd Sd d andd CoG z andl
                (1#4)*(y*d1+z1+i)+(i#4)===(1#4)*(z+j)+d)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume "jdProp" "z0" "jdz0Prop")

(intro 0 (pt "d"))
(intro 0 (pt "j"))
(intro 0 (pt "x1* ~d1"))
(intro 0 (pt "z0"))

(split)
(use "jdz0Prop")
(split)
(use "jdz0Prop")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "jdz0Prop")

;; ?^92:(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1* ~d1*y+z0+j)+d)
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*z1+i)"))
(use "Eq1")
(use "RealEqTrans" (pt "(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1+i)+(i#4)))"))
(use "Eq2")
(drop "Eq1" "Eq2")
(assert "CoG z0")
(use "jdz0Prop")
(assume "CoGz0")
(simpreal "jdz0Prop")

;; ?^101:(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(z0+j)+d))===
;;       (1#2)*((1#4)*(x1* ~d1*y+z0+j)+d)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z0"))
(assume "cs" "L" "z0Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^113:~((1#4)*as n*d1*bs n)+(1#4)*(cs n+j)==(1#4)*(~(as n*d1*bs n)+cs n+j)
(simp (pf "(1#4)*as n*d1*bs n=(1#4)*(as n*d1*bs n)"))
(simp (pf "~((1#4)*(as n*d1*bs n))=(1#4)* ~(as n*d1*bs n)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Now we prove the formula cut in above
(use "JKUz")
(use "Sdtwoi")
(use "CoGAvcToCoG")
(intro 0 (pt "i"))
(intro 0 (pt "y*d1"))
(intro 0 (pt "z1"))
(split)
(use "Sdtwoi")
(split)
(use "CoGPsdTimes")
(use "CoGy")
(use "Psdd1")
(split)
(use "CoHToCoG")
(use "CoHz1")
(use "RealEqRefl")
(realproof)
;; Proof finished.
;; (cdp)
(save "CoGMultcSatCoIClLrxUz")

;; cCoGMultcSatCoIClLrxUz:
;; ag=>sdtwo=>boole=>ag=>ah=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [ag,t,boole,ag0,ah]
;;  [let tsg
;;    (cJKUz t(cCoGAvcToCoG(t pair cCoGPsdTimes ag boole pair cCoHToCoG ah)))
;;    (clft crht tsg pair 
;;    clft tsg pair cCoGPsdTimes ag0(cPsdUMinus boole)pair crht crht tsg)]

;; CoGMultcSatCoIClUxLrz
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> allnc x1(
 CoH x1 -> x===(1#2)*x1 -> allnc d0,z1(
 Psd d0 -> CoG z1 -> z===(1#2)*(z1+IntN 1)* ~d0 ->
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi"
	"x1" "CoHx1" "x1Prop"
	"d0" "z1" "Psdd0" "CoGz1" "d0z1Prop")

;; Substitute x===(1#2)*x1 and z===(1#2)*(z1+IntN 1)* ~d0
(assert "(1#4)*(x*y+z+i)===
(1#4)*((1#2)*x1*y+((1#2)*(z1+IntN 1)* ~d0)+i)")
(simpreal "x1Prop")
(simpreal "d0z1Prop")
(use "RealEqRefl")
(realproof)
(assume "Eq1")
;; Prepare for application of CoGAvcToCoG and JKLrz
(assert "(1#4)*((1#2)*x1*y+(1#2)*(z1+IntN 1)* ~d0+i)===
         (1#2)*((1#4)*(x1*y)+((1#4)*(0+z1* ~d0+i)+(d0+i#4)))")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^22:(1#4)*((1#2)*as n*bs n+(1#2)*(cs n+IntN 1)* ~d0+i)==
;;      (1#2)*((1#4)*as n*bs n+(1#4)*(cs n* ~d0+i)+(d0+i#4))
;; Replace first i by (1#2)*RatPlus i i, and prepare for taking (1#2) out

(use "RatEqvTrans" 
 (pt "(1#4)*((1#2)*(as n*bs n)+(1#2)*((cs n+IntN 1)* ~d0)+(1#2)*RatPlus i i)"))
(ng #t)
(simp (pf "2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; Similarly replace (d0+i#4) by (1#4)*RatPlus d0 i.
(use "RatEqvTrans" 
  (pt "(1#2)*((1#4)*(as n*bs n)+(1#4)*(cs n* ~d0+i)+(1#4)*RatPlus d0 i)"))
;; Cancel rational factors
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
;; ?^40:as n*bs n+(cs n+IntN 1)* ~d0+RatPlus i i==
;;      as n*bs n+(cs n* ~d0+i)+RatPlus d0 i
(simprat "RatTimesPlusDistrLeft")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
(simp "IntTimesIntNL")
(ng #t)
(simp (pf "d0+i=i+d0"))
(use "Truth")
(use "IntPlusComm")
(use "RatTimesComm")
(use "Truth")
(assume "Eq2")
;;   Eq1:(1#4)*(x*y+z+i)===(1#4)*((1#2)*x1*y+(1#2)*(z1+IntN 1)* ~d0+i)
;;   Eq2:(1#4)*((1#2)*x1*y+(1#2)*(z1+IntN 1)* ~d0+i)===
;;       (1#2)*((1#4)*(x1*y)+((1#4)*(0+z1* ~d0+i)+(d0+i#4)))
;; -----------------------------------------------------------------------------
;; ?_55:exr d,j,x0,y0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y0+z0+j)+d))
;; Now we aim for using JKLrz
(cut "exr j,d,z(Sdtwo j andi Sd d andi CoG z andi
                (1#4)*(0+z1* ~d0+i)+(d0+i#4)===(1#4)*(z+j)+d)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume "jdProp" "z0" "jdz0Prop")

(intro 0 (pt "d"))
(intro 0 (pt "j"))
(intro 0 (pt "x1"))
(intro 0 (pt "z0"))

(split)
(use "jdz0Prop")
(split)
(use "jdz0Prop")
(split)
(use "CoHToCoG")
(use "CoHx1")
(split)
(use "jdz0Prop")

;; ?^81:(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z0+j)+d)
(use "RealEqTrans" (pt "(1#4)*((1#2)*x1*y+(1#2)*(z1+IntN 1)* ~d0+i)"))
(use "Eq1")
(use "RealEqTrans"
     (pt "(1#2)*((1#4)*(x1*y)+((1#4)*(0+z1* ~d0+i)+(d0+i#4)))"))
(use "Eq2")
(drop "Eq1" "Eq2")
(assert "CoG z0")
(use "jdz0Prop")
(assume "CoGz0")

(assert "Real((1#2)*((1#4)*(x1*y+z0+j)+d))")
(realproof)
(assume "R")
(simpreal "jdz0Prop")
;; ?^93:(1#2)*((1#4)*(x1*y)+((1#4)*(z0+j)+d))===(1#2)*((1#4)*(x1*y+z0+j)+d)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z0"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^105:(1#4)*as n*bs n+(1#4)*(cs n+j)==(1#4)*(as n*bs n+cs n+j)
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?^109:as n*bs n+(cs n+j)==as n*bs n+cs n+j
(use "Truth")
;; Now we prove the formula cut in above
(use "JKLrz")
(use "Sdtwoi")
(use "Psdd0")
(use "CoGAvcToCoG")
(intro 0 (pt "i"))
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(intro 0 (pt "z1* ~d0"))
(split)
(use "Sdtwoi")
(split)
(use "CoGZero")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "PsdUMinus")
(use "Psdd0")
(use "RealEqRefl")
(realproof)
;; Proof finished.
;; (cdp)
(save "CoGMultcSatCoIClUxLrz")

;; cCoGMultcSatCoIClUxLrz:
;; ag=>sdtwo=>ah=>boole=>ag=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [ag,t,ah,boole,ag0]
;;  [let tsg
;;    (cJKLrz t boole
;;    (cCoGAvcToCoG(t pair cCoGZero pair cCoGPsdTimes ag0(cPsdUMinus boole))))
;;    (clft crht tsg pair clft tsg pair cCoHToCoG ah pair crht crht tsg)]

;; CoGMultcSatCoIClUxUz
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> allnc x1(
 CoH x1 -> x===(1#2)*x1 -> allnc z1(
 CoH z1 -> z===(1#2)*z1 ->
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi"
	"x1" "CoHx1" "x1Prop"
	"z1" "CoHz1" "z1Prop")

;; Substitute x===(1#2)*x1 and z===(1#2)*z1
(assert "(1#4)*(x*y+z+i)===(1#4)*((1#2)*x1*y+(1#2)*z1+i)")
(simpreal "x1Prop")
(simpreal "z1Prop")
(use "RealEqRefl")
(realproof)
(assume "Eq1")
;; Prepare for application of CoGAvcToCoG and JKLrz
(assert "(1#4)*((1#2)*x1*y+(1#2)*z1+i)===
         (1#2)*((1#4)*(x1*y)+((1#4)*(0+z1+i)+(i#4)))")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^22:(1#4)*((1#2)*as n*bs n+(1#2)*cs n+i)==
;;      (1#2)*((1#4)*as n*bs n+(1#4)*(cs n+i)+(i#4))
;; Replace first i by (1#2)*RatPlus i i, and prepare for taking (1#2) out

(use "RatEqvTrans" 
 (pt "(1#4)*((1#2)*(as n*bs n)+(1#2)*cs n+(1#2)*RatPlus i i)"))
(ng #t)
(simp (pf "2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; Similarly replace (i#4) by (1#4)*i.
(use "RatEqvTrans" (pt "(1#2)*((1#4)*(as n*bs n)+(1#4)*(cs n+i)+(1#4)*i)"))
;; Cancel rational factors
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
;; ?^40:as n*bs n+cs n+RatPlus i i==as n*bs n+(cs n+i)+i
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "Truth")
(use "Truth")
(use "Truth")
(assume "Eq2")
;;   Eq1:(1#4)*(x*y+z+i)===(1#4)*((1#2)*x1*y+(1#2)*z1+i)
;;   Eq2:(1#4)*((1#2)*x1*y+(1#2)*z1+i)===
;;       (1#2)*((1#4)*(x1*y)+((1#4)*(0+z1+i)+(i#4)))
;; -----------------------------------------------------------------------------
;; ?_44:exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))
;; Now we aim for using JKUz
(cut "exr j,d,z(Sdtwo j andi Sd d andi CoG z andi
                (1#4)*(0+z1+i)+(i#4)===(1#4)*(z+j)+d)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume "jdProp" "z0" "jdz0Prop")

(intro 0 (pt "d"))
(intro 0 (pt "j"))
(intro 0 (pt "x1"))
(intro 0 (pt "z0"))

(split)
(use "jdz0Prop")
(split)
(use "jdz0Prop")
(split)
(use "CoHToCoG")
(use "CoHx1")
(split)
(use "jdz0Prop")

;; ?^70:(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z0+j)+d)
(use "RealEqTrans" (pt "(1#4)*((1#2)*x1*y+(1#2)*z1+i)"))
(use "Eq1")
(use "RealEqTrans" (pt "(1#2)*((1#4)*(x1*y)+((1#4)*(0+z1+i)+(i#4)))"))
(use "Eq2")
(drop "Eq1" "Eq2")
(assert "CoG z0")
(use "jdz0Prop")
(assume "CoGz0")

(simpreal "jdz0Prop")
;; ?^79:(1#2)*((1#4)*(x1*y)+((1#4)*(z0+j)+d))===(1#2)*((1#4)*(x1*y+z0+j)+d)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z0"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^91:(1#4)*as n*bs n+(1#4)*(cs n+j)==(1#4)*(as n*bs n+cs n+j)
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(use "Truth")
;; Now we prove the formula cut in above
(use "JKUz")
(use "Sdtwoi")
(use "CoGAvcToCoG")
(intro 0 (pt "i"))
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(intro 0 (pt "z1"))
(split)
(use "Sdtwoi")
(split)
(use "CoGZero")
(split)
(use "CoHToCoG")
(use "CoHz1")
(use "RealEqRefl")
(realproof)
;; Proof finished.
;; (cdp)
(save "CoGMultcSatCoIClUxUz")

;; cCoGMultcSatCoIClUxUz:
;; ag=>sdtwo=>ah=>ah=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [ag,t,ah,ah0]
;;  [let tsg
;;    (cJKUz t(cCoGAvcToCoG(t pair cCoGZero pair cCoHToCoG ah0)))
;;    (clft crht tsg pair clft tsg pair cCoHToCoG ah pair crht crht tsg)]

;; CoGMultcSatCoICl
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> CoG x -> CoG z -> 
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi" "CoGx" "CoGz")

(inst-with-to "CoGClosure" (pt "x") "CoGx" "xCases")
(elim "xCases")
;; 5,6
(drop "xCases")

;; Case LRx
(assume "ExHypx")
(by-assume "ExHypx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(assert "CoG x1")
(use "d1x1Prop")
(assume "CoGx1")

;; We distinguish cases on CoG z
(inst-with-to "CoGClosure" (pt "z") "CoGz" "zCases")
(elim "zCases")
;; 20,21
(drop "zCases")

;; Subcase LRx, LRz
(assume "ExHypz")
(by-assume "ExHypz" "d0" "d0Prop")
(by-assume "d0Prop" "z1" "d0z1Prop")

(use "CoGMultcSatCoIClLrxLrz" (pt "d1") (pt "x1") (pt "d0") (pt "z1"))
(use "CoGy")
(use "Sdtwoi")
(use "d1x1Prop")
(use "d1x1Prop")
(use "d1x1Prop")
(use "d0z1Prop")
(use "d0z1Prop")
(use "d0z1Prop")

;; ?_21:exr x0(CoH x0 andl z===(1#2)*x0) -> 
;;      exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

(drop "zCases")

;; Subcase LRx, Uz
(assume "ExHypz")
(by-assume "ExHypz" "z1" "z1Prop")

(use "CoGMultcSatCoIClLrxUz" (pt "d1") (pt "x1") (pt "z1"))
(use "CoGy")
(use "Sdtwoi")
(use "d1x1Prop")
(use "d1x1Prop")
(use "d1x1Prop")
(use "z1Prop")
(use "z1Prop")

;; ?_6:exr x0(CoH x0 andl x===(1#2)*x0) -> 
;;     exr d,j,x0,z0(
;;      Sd d andd 
;;      Sdtwo j andd 
;;      CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

(drop "xCases")

;; Case Ux
(assume "ExHypx")
(by-assume "ExHypx" "x1" "x1Prop")

;; We distinguish cases on CoG z
(inst-with-to "CoGClosure" (pt "z") "CoGz" "zCases")
(elim "zCases")
;; 57,58
(drop "zCases")

;; Subcase Ux, LRz
(assume "ExHypz")
(by-assume "ExHypz" "d0" "d0Prop")
(by-assume "d0Prop" "z1" "d0z1Prop")

(use "CoGMultcSatCoIClUxLrz" (pt "x1") (pt "d0") (pt "z1"))
(use "CoGy")
(use "Sdtwoi")
(use "x1Prop")
(use "x1Prop")
(use "d0z1Prop")
(use "d0z1Prop")
(use "d0z1Prop")

;; ?_58:exr x0(CoH x0 andl z===(1#2)*x0) -> 
;;      exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

(drop "zCases")

;; Subcase Ux, Uz
(assume "ExHypz")
(by-assume "ExHypz" "z1" "z1Prop")

(use "CoGMultcSatCoIClUxUz" (pt "x1") (pt "z1"))
(use "CoGy")
(use "Sdtwoi")
(use "x1Prop")
(use "x1Prop")
(use "z1Prop")
(use "z1Prop")
;; Proof finished.
;; (cdp)
(save "CoGMultcSatCoICl")

;; cCoGMultcSatCoICl:
;; ag=>sdtwo=>ag=>ag=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag,t,ag0,ag1]
;;  [case (cCoGClosure ag0)
;;    (InL bg -> 
;;    [case (cCoGClosure ag1)
;;      (InL bg0 -> 
;;      cCoGMultcSatCoIClLrxLrz ag t clft bg crht bg clft bg0 crht bg0)
;;      (InR ah -> cCoGMultcSatCoIClLrxUz ag t clft bg crht bg ah)])
;;    (InR ah -> 
;;    [case (cCoGClosure ag1)
;;      (InL bg -> cCoGMultcSatCoIClUxLrz ag t ah clft bg crht bg)
;;      (InR ah0 -> cCoGMultcSatCoIClUxUz ag t ah ah0)])]

(animate "CoGClosure")
(animate "CoGMultcSatCoIClLrxLrz")
(animate "CoGMultcSatCoIClLrxUz")
(animate "CoGMultcSatCoIClUxLrz")
(animate "CoGMultcSatCoIClUxUz")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag,t,ag0,ag1][case (DesYprod ag0)
;;    (InL bg -> [case (DesYprod ag1)
;;      (InL bg0 -> 
;;      [let tsg (cJKLrz t clft bg0
;;        (cCoGAvcToCoG (t pair cCoGPsdTimes ag clft bg pair 
;;                       cCoGPsdTimes crht bg0(cPsdUMinus clft bg0))))
;;        (clft crht tsg pair 
;;        clft tsg pair 
;;        cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair crht crht tsg)])
;;      (InR ah -> [let tsg
;;        (cJKUz t (cCoGAvcToCoG(t pair cCoGPsdTimes ag clft bg pair
;;                               cCoHToCoG ah)))
;;        (clft crht tsg pair 
;;         clft tsg pair 
;;         cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair
;;         crht crht tsg)])])
;;    (InR ah -> [case (DesYprod ag1)
;;      (InL bg -> [let tsg (cJKLrz t clft bg
;;        (cCoGAvcToCoG (t pair cCoGZero pair
;;                       cCoGPsdTimes crht bg(cPsdUMinus clft bg))))
;;        (clft crht tsg pair clft tsg pair
;;         cCoHToCoG ah pair crht crht tsg)])
;;      (InR ah0 -> [let tsg
;;        (cJKUz t(cCoGAvcToCoG(t pair cCoGZero pair cCoHToCoG ah0)))
;;        (clft crht tsg pair clft tsg pair
;;         cCoHToCoG ah pair crht crht tsg)])])]

(deanimate "CoGClosure")
(deanimate "CoGMultcSatCoIClLrxLrz")
(deanimate "CoGMultcSatCoIClLrxUz")
(deanimate "CoGMultcSatCoIClUxLrz")
(deanimate "CoGMultcSatCoIClUxUz")

;; Putting things together.  First a lemma for estimates.

;; CoGMultcToCoGAux
(set-goal "all x,y,z,i(Real x -> Real y -> Real z -> Sdtwo i ->
 abs x<<=1 -> abs y<<=1 -> abs z<<=1 -> abs((1#4)*(x*y+z+i))<<=1)")
(assume "x" "y" "z" "i" "Rx" "Ry" "Rz" "Sdtwoi" "xBd" "yBd" "zBd")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes(1#4)4"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
;; ?^11:abs(x*y+z+i)<<=4
(use "RealLeTrans" (pt "(RealTimes 1 1)+1+2"))
(use "RealLeTrans" (pt "abs(x*y)+(abs z)+RealAbs i"))
(use "RealLeTrans" (pt "abs(x*y+z)+RealAbs i"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlus")
(autoreal)
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
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
(use "RatLeToRealLe")
(use "RatLeTrans" (pt "2#1"))
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoGMultcToCoGAux")

;; (set! COMMENT-FLAG #f)
;; CoGMultcToCoG
(set-goal "allnc z0(
 exr i,x,y,z(Sdtwo i andi CoG x andi CoG y andi CoG z andi
             z0===(1#4)*(x*y+z+i)) -> CoG z0)")
(assume "z0" "Qz0")
(coind "Qz0" (pf "exr i,x,y,z
          (Sdtwo i andi CoG x andi CoG y andi CoG z andi
           z0===(1#4)*(x*y+z+i)) -> CoH z0"))
;; 3,4
(assume "z2" "Qz2")
(by-assume "Qz2" "i" "iProp")
(by-assume "iProp" "x" "ixProp")
(by-assume "ixProp" "y" "ixyProp")
(by-assume "ixyProp" "z" "ixyzProp")
(assert "CoG y")
(use "ixyzProp")
(assume "CoGy")
;; let introduction
(cut "exr d,j,x0,z0(
 Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "d1" "d1Prop")
(by-assume "d1Prop" "i1" "d1i1Prop")
(by-assume "d1i1Prop" "x1" "d1i1x1Prop")
(by-assume "d1i1x1Prop" "z1" "d1i1x1z1Prop")
(assert "Sd d1")
(use "d1i1x1z1Prop")
(assume "Sdd1")
(assert "Sdtwo i1")
(use "d1i1x1z1Prop")
(assume "Sdtwoi1")
(assert "CoG x1")
(use "d1i1x1z1Prop")
(assume "CoGx1")
(assert "CoG z1")
(use "d1i1x1z1Prop")
(assume "CoGz1")
(assert "(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z1+i1)+d1)")
(use "d1i1x1z1Prop")
(assume "Eq")
(drop "d1i1x1z1Prop")
(assert "d1=0 orr Psd d1")
 (use-with "SdDisj" (pt "d1") "?")
 (use "Sdd1")
(assume "Disj")
(elim "Disj")
;; 57,58
(drop "Disj")
(assume "d1=0") ;case small
(intro 1)
(intro 0 (pt "(1#4)*(x1*y+z1+i1)"))
(intro 0 (pt "z2"))
(split)
(realproof)
(split)
;; ?^66:abs((1#4)*(x1*y+z1+i1))<<=1
(use "CoGMultcToCoGAux")
(autoreal)
(use "Sdtwoi1")
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy")
(use "CoGToBd")
(use "CoGz1")
(split)
(intro 1)
(intro 0 (pt "i1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y"))
(intro 0 (pt "z1"))
(split)
(use "Sdtwoi1")
(split)
(use "CoGx1")
(split)
(use "CoGy")
(split)
(use "CoGz1")
(use "RealEqRefl")
(autoreal)
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;;   d1=0:d1=0
;; -----------------------------------------------------------------------------
;; ?^97:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===(1#2)*((1#4)*(x1*y+z1+i1))
(simp "d1=0")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
(simpreal "ixyzProp")
(use "RealEqRefl")
(autoreal)
;; 58
(drop "Disj")
(assume "Psdd1")
(intro 0)
(intro 0 (pt "d1"))
(intro 0 (pt "(1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)"))
(intro 0 (pt "z2"))
(split)
(use "Psdd1")
(split)
(autoreal)
(split)
;; ?^114:abs((1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1))<<=1
(use "CoGMultcToCoGAux")
(autoreal)
(simp (pf "~(i1*d1)= ~i1*d1"))
(use "IntTimesSdtwoPsdToSdtwo")
;; ?^125:Sdtwo(~i1)
(use "SdtwoIntUMinus")
(use "Sdtwoi1")
(use "Psdd1")
(use "Truth")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
;; ?^142:RatLe abs d1 1
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "CoGToBd")
(use "CoGz1")
;; ?^154:abs~d1<<=1
(use "RatLeToRealLe")
;; ?^158:RatLe abs d1 1
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; 115
(split)
(intro 1)
(intro 0 (pt "i1* ~d1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y* ~d1"))
(intro 0 (pt "z1* ~d1"))
(split)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "CoGx1")
(split)
(use "CoGPsdTimes")
(use "CoGy")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "PsdUMinus")
(use "Psdd1")
;; ?^183:(1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)===
;;       (1#4)*(x1*(y* ~d1)+z1* ~d1+i1* ~d1)
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "Truth")
;;?^164:z2===(1#2)*((1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)+IntN 1)* ~d1 andnc
;;       z2===z2
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;; ?^202:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===
;;       (1#2)*((1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)+IntN 1)* ~d1
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^214:(1#2)*((1#4)*(as n*bs n+cs n+i1)+d1)== 
;;       ~((1#2)*((1#4)*(~(as n*bs n*d1)+ ~(cs n*d1)+ ~(i1*d1))+IntN 1)*d1)
(simp "<-" "RatTimes3RewRule")
(simp "<-" "RatTimesAssoc")
(use "RatTimesCompat")
(use "Truth")
;; ?^218:(1#4)*(as n*bs n+cs n+i1)+d1==
;;       ((1#4)*(~(as n*bs n*d1)+ ~(cs n*d1)+ ~(i1*d1))+IntN 1)* ~d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(use "RatPlusCompat")
;; ?^222:(1#4)*(as n*bs n+cs n+i1)==
;;       (1#4)*(~(as n*(bs n*d1))+ ~(cs n*d1)+ ~(i1*d1))* ~d1
(simp "<-" "RatTimesAssoc")
(use "RatTimesCompat")
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(ng #t)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(ng #t)
(simp "<-" "RatTimesAssoc")
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
;; ?^200:z2===z2
(use "RealEqRefl")
(use "RealEqToReal0" (pt "(1#4)*(x*y+z+i)"))
(use "ixyzProp")

;; ?_22:exr j,d,x0,y0,z0(
;;       Sdtwo j andd 
;;       Sd d andd 
;;       CoG x0 andd 
;;       CoG y0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y0+z0+j)+d))

;; Now we prove the formula cut in above, using CoGMultcSatCoICl
(use "CoGMultcSatCoICl")
(use "CoGy")
(use "ixyzProp")
(use "ixyzProp")
(use "ixyzProp")
;; 4
(assume "z2" "Qz2")
(by-assume "Qz2" "i" "iProp")
(by-assume "iProp" "x" "ixProp")
(by-assume "ixProp" "y" "ixyProp")
(by-assume "ixyProp" "z" "ixyzProp")
(assert "CoG y")
(use "ixyzProp")
(assume "CoGy")
;; let introduction
(cut "exr d,j,x0,z0(
 Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "d1" "d1Prop")
(by-assume "d1Prop" "i1" "d1i1Prop")
(by-assume "d1i1Prop" "x1" "d1i1x1Prop")
(by-assume "d1i1x1Prop" "z1" "d1i1x1z1Prop")
(assert "Sd d1")
 (use "d1i1x1z1Prop")
(assume "Sdd1")
(assert "Sdtwo i1")
 (use "d1i1x1z1Prop")
(assume "Sdtwoi1")
(assert "CoG x1")
 (use "d1i1x1z1Prop")
(assume "CoGx1")
(assert "CoG z1")
 (use "d1i1x1z1Prop")
(assume "CoGz1")
(assert "(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z1+i1)+d1)")
 (use "d1i1x1z1Prop")
(assume "Eq")
(drop "d1i1x1z1Prop")
(assert "d1=0 orr Psd d1")
 (use-with "SdDisj" (pt "d1") "?")
 (use "Sdd1")
(assume "Disj")
(elim "Disj")
;; 302,303
(drop "Disj")
(assume "d1=0") ;case small
(intro 1)
(intro 0 (pt "(1#4)*(x1*y+z1+i1)"))
(intro 0 (pt "z2"))
(split)
(autoreal)
(split)
;; ?^311:abs((1#4)*(x1*y+z1+i1))<<=1
(use "CoGMultcToCoGAux")
(autoreal)
(use "Sdtwoi1")
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy")
(use "CoGToBd")
(use "CoGz1")
(split)
(intro 1)
(intro 0 (pt "i1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y"))
(intro 0 (pt "z1"))
(split)
(use "Sdtwoi1")
(split)
(use "CoGx1")
(split)
(use "CoGy")
(split)
(use "CoGz1")
(use "RealEqRefl")
(autoreal)
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;;   d1=0:d1=0
;; -----------------------------------------------------------------------------
;; ?^342:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===(1#2)*((1#4)*(x1*y+z1+i1))
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(simp "d1=0")
(use "Truth")
;; ?^340:z2===z2
(use "RealEqRefl")
(use "RealEqToReal0" (pt "(1#4)*(x*y+z+i)"))
(use "ixyzProp")
;; 303
(drop "Disj")
(assume "Psdd1")
(intro 0)
(intro 0 (pt "d1"))
(intro 0 (pt "(1#4)*(x1*y* d1+z1* d1+RealTimes i1 d1)"))
(intro 0 (pt "z2"))
(split)
(use "Psdd1")
(split)
(autoreal)
(split)
;; ?^368:abs((1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1))<<=1
(use "CoGMultcToCoGAux")
(autoreal)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "Psdd1")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
;; ?_393:RatLe abs d1 1
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "CoGToBd")
(use "CoGz1")
;; ?^405:abs d1<<=1
(use "RatLeToRealLe")
;; ?^409:RatLe abs d1 1
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; 369
(split)
(intro 1)
(intro 0 (pt "i1*d1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y*d1"))
(intro 0 (pt "z1*d1"))
(split)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "Psdd1")
(split)
(use "CoGx1")
(split)
(use "CoGPsdTimes")
(use "CoGy")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "Psdd1")
;; ?^432:(1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1)===(1#4)*(x1*(y*d1)+z1*d1+i1*d1)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "Truth")
;; ?^415:z2===(1#2)*((1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1)+1)*d1 andnc z2===z2
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;; ?^450:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===
;;       (1#2)*((1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1)+1)*d1
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?^462:(1#2)*((1#4)*(as n*bs n+cs n+i1)+d1)==
;;       (1#2)*((1#4)*(as n*bs n*d1+cs n*d1+i1*d1)+1)*d1
(simp "<-" "RatTimesAssoc")
(use "RatTimesCompat")
(use "Truth")
;; ?^465:(1#4)*(as n*bs n+cs n+i1)+d1==((1#4)*(as n*bs n*d1+cs n*d1+i1*d1)+1)*d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(use "RatPlusCompat")
;; ?^468:(1#4)*(as n*bs n+cs n+i1)==(1#4)*(as n*(bs n*d1)+cs n*d1+i1*d1)*d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(ng #t)
(simp "<-" "RatTimesAssoc")
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
;; ?^448:z2===z2
(use "RealEqRefl")
(use "RealEqToReal0" (pt "(1#4)*(x*y+z+i)"))
(use "ixyzProp")

;; ?_267:exr d,j,x0,z0(
;;        Sd d andd 
;;        Sdtwo j andd 
;;        CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

;; Now we prove the formula cut in above, using CoGMultcSatCoICl
(use "CoGMultcSatCoICl")
(use "CoGy")
(use "ixyzProp")
(use "ixyzProp")
(use "ixyzProp")
;; Proof finished.
;; (cdp)
(save "CoGMultcToCoG")

;; cCoGMultcToCoG: sdtwo yprod ag yprod ag yprod ag=>ag

(define eterm (proof-to-extracted-term))
(add-var-name "tggg" (py "sdtwo yprod ag yprod ag yprod ag"))
(add-var-name "stgg" (py "sd yprod sdtwo yprod ag yprod ag"))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [tggg](CoRec sdtwo yprod ag yprod ag yprod ag=>ag
;;              sdtwo yprod ag yprod ag yprod ag=>ah)tggg
;;  ([tggg0][let stgg (cCoGMultcSatCoICl
;;                      clft crht crht tggg0 clft tggg0
;;                      clft crht tggg0 crht crht crht tggg0)
;;      [case (cSdDisj clft stgg)
;;       (DummyL -> InR(InR(clft crht stgg pair 
;;                          clft crht crht stgg pair
;;                          clft crht crht tggg0 pair
;;                          crht crht crht stgg)))
;;       (Inr boole -> InL(boole pair 
;;        InR(cIntTimesSdtwoPsdToSdtwo
;;             clft crht stgg(cPsdUMinus boole)pair 
;;             clft crht crht stgg pair 
;;             cCoGPsdTimes clft crht crht tggg0
;;                          (cPsdUMinus boole)pair 
;;             cCoGPsdTimes crht crht crht stgg
;;                          (cPsdUMinus boole))))]])
;;  ([tggg0][let stgg (cCoGMultcSatCoICl
;;                      clft crht crht tggg0 clft tggg0
;;                      clft crht tggg0 crht crht crht tggg0)
;;      [case (cSdDisj clft stgg)
;;       (DummyL -> InR(InR(clft crht stgg pair 
;;                          clft crht crht stgg pair 
;;                          clft crht crht tggg0 pair
;;                          crht crht crht stgg)))
;;       (Inr boole -> InL(boole pair 
;;        InR(cIntTimesSdtwoPsdToSdtwo
;;             clft crht stgg boole pair 
;;             clft crht crht stgg pair 
;;             cCoGPsdTimes clft crht crht tggg0 boole pair 
;;             cCoGPsdTimes crht crht crht stgg boole)))]])

;; CoGMult
(set-goal "allnc x,y(CoG x -> CoG y -> CoG(x*y))")
(assume "x" "y" "CoGx" "CoGy")
(use "CoGMultcToCoG")
(use "CoGMultToMultc")
(use "CoGx")
(use "CoGy")
;; Proof finished.
(save "CoGMult")

(define CoGMult-eterm (proof-to-extracted-term))
(define CoGMult-neterm (rename-variables (nt CoGMult-eterm)))
;; (ppc CoGMult-neterm)

;; [ag,ag0]cCoGMultcToCoG(cCoGMultToMultc ag ag0)

