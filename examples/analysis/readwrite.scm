;; 2022-03-12.  examples/analysis/readwrite.scm.  Adaption of Kenji
;; Miyamoto's readwrite.scm to the current state of Minlog:
;; numbers.scm replaced by nat.scm list.scm pos.scm int.scm rat.scm
;; rea.scm.  Also digits.scm loaded.  Primitive pairs replaced by
;; defined pairs.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")

(load "~/git/minlog/examples/analysis/digits.scm")

;; (set! COMMENT-FLAG #t)

;; Contents
;; 1. A type-1 uniformly continuous function to a type-0 ucf
;; 2. A type-0 ucf to a type-1 ucf
;; 3. Applying a type-0 ucf to a type-0 real number
;; 4. Composing ucfs
;; 5. Definite integration of a type-0 ucf
;; 6. Experiments

;; 1. A type-1 uniformly continuous function to a type-0 ucf
;; =========================================================

(add-tvar-name "xi") ;type of uniformly continuous functions
(add-var-name "f" (py "xi"))
(add-pvar-name "X" (make-arity (py "xi")))

(add-program-constant "Outf" (py "sd=>xi=>xi")) ;Outf s f means (Out_s \circ f)
(add-program-constant "fIn" (py "sd=>xi=>xi")) ;fIn s f means (f \circ In_s)

;; Sub f a m b n means f[I_{a,m}] \subseteq I_{b,n}
(add-program-constant "Sub" (py "xi=>rat=>nat=>rat=>nat=>boole"))

(add-program-constant "IdF" (py "xi"))

(add-global-assumption
 "AxOutIntro"
 "all f^,s,a,m,b,n(
 (Sub xi)f^ 0 Zero(SdToInt s#2)(Succ Zero) ->
 (Sub xi)f^ a m b(Succ n) -> (Sub xi)((Outf xi)s f^)a m(2*b+ ~(SdToInt s))n)")

(add-global-assumption
 "AxOutElim"
 "all f^,s,a,m,b,n(
 (Sub xi)f^ 0 Zero(SdToInt s#2)(Succ Zero) -> 
 (Sub xi)((Outf xi)s f^)a m b n -> 
 (Sub xi)f^ a m((1#2)*(b+SdToInt s))(Succ n))")

(add-global-assumption
 "AxInIntro"
 "all f^,s,a,m,b,n(
 (Sub xi)f^((1#2)*(a+SdToInt s))(Succ m)b n -> (Sub xi)((fIn xi)s f^)a m b n)")

(add-global-assumption
 "AxInElim"
 "all f^,s,a,m,b,n(
 (Sub xi)((fIn xi)s f^)(2*a+ ~(SdToInt s))m b n -> (Sub xi)f^ a(Succ m)b n)")

(add-global-assumption
 "AxUcfWeak"
 "all f^,a,m1,m2,b,n(m1<=m2 -> (Sub xi)f^ a m1 b n -> (Sub xi)f^ a m2 b n)")

(add-global-assumption
 "AxUcfBound"
 "all f^,a,m(Sub xi)f^ a m 0 Zero")

(add-global-assumption
 "AxUcfIdF"
 "all a,m(Sub xi)(IdF xi)a m a m")

(add-global-assumption
 "AxUcfLft"
 "all f^,b((Sub xi)f^ 0 Zero b(Succ(Succ Zero)) -> b<(IntN 1#4) ->
 (Sub xi)f^ 0 Zero(IntN 1#2)(Succ Zero))")

(add-global-assumption
 "AxUcfMid"
 "all f^,b((Sub xi)f^ 0 Zero b(Succ(Succ Zero)) -> (IntN 1#4)<=b -> b<(1#4) ->
 (Sub xi)f^ 0 Zero(0#2)(Succ Zero))")

(add-global-assumption
 "AxUcfRht"
 "all f^,b((Sub xi)f^ 0 Zero b(Succ(Succ Zero)) -> (1#4)<=b ->
 (Sub xi)f^ 0 Zero(1#2)(Succ Zero))")

;; StandardSplit
(set-goal "all a(a<(IntN 1#4) orr (IntN 1#4)<=a andnc a<(1#4) oru 1/4<=a)")
(cases)
(cases)
(assume "p" "q")
(ng #t)
(intro 1)
(cases (pt "SZero(SZero p)<q"))
(assume "4p<q")
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4p<q -> F")
(intro 1)
(use "PosNotLtToLe")
(use "4p<q -> F")
;; 4
(assume "p")
(ng #t)
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
;; 5
(assume "p" "q")
(ng #t)
(cases (pt "SZero(SZero p)<=q"))
(assume "4p<=q")
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4p<=q -> F")
(intro 0)
(use "PosNotLeToLt")
(use "4p<=q -> F")
;; Proof finished.
;; (cp)
(save "StandardSplit")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [a]
;;  [case a
;;    (k#p -> 
;;    [case k
;;      (p0 -> Inr(SZero(SZero p0)<p))
;;      (0 -> Inr True)
;;      (IntN p0 -> 
;;      [case (SZero(SZero p0)<=p) (True -> Inr True) (False -> DummyL)])])]

;; FindSd
;; L5: f[I] sub I_{b,2} -> ex d f[I] sub I_d
(set-goal
 "allnc f^ all b((Sub xi)f^ 0 Zero b(Succ(Succ Zero)) ->
  exl s (Sub xi)f^ 0 Zero(SdToInt s#2)(Succ Zero))")
(assume "f^" "b" "f[I] sub I_{b,2}")
(inst-with-to "StandardSplit" (pt "b") "StandardSplitInst")
(elim "StandardSplitInst")
(drop "StandardSplitInst")
(assume "b<-1/4")
(intro 0 (pt "SdL"))
(use "AxUcfLft" (pt "b"))
(use "f[I] sub I_{b,2}")
(use "b<-1/4")
(assume "MidOrRht")
(elim "MidOrRht")
(drop "MidOrRht")
(assume "(IntN 1/4)<=b & b<1/4") ;Middle
(intro 0 (pt "SdM"))
(use "AxUcfMid" (pt "b"))
(use "f[I] sub I_{b,2}")
(use "(IntN 1/4)<=b & b<1/4")
(use "(IntN 1/4)<=b & b<1/4")
(assume "1/4<=b")
(intro 0 (pt "SdR"))
(use "AxUcfRht" (pt "b"))
(use "f[I] sub I_{b,2}")
(use "1/4<=b")
;; Proof finished.
;; (cp)
(save "FindSd")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [a]
;;  [case (cStandardSplit a)
;;    (DummyL -> SdL)
;;    (Inr boole -> [case boole (True -> SdM) (False -> SdR)])]

(animate "StandardSplit")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [a]
;;  [case a
;;    (k#p -> 
;;    [case k
;;      (p0 -> [case (SZero(SZero p0)<p) (True -> SdM) (False -> SdR)])
;;      (0 -> SdM)
;;      (IntN p0 -> [case (SZero(SZero p0)<=p) (True -> SdM) (False -> SdL)])])]

(deanimate "StandardSplit")

(add-algs "algread"
	  '("sd=>alpha=>algread" "Put")
	  '("algread=>algread=>algread=>algread" "Get"))

(add-ids
 (list (list "Read" (make-arity (py "xi")) "algread"))
 '("allnc f^ all s(
   (Sub xi)f^ 0 Zero(SdToInt s#2)(Succ Zero) -> X((Outf xi)s f^) -> Read f^)"
   "InitRead")
 '("allnc f^(
    Read((fIn xi)SdL f^) -> Read((fIn xi)SdM f^) -> Read((fIn xi)SdR f^) ->
    Read f^)"
   "GenRead"))

(add-algs "algwrite"
	  '("algwrite" "Stop")
	  '("algread algwrite=>algwrite" "Cont"))

(add-ids
 (list (list "Write" (make-arity (py "xi")) "algwrite"))
 '("Write(IdF xi)" "InitWrite")
 '("allnc f^((Read(cterm (f^) Write f^))f^ -> Write f^)" "GenWrite"))

(add-co "Write")

;; We now aim at ContToCoWrite: C f -> CoWrite f.  This will
;; essentially depend on an auxiliary lemma ContToCoWriteAux proved by
;; induction: all m(B m 2 f -> C f -> Read(CoWrite or C)f)

;; ContToCoWriteAux
;; Lemma 6
;; all m(B m 2 f -> C f -> Read(CoWrite or C)f)
(set-goal "all m allnc f^(
      all a exl b (Sub xi)f^ a m b(Succ(Succ Zero)) -> 
      all n exd m all a exl b (Sub xi)f^ a m b n -> 
      (Read (cterm (f^) 
              CoWrite f^ ord all n exd m all a exl b (Sub xi)f^ a m b n))
      f^)")
(ind)
;; Base case m=0
(assume "f^" "B02f" "Cf")
(inst-with-to "B02f" (pt "IntZero#1") "B02fInst")
(by-assume "B02fInst" "b" "bProp")
(cut "exl s (Sub xi)f^ 0 Zero(SdToInt s#2)(Succ Zero)")
;; (use "Id") ;slow.  Use use-with instead:
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "s" "sProp")
;; (use "InitRead" (pt "s"))
(use-with "InitRead"
	  (make-cterm
	   (pv "f^")
	   (pf "CoWrite f^ ord all n exd m all a exl b (Sub xi)f^ a m b n"))
	   (pt "f^") (pt "s") "?" "?")
(use "sProp")
(intro 1)
(assume "n")
(inst-with-to "Cf" (pt "n+1") "CfInst")
(by-assume "CfInst" "m" "mProp")
(intro 0 (pt "m"))
(assume "a")
(inst-with-to "mProp" (pt "a") "mPropInst")
(by-assume "mPropInst" "b1" "b1Prop")
(intro 0 (pt "2*b1+ ~(SdToInt s)"))
(use "AxOutIntro")
(use "sProp")
(use "b1Prop")
(use "FindSd" (pt "b"))
(use "bProp")
;; 3 Step case
(assume "m" "IH" "f^" "B(m+1)2" "Cf")
;; (use "GenRead")
(use-with "GenRead"
	  (make-cterm
	   (pv "f^")
	   (pf "CoWrite f^ ord all n exd m all a exl b (Sub xi)f^ a m b n"))
	  (pt "f^") "?" "?" "?")
;; 38-40
(use "IH") ;here we need f^ since fIn is not total.
(drop "IH")
(assume "a")
(inst-with-to "B(m+1)2" (pt "(1#2)*(a+SdToInt SdL)") "B(m+1)2Inst")
(by-assume "B(m+1)2Inst" "b" "bProp")
(intro 0 (pt "b"))
(use "AxInIntro")
(use "bProp")
(drop "IH")
(assume "n")
(inst-with-to "Cf" (pt "n") "CfInst")
(by-assume "CfInst" "m1" "m1Prop")
(intro 0 (pt "m1"))
(assume "a")
(inst-with-to "m1Prop" (pt "(1#2)*(a+SdToInt SdL)") "m1PropInst")
(by-assume "m1PropInst" "b" "bProp")
(intro 0 (pt "b"))
(use "AxInIntro")
(use "AxUcfWeak" (pt "m1"))
(use "Truth")
(use "bProp")
;; 39
(use "IH")
(drop "IH")
(assume "a")
(inst-with-to "B(m+1)2" (pt "(1#2)*(a+SdToInt SdM)") "B(m+1)2Inst")
(by-assume "B(m+1)2Inst" "b" "bProp")
(intro 0 (pt "b"))
(use "AxInIntro")
(use "bProp")
(drop "IH")
(assume "n")
(inst-with-to "Cf" (pt "n") "CfInst")
(by-assume "CfInst" "m1" "m1Prop")
(intro 0 (pt "m1"))
(assume "a")
(inst-with-to "m1Prop" (pt "(1#2)*(a+SdToInt SdM)") "m1PropInst")
(by-assume "m1PropInst" "b" "bProp")
(intro 0 (pt "b"))
(use "AxInIntro")
(use "AxUcfWeak" (pt "m1"))
(use "Truth")
(use "bProp")
;; 40
(use "IH")
(drop "IH")
(assume "a")
(inst-with-to "B(m+1)2" (pt "(1#2)*(a+SdToInt SdR)") "B(m+1)2Inst")
(by-assume "B(m+1)2Inst" "b" "bProp")
(intro 0 (pt "b"))
(use "AxInIntro")
(use "bProp")
;; 100
(drop "IH")
(assume "n")
(inst-with-to "Cf" (pt "n") "CfInst")
(by-assume "CfInst" "m1" "m1Prop")
(intro 0 (pt "m1"))
(assume "a")
(inst-with-to "m1Prop" (pt "(1#2)*(a+SdToInt SdR)") "m1PropInst")
(by-assume "m1PropInst" "b" "bProp")
(intro 0 (pt "b"))
(use "AxInIntro")
(use "AxUcfWeak" (pt "m1"))
(use "Truth")
(use "bProp")
;; Proof finished.
;; (cp)
(save "ContToCoWriteAux")

;; ContToCoWrite
;; C f -> CoWrite f
(set-goal "allnc f^(all n exd m all a exl b (Sub xi)f^ a m b n -> CoWrite f^)")
(assume "f^" "Cf")
(coind "Cf")
(assume "f^1" "Cf1")
(intro 1)
(intro 0 (pt "f^1"))
(split)
(inst-with-to "Cf1" (pt "Succ(Succ Zero)") "Cf1Inst")
(by-assume "Cf1Inst" "m" "mProp")
(use "ContToCoWriteAux" (pt "m"))
(use "mProp")
(use "Cf1")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ContToCoWrite")

(define eterm-a (proof-to-extracted-term))

(add-var-name "oh" (py "nat=>nat yprod(rat=>rat)"))
;; o for module omega, h for approximating function

(define neterm-a (rename-variables (nt eterm-a)))

(ppc neterm-a)

;; [oh]
;;  (CoRec (nat=>nat yprod(rat=>rat))=>algwrite)oh
;;  ([oh0]
;;    Inr[case (oh0(Succ(Succ Zero)))
;;         (n pair(rat=>rat) -> cContToCoWriteAux n(rat=>rat)oh0)])

(animate "ContToCoWriteAux")

;; st for step
(add-var-name
 "st" (py "(rat=>rat)=>(nat=>nat yprod(rat=>rat))=>
           algread(algwrite ysum(nat=>nat yprod(rat=>rat)))"))

(add-var-name "af" (py "rat=>rat"))

(define neterm-a (rename-variables (nt eterm-a)))
(pp neterm-a)

;; [oh]
;;  (CoRec (nat=>nat yprod(rat=>rat))=>algwrite)oh
;;  ([oh0]
;;    Inr[if (oh0(Succ(Succ Zero)))
;;         ([n,af]
;;          (Rec nat=>(rat=>rat)=>(nat=>nat yprod(rat=>rat))=>algread(algwrite ysum(nat=>nat yprod(rat=>rat))))
;;          n
;;          ([af0,oh1]
;;            [let s
;;              (cFindSd(af0 0))
;;              ((Put algwrite ysum(nat=>nat yprod(rat=>rat)))s
;;              ((InR (nat=>nat yprod(rat=>rat)) algwrite)
;;               ([n0]
;;                 [if (oh1(Succ n0))
;;                   ([n1,af1]n1 pair([a]2*af1 a+ ~(SdToInt s)))])))])
;;          ([n0,st,af0,oh1]
;;            (Get algwrite ysum(nat=>nat yprod(rat=>rat)))
;;            (st([a]af0((1#2)*(a+IntN 1)))
;;             ([n1][if (oh1 n1) ([n2,af1]n2 pair([a]af1((1#2)*(a+IntN 1))))]))
;;            (st([a]af0((1#2)*a))
;;             ([n1][if (oh1 n1) ([n2,af1]n2 pair([a]af1((1#2)*a)))]))
;;            (st([a]af0((1#2)*(a+1)))
;;             ([n1][if (oh1 n1) ([n2,af1]n2 pair([a]af1((1#2)*(a+1))))])))
;;          af 
;;          oh0)])

;; Note that let s ... avoids a double occurrence of cFindSd(af0 0)

(animate "FindSd")
(animate "StandardSplit")

(define neterm-a (rename-variables (nt eterm-a)))
(pp neterm-a)

;; [oh]
;;  (CoRec (nat=>nat yprod(rat=>rat))=>algwrite)oh
;;  ([oh0]
;;    Inr[if (oh0(Succ(Succ Zero)))
;;         ([n,af]
;;          (Rec nat=>(rat=>rat)=>(nat=>nat yprod(rat=>rat))=>algread(algwrite ysum(nat=>nat yprod(rat=>rat))))
;;          n
;;          ([af0,oh1]
;;            [let s
;;              [if (af0 0)
;;               ([k,p]
;;                [if k
;;                  ([p0][if (SZero(SZero p0)<p) SdM SdR])
;;                  SdM
;;                  ([p0][if (SZero(SZero p0)<=p) SdM SdL])])]
;;              ((Put algwrite ysum(nat=>nat yprod(rat=>rat)))s
;;              ((InR (nat=>nat yprod(rat=>rat)) algwrite)
;;               ([n0]
;;                 [if (oh1(Succ n0))
;;                   ([n1,af1]n1 pair([a]2*af1 a+ ~(SdToInt s)))])))])
;;          ([n0,st,af0,oh1]
;;            (Get algwrite ysum(nat=>nat yprod(rat=>rat)))
;;            (st([a]af0((1#2)*(a+IntN 1)))
;;             ([n1][if (oh1 n1) ([n2,af1]n2 pair([a]af1((1#2)*(a+IntN 1))))]))
;;            (st([a]af0((1#2)*a))
;;             ([n1][if (oh1 n1) ([n2,af1]n2 pair([a]af1((1#2)*a)))]))
;;            (st([a]af0((1#2)*(a+1)))
;;             ([n1][if (oh1 n1) ([n2,af1]n2 pair([a]af1((1#2)*(a+1))))])))
;;          af 
;;          oh0)])

(deanimate "ContToCoWriteAux")
(deanimate "FindSd")
(deanimate "StandardSplit")

;; 2. A type-0 ucf to a type-1 ucf
;; ===============================

;; We now aim at the converse, CoWriteToCon

;; LemmaNine
;; OutElimCorsd
(set-goal "allnc f^ all s,m,n(
 (Sub xi)f^ 0 Zero(SdToInt s#2)(Succ Zero) ->
 all a exl b (Sub xi)((Outf xi)s f^)a m b n ->
 all a exl b (Sub xi)f^ a m b(Succ n))")
(assume "f^" "s" "m" "n" "f[I]subId" "BOut" "a")
(inst-with-to "BOut" (pt "a") "BOutInst")
(by-assume "BOutInst" "b" "bProp")
(intro 0 (pt "(1#2)*(b+SdToInt s)"))
(use "AxOutElim")
(use "f[I]subId")
(use "bProp")
;; Proof finished.
;; (cp)
(save "OutElimCor")

;; CoWriteToCon
(set-goal "allnc f^(CoWrite f^ -> all n exd m all a exl b (Sub xi)f^ a m b n)")
(cut "all n allnc f^(CoWrite f^ -> exd m all a exl b (Sub xi)f^ a m b n)")
 (assume "CutHyp" "f^" "CoWf" "n")
 (use "CutHyp")
 (use "CoWf")
(ind)
;; Base n=0
(assume "f^" "CoWf")
(intro 0 (pt "Zero"))
(assume "a")
(intro 0 (pt "0#1"))
(use "AxUcfBound")
;; Step n -> n+1
(assume "n" "IH" "f^" "CoWf")
(inst-with-to "CoWriteClause" (pt "f^") "CoWf" "ClauseHyp")
(elim "ClauseHyp")
;; Case IdF
(assume "f=IdF")
(intro 0 (pt "Succ n"))
(assume "a")
(intro 0 (pt "a"))
(simp "f=IdF")
(use "AxUcfIdF")
;; Case Read
(assume "ExHyp")
(by-assume "ExHyp" "f^0" "Conj")
(elim "Conj")
(assume "Readf0" "f=f0")
(simp "f=f0")
(elim "Readf0")
;; Side induction base
;; ?_29:allnc f^ 
;;       all s(
;;        (Sub xi)f^ 0 Zero(SdToInt s#2)(Succ Zero) -> 
;;        CoWrite((Outf xi)s f^) -> exd m all a exl b (Sub xi)f^ a m b(Succ n))
(assume "f^1" "s" "SubHyp" "CoWHyp")
(inst-with-to "IH" (pt "(Outf xi)s f^1") "CoWHyp" "IHInst")
(by-assume "IHInst" "m" "mProp")
(intro 0 (pt "m"))
(use "OutElimCor" (pt "s"))
(use "SubHyp")
(use "mProp")
;; Side induction step
;; ?_30:allnc f^(
;;       (Read (cterm (f^0) CoWrite f^0))((fIn xi)SdL f^) -> 
;;       exd m all a exl b (Sub xi)((fIn xi)SdL f^)a m b(Succ n) -> 
;;       (Read (cterm (f^0) CoWrite f^0))((fIn xi)SdM f^) -> 
;;       exd m all a exl b (Sub xi)((fIn xi)SdM f^)a m b(Succ n) -> 
;;       (Read (cterm (f^0) CoWrite f^0))((fIn xi)SdR f^) -> 
;;       exd m all a exl b (Sub xi)((fIn xi)SdR f^)a m b(Succ n) -> 
;;       exd m all a exl b (Sub xi)f^ a m b(Succ n))
(assume "f^1" "HReadL" "IHL" "HReadM" "IHM" "HReadR" "IHR")
(by-assume "IHL" "m0" "m0Prop")
(by-assume "IHM" "m1" "m1Prop")
(by-assume "IHR" "m2" "m2Prop")
(intro 0 (pt "Succ(m0 max m1 max m2)"))
(assume "a")
(inst-with-to "StandardSplit" (pt "a") "StandardSplitInst")
(elim "StandardSplitInst")
(assume "a<-1#4")
(inst-with-to "m0Prop" (pt "(2*a+ ~(SdToInt SdL))") "m0PropInst")
(by-assume "m0PropInst" "b" "bProp")
(intro 0 (pt "b"))
(assert "(Sub xi)f^1 a(Succ m0)b(Succ n)")
 (use "AxInElim" (pt "SdL"))
 (use "bProp")
(assume "(Sub xi)f^1 a(Succ m0)b(Succ n)")
(use "AxUcfWeak" (pt "Succ m0"))
(ng #t)
(use "NatLeTrans" (pt "m0 max m1"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "(Sub xi)f^1 a(Succ m0)b(Succ n)")
;; 55
(assume "MidOrRight")
(elim "MidOrRight")
(assume "(IntN 1#4)<=a & a<(1#4)")
(inst-with-to "m1Prop" (pt "(2*a+ ~(SdToInt SdM))") "m1PropInst")
(by-assume "m1PropInst" "b" "bProp")
(intro 0 (pt "b"))
(assert "(Sub xi)f^1 a(Succ m1)b(Succ n)")
 (use "AxInElim" (pt "SdM"))
 (use "bProp")
(assume "(Sub xi)f^1 a(Succ m1)b(Succ n)")
(use "AxUcfWeak" (pt "Succ m1"))
(ng #t)
(use "NatLeTrans" (pt "m0 max m1"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "(Sub xi)f^1 a(Succ m1)b(Succ n)")
;; 74
(assume "(1#4)<=a")
(inst-with-to "m2Prop" (pt "(2*a+ ~(SdToInt SdR))") "m2PropInst")
(by-assume "m2PropInst" "b" "bProp")
(intro 0 (pt "b"))
(assert "(Sub xi)f^1 a(Succ m2)b(Succ n)")
 (use "AxInElim" (pt "SdR"))
 (use "bProp")
(assume "(Sub xi)f^1 a(Succ m2)b(Succ n)")
(use "AxUcfWeak" (pt "Succ m2"))
(ng #t)
(use "NatMaxUB2")
(use "(Sub xi)f^1 a(Succ m2)b(Succ n)")
;; Proof finished.
;; (cp)
(save "CoWriteToCont")

(add-var-name "naf" (py "nat yprod(rat=>rat)"))
(add-var-name "nafs" (py "algwrite=>nat yprod(rat=>rat)"))
(add-var-name "rw" (py "algread algwrite"))
(add-var-name "w" (py "algwrite"))

(define eterm-b (proof-to-extracted-term))
(define neterm-b (rename-variables (nt eterm-b)))
(ppc neterm-b)

;; [w,n]
;;  (Rec nat=>algwrite=>nat yprod(rat=>rat))n([w0]Zero pair([a]0))
;;  ([n0,nafs,w0]
;;    [case (Des w0)
;;      (DummyL -> Succ n0 pair([a]a))
;;      (Inr rw -> 
;;      (Rec algread algwrite=>nat yprod(rat=>rat))rw
;;      ([s,w1][case (nafs w1) (n1 pair af -> n1 pair cOutElimCor s n1 n0 af)])
;;      ([rw0,naf,rw1,naf0,rw2,naf1]
;;        [case naf
;;          (n1 pair af -> 
;;          [case naf0
;;            (n2 pair af0 -> 
;;            [case naf1
;;              (n3 pair af1 -> 
;;              Succ(n1 max n2 max n3)pair
;;              ([a]
;;                [case (cStandardSplit a)
;;                  (DummyL -> af(2*a+1))
;;                  (Inr boole -> 
;; 		      [case boole
;; 			(True -> af0(2*a))
;; 			(False -> af1(2*a+IntN 1))])]))])])]))])
;;  w

(animate "OutElimCor")
(animate "StandardSplit")

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "CoWriteToCont")))))

;; [w,n]
;;  (Rec nat=>algwrite=>nat yprod(rat=>rat))n([w0]Zero pair([a]0))
;;  ([n0,nafs,w0]
;;    [case (Des w0)
;;      (DummyL -> Succ n0 pair([a]a))
;;      (Inr rw -> 
;;      (Rec algread algwrite=>nat yprod(rat=>rat))rw
;;      ([s,w1]
;;        [case (nafs w1) (n1 pair af -> n1 pair([a](1#2)*(af a+SdToInt s)))])
;;      ([rw0,naf,rw1,naf0,rw2,naf1]
;;        [case naf
;;          (n1 pair af -> 
;;          [case naf0
;;            (n2 pair af0 -> 
;;            [case naf1
;;              (n3 pair af1 -> 
;;              Succ(n1 max n2 max n3)pair
;;              ([a]
;;                [case a
;;                  (k#p -> 
;;                  [case k
;;                    (p0 -> 
;;                    [case (SZero(SZero p0)<p)
;;                      (True -> af0(2*a))
;;                      (False -> af1(2*a+IntN 1))])
;;                    (0 -> af0(2*a))
;;                    (IntN p0 -> 
;;                    [case (SZero(SZero p0)<=p)
;;                      (True -> af0(2*a))
;;                      (False -> af(2*a+1))])])]))])])]))])
;;  w

(deanimate "OutElimCor")
(deanimate "StandardSplit")

;; 3. Applying a type-0 ucf to a type-0 real number
;; ================================================

;; This section is related to examples/analysis/average.scm.  There we
;; axiomatized (by somewhat ad hoc rewrite rules) the constants IntToR
;; P (plus) and H (half).  Here we use axioms for Z (zero) Av
;; (average) Va (inverse of average) and Elem (x in I_{a,n}) instead.

(remove-var-name "x" "y" "z") ;will be used for abstract reals
(remove-var-name "r")
(remove-token "r")
(add-tvar-name "r") ;abstract real
(add-var-name "x" "y" "z" (py "r"))

(add-program-constant "Z" (py "r")) ;zero
(add-program-constant "Av" (py "r=>sd=>r")) ;average
(add-program-constant "Va" (py "r=>sd=>r")) ;inverse of average
(add-program-constant "Elem" (py "r=>rat=>nat=>boole"))

(add-algs "iv" '("II" "iv") '("C" "sd=>iv=>iv"))

;; We inductively define a set I of reals.

(add-ids (list (list "I" (make-arity (py "r")) "iv"))
	 '("I(Z r)" "InitI")
	 '("allnc x^ all s(I x^ -> I((Av r)x^ s))" "GenI"))

(add-co "I")

(add-program-constant "App" (py "xi=>r=>r"))

(add-global-assumption
 "AxAvVaId"
 "all x^,s((Elem r)x^(SdToInt s#2)(Succ Zero) ->
            x^ eqd(Av r)((Va r)x^ s)s)")

(add-global-assumption
 "AxVaAvId"
 "all x^,s(x^ eqd(Va r)((Av r)x^ s)s)")

(add-global-assumption
 "AxAvZero"
 "(Av r)(Z r)SdM eqd (Z r)")

(add-global-assumption
 "AxAppId"
 "all x^((App xi r)(IdF xi)x^ eqd x^)")

(add-global-assumption
 "AxApohubElem"
 "all f^,x^,b,n((Sub xi)f^ 0 Zero b n -> (Elem r)((App xi r)f^ x^)b n)")

(add-global-assumption
 "AxVaOut"
 "all f^,x^,s((Sub xi)f^ 0 Zero(SdToInt s#2)(Succ Zero) ->
   (Va r)((App xi r)f^ x^)s eqd(App xi r)((Outf xi)s f^)x^)")

(add-global-assumption
 "AxAvIn"
 "all f^,x^,s((App xi r)f^((Av r)x^ s)eqd(App xi r)((fIn xi)s f^)x^)")

;; LemmaApply
(set-goal "allnc f^0(
     (Read (cterm (f^) CoWrite f^))f^0 ->
     allnc x^0(
      CoI x^0 ->
      (App xi r)f^0 x^0 eqd(Z r) orr
      exr y^
       exd s(
        (CoI y^ ord
         exr f^1,x^1(
        y^ eqd(App xi r)f^1 x^1 andi CoWrite f^1 andi CoI x^1)) andi
        (App xi r)f^0 x^0 eqd(Av r)y^ s)))")
(assume "f^0" "Read f0")
(elim "Read f0")
;; 3,4
(assume "f^1" "s" "Cod f sub I_s" "CoW(Out s f)" "x^0" "CoI x0")
(intro 1)
(intro 0 (pt "(App xi r)((Outf xi) s f^1)x^0"))
(intro 0 (pt "s"))
(split)
(intro 1)
(intro 0 (pt "(Outf xi)s f^1"))
(intro 0 (pt "x^0"))
(split)
(use "InitEqD")
(split)
(use "CoW(Out s f)")
(use "CoI x0")
(simp "<-" "AxVaOut")
(simp "<-" "AxAvVaId")
(use "InitEqD")
(use "AxApohubElem")
(use "Cod f sub I_s")
(use "Cod f sub I_s")
;; 4
(assume "f^" "HypRL" "IHL" "HypRM" "IHM" "HypRR" "IHR" "x^0" "CoI x0")
(inst-with-to "CoIClause" (pt "x^0") "CoI x0" "HCases CoI x0")
(elim "HCases CoI x0")
;; Left case
(assume "x0=0")
(inst-with-to "IHM" (pt "x^0") "CoI x0" "IHMInst")
(assert "(App xi r)f^ x^0 eqd(App xi r)((fIn xi)SdM f^)x^0")
 (simp "x0=0")
 (simp "<-" "AxAvIn")
 (simp "AxAvZero")
 (use "InitEqD")
(assume "Heq")
(simp "Heq")
(use "IHMInst")
;; Right case
(assume "Hexex")
(elim "Hexex")
(assume "x^1" "Hex")
(by-assume "Hex" "s1" "H0")
(inst-with-to "H0" 'left "CoI x1")
(cases (pt "s1"))
;; Three subcases: R
(assume "CaseR")
(inst-with-to "IHR" (pt "x^1") "CoI x1" "IHRInst")
(elim "H0")
(assume "H0L" "H0R")
(simp "H0R" 'right)
(simp "CaseR")
(simp "AxAvIn")
(use "IHRInst")
;; Three subcases: M
(assume "CaseM")
(inst-with-to "IHM" (pt "x^1") "CoI x1" "IHMInst")
(elim "H0")
(assume "H0L" "H0R")
(simp "H0R" 'right)
(simp "CaseM")
(simp "AxAvIn")
(use "IHMInst")
;; Three subcases: L
(assume "CaseL")
(inst-with-to "IHL" (pt "x^1") "CoI x1" "IHLInst")
(elim "H0")
(assume "H0L" "H0R")
(simp "H0R" 'right)
(simp "CaseL")
(simp "AxAvIn")
(use "IHLInst")
;; Proof finished.
;; (cp)
(save "LemmaApply")

(add-var-name "niv" (py "iv=>uysum(sd yprod(iv ysum algwrite yprod iv))"))

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [rw]
;;  (Rec algread algwrite=>iv=>uysum(sd yprod(iv ysum algwrite yprod iv)))rw
;;  ([s,w,iv]Inr(s pair InR(w pair iv)))
;;  ([rw0,niv,rw1,niv0,rw2,niv1,iv]
;;    [case (DesYprod iv)
;;      (DummyL -> niv0 iv)
;;      (Inr(sd yprod iv) -> 
;;      [case (sd yprod iv)
;;        (s pair iv0 -> 
;;        [case s (SdR -> niv1 iv0) (SdM -> niv0 iv0) (SdL -> niv iv0)])])])

;; PropApply
(set-goal "allnc f^,x^(CoWrite f^ -> CoI x^ -> CoI((App xi r)f^ x^))")
(assume "f^" "x^" "CoW f" "CoI x")
;; Preparing our competitor
(assert "exr f^1,x^1((App xi r)f^ x^ eqd(App xi r)f^1 x^1 andi
                      CoWrite f^1 andi CoI x^1)")
 (intro 0 (pt "f^"))
 (intro 0 (pt "x^"))
 (split)
 (use "InitEqD")
 (split)
 (use "CoW f")
 (use "CoI x")
;; Assuming our competitor
(assume "Q z")
(coind "Q z")
(assume "z^0" "Q z0")
(elim "Q z0")
(assume "f^0" "Hex")
(elim "Hex")
(assume "x^0" "Hand")
(inst-with-to "Hand" 'right 'left "CoW f0")
(inst-with-to "Hand" 'right 'right "CoI x0")
(inst-with-to "CoWriteClause" (pt "f^0") "CoW f0" "HCases")
(elim "HCases")
;; 24,25
;; Case f0 = Id
(assume "f0 eqd Id")
(inst-with-to "CoIClause" (pt "x^0") "CoI x0" "HCases x0")
(elim "HCases x0")
(assume "x0=0")
(intro 0)
(simp "Hand")
(simp "f0 eqd Id")
(simp "x0=0")
(use "AxAppId")
(assume "Hexrex")
(intro 1)
(elim "Hexrex")
(assume "x^1" "Hex 2")
(intro 0 (pt "x^1"))
(by-assume "Hex 2" "s" "Heqd")
(intro 0 (pt "s"))
(split)
(intro 0)
(use "Heqd")
(simp "Hand")
(simp "f0 eqd Id")
(elim "Heqd")
(assume "HeqdL" "HeqdR")
(simp "HeqdR")
(use "AxAppId")
;; ?_25:exr f^((Read (cterm (f^1) CoWrite f^1))f^ andl f^0 eqd f^) -> 
;;      z^0 eqd(Z r) orr 
;;      exr x^ 
;;       exd s(
;;        (CoI x^ ord 
;;        exr f^,x^0(x^ eqd(App xi r)f^ x^0 andr CoWrite f^ andd CoI x^0)) andl 
;;        z^0 eqd(Av r)x^ s)
(assume "HypRead")
(assert "(Read (cterm (f^1) CoWrite f^1))f^0")
 (elim "HypRead")
 (assume "f^1" "H1")
 (elim "H1")
 (assume "H1L" "H1R")
 (simp "H1R")
 (use "H1")
(assume "HRead")
(assert "(App xi r)f^0 x^0 eqd(Z r) orr
      exr x^
       exd s(
        (CoI x^ ord
         exr f^,x^0(x^ eqd(App xi r)f^ x^0 andi CoWrite f^ andi CoI x^0)) andl
        (App xi r)f^0 x^0 eqd(Av r)x^ s)")
 (use "LemmaApply")
 (use "HRead")
 (use "CoI x0")
(assume "H2")
(elim "H2")
(assume "Hleft")
(intro 0)
(simp "Hand")
(use "Hleft")
(assume "Hright")
(intro 1)
(simp "Hand")
(use "Hright")
;; Proof finished.
;; (cp)
(save "PropApply")

(define eterm-apply (proof-to-extracted-term))

(add-var-name "wiv" (py "algwrite yprod iv"))
(add-var-name "siv" (py "sd yprod iv"))

(define neterm-apply (rename-variables (nt eterm-apply)))
(pp neterm-apply)

;; [w,iv]
;;  (CoRec algwrite yprod iv=>iv)(w pair iv)
;;  ([wiv]
;;    [if (Des clft wiv)
;;      [if (DesYprod crht wiv)
;;       (DummyL sd yprod(iv ysum algwrite yprod iv))
;;       ([siv]Inr[if siv ([s,iv0]s pair(InL iv (algwrite yprod iv))iv0)])]
;;      ([rw]cLemmaApply rw crht wiv)])

(animate "LemmaApply")

(define neterm-apply (rename-variables (nt eterm-apply)))
(pp neterm-apply)

;; [w,iv]
;;  (CoRec algwrite yprod iv=>iv)(w pair iv)
;;  ([wiv]
;;    [if (Des clft wiv)
;;      [if (DesYprod crht wiv)
;;       (DummyL sd yprod(iv ysum algwrite yprod iv))
;;       ([siv]Inr[if siv ([s,iv0]s pair(InL iv (algwrite yprod iv))iv0)])]
;;      ([rw]
;;       (Rec algread algwrite=>iv=>uysum(sd yprod(iv ysum algwrite yprod iv)))
;;       rw
;;       ([s,w0,iv0]Inr(s pair(InR (algwrite yprod iv) iv)(w0 pair iv0)))
;;       ([rw0,niv,rw1,niv0,rw2,niv1,iv0]
;;         [if (DesYprod iv0)
;;           (niv0 iv0)
;;           ([siv][if siv ([s,iv1][if s (niv1 iv1) (niv0 iv1) (niv iv1)])])])
;;       crht wiv)])

(deanimate "LemmaApply")

;; 4. Composing ucfs
;; =================

(add-global-assumption
 "AxIdIn"
 "all s (Sub xi)((fIn xi)s(IdF xi))0 Zero(SdToInt s#2)(Succ Zero)")

(add-global-assumption
 "AxOutInId"
 "all s (Outf xi)s((fIn xi)s(IdF xi))eqd(IdF xi)")

(add-global-assumption
 "AxUcfIn"
 "all f^,b,n,s((Sub xi)f^ 0 Zero b n -> (Sub xi)((fIn xi)s f^)0 Zero b n)")

(add-global-assumption
 "AxUcfOutInInOut"
 "all f^,s1,s2(
  (Sub xi)f^ 0 Zero(SdToInt s1#2)(Succ Zero) ->
  (Outf xi)s1((fIn xi)s2 f^)eqd(fIn xi)s2((Outf xi)s1 f^))")

;; CoWriteIn
(set-goal "allnc f^ all s(CoWrite f^ -> CoWrite((fIn xi)s f^))")
(assume "f^" "s" "CoWf")
(assert "exr f^1(CoWrite f^1 andl (fIn xi)s f^ eqd (fIn xi)s f^1)")
 (intro 0 (pt "f^"))
 (split)
 (use "CoWf")
 (use "InitEqD")
(assume "Pf")
(coind "Pf")
(assume "f^1" "Pf1")
(by-assume "Pf1" "f^2" "Hyp1")
(inst-with-to "Hyp1" 'left "CoWf2")
(inst-with-to "Hyp1" 'right "Eq")
(simp "Eq")
(inst-with-to "CoWriteClause" (pt "f^2") "CoWf2" "Case f2")
(elim "Case f2")
;; left
(assume "f2=Id")
(intro 1)
(simp "f2=Id")
(intro 0 (pt "(fIn xi)s(IdF xi)"))
(split)
(intro 0 (pt "s"))
(use "AxIdIn")
(simp "AxOutInId")
(intro 0)
(simp "<-" "f2=Id")
(use "CoWf2")
(use "InitEqD")
;; right
(assume "Hyp2")
(by-assume "Hyp2" "f^3" "Read f3 and eq")
(intro 1)
(inst-with-to "Read f3 and eq" 'left "Read f3")
(intro 0 (pt "(fIn xi)s f^2"))
(split)
(elim "Read f3 and eq")
(assume "Read f3 2" "Heq")
(simp "Heq")
(elim "Read f3")
(assume "f^4" "s1" "f[I] sub I_s1" "CoWrite out f")
(intro 0 (pt "s1"))
(use "AxUcfIn")
(use "f[I] sub I_s1")
(intro 1)
(intro 0 (pt "(Outf xi)s1 f^4"))
(split)
(use "CoWrite out f")
(use "AxUcfOutInInOut")
(use "f[I] sub I_s1")
;; 48
(assume "f^4" "Read L" "IH L" "Read M" "IH M" "Read R" "IH R")
(cases (pt "s"))
;; 59-61
(assume "Case R")
(elim "Read R")
(assume "f^5" "s1" "f5[I] sub I_s1" "CoWrite out f5")
(intro 0 (pt "s1"))
(use "f5[I] sub I_s1")
(intro 0)
(use "CoWrite out f5")
(assume "f^5" "Sub Read L" "Sub IH L" "Sub Read M" "Sub IH M"
	"Sub Read R" "Sub IH R")
(intro 1)
(use "Sub IH L")
(use "Sub IH M")
(use "Sub IH R")
;; 60
(assume "Case M")
(elim "Read M")
(assume "f^5" "s1" "f5[I] sub I_s1" "CoWrite out f5")
(intro 0 (pt "s1"))
(use "f5[I] sub I_s1")
(intro 0)
(use "CoWrite out f5")
(assume "f^5" "Sub Read L" "Sub IH L" "Sub Read M" "Sub IH M"
	"Sub Read R" "Sub IH R")
(intro 1)
(use "Sub IH L")
(use "Sub IH M")
(use "Sub IH R")
;; 61
(assume "Case L")
(elim "Read L")
(assume "f^5" "s1" "f5[I] sub I_s1" "CoWrite out f5")
(intro 0 (pt "s1"))
(use "f5[I] sub I_s1")
(intro 0)
(use "CoWrite out f5")
(assume "f^5" "Sub Read L" "Sub IH L" "Sub Read M"
	"Sub IH M" "Sub Read R" "Sub IH R")
(intro 1)
(use "Sub IH L")
(use "Sub IH M")
(use "Sub IH R")
;; 43
(use "InitEqD")
;; Proof finished.
(cp)
(save "CoWriteIn") ;was Lemma 10

(define eterm (proof-to-extracted-term))
(add-var-name "rww" (py "algread(algwrite ysum algwrite)"))

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [s,w]
;;  (CoRec algwrite=>algwrite)w
;;  ([w0]
;;    [if (Des w0)
;;      (Inr((Put algwrite ysum algwrite)s((InL algwrite algwrite)w0)))
;;      ([rw]
;;       Inr[if rw
;;            ([s0,w1](Put algwrite ysum algwrite)s0((InR algwrite algwrite)w1))
;;            ([rw0,rw1,rw2]
;;             [if s
;;               ((Rec algread algwrite=>algread(algwrite ysum algwrite))rw2
;;               ([s0,w1]
;;                 (Put algwrite ysum algwrite)s0((InL algwrite algwrite)w1))
;;               ([rw3,rww,rw4,rww0,rw5](Get algwrite ysum algwrite)rww rww0))
;;               ((Rec algread algwrite=>algread(algwrite ysum algwrite))rw1
;;               ([s0,w1]
;;                 (Put algwrite ysum algwrite)s0((InL algwrite algwrite)w1))
;;               ([rw3,rww,rw4,rww0,rw5](Get algwrite ysum algwrite)rww rww0))
;;               ((Rec algread algwrite=>algread(algwrite ysum algwrite))rw0
;;               ([s0,w1]
;;                 (Put algwrite ysum algwrite)s0((InL algwrite algwrite)w1))
;;               ([rw3,rww,rw4,rww0,rw5]
;; 	       (Get algwrite ysum algwrite)rww rww0))])])])

(ppc neterm)

;; [s,w]
;;  (CoRec algwrite=>algwrite)w
;;  ([w0]
;;    [case (Des w0)
;;      (DummyL -> Inr(Put s(InL w0)))
;;      (Inr rw -> 
;;      Inr[case rw
;;           (Put s0 w1 -> Put s0(InR w1))
;;           (Get rw0 rw1 rw2 -> 
;;           [case s
;;             (SdR -> 
;;             (Rec algread algwrite=>algread(algwrite ysum algwrite))rw2
;;             ([s0,w1]Put s0(InL w1))
;;             ([rw3,rww,rw4,rww0,rw5]Get rww rww0))
;;             (SdM -> 
;;             (Rec algread algwrite=>algread(algwrite ysum algwrite))rw1
;;             ([s0,w1]Put s0(InL w1))
;;             ([rw3,rww,rw4,rww0,rw5]Get rww rww0))
;;             (SdL -> 
;;             (Rec algread algwrite=>algread(algwrite ysum algwrite))rw0
;;             ([s0,w1]Put s0(InL w1))
;;             ([rw3,rww,rw4,rww0,rw5]Get rww rww0))])])])

(add-program-constant "Cmp" (py "xi=>xi=>xi"))

(add-global-assumption
 "AxCmpIdL"
 "all f^((Cmp xi)(IdF xi)f^ eqd f^)")

(add-global-assumption
 "AxCmpIdR"
 "all f^((Cmp xi)f^(IdF xi)eqd f^)")

(add-global-assumption
 "AxCmpBound"
 "all f^1,f^2,s((Sub xi)f^1 0 Zero(SdToInt s#2)(Succ Zero) ->
  (Sub xi)((Cmp xi)f^1 f^2) 0 Zero(SdToInt s#2)(Succ Zero))")

(add-global-assumption
 "AxAssocOutCmp"
 "all f^1,f^2,s((Sub xi)f^1 0 Zero(SdToInt s#2)(Succ Zero) ->
  (Cmp xi)((Outf xi)s f^1)f^2 eqd(Outf xi)s((Cmp xi)f^1 f^2))")

(add-global-assumption
 "AxOutIntroI"
 "all f^,s(
 (Sub xi)f^ 0 Zero(SdToInt s#2)(Succ Zero) ->
 (Sub xi)((Outf xi)s f^)0 Zero 0 Zero)")

(add-global-assumption
 "AxInOutId"
 "all f^1,f^2,s((Sub xi)f^2 0 Zero(SdToInt s#2)(Succ Zero) ->
   (Cmp xi)f^1 f^2 eqd(Cmp xi)((fIn xi)s f^1)((Outf xi)s f^2))")

(add-global-assumption
 "AxAssocCmpIn"
 "all f^1,f^2,s (fIn xi)s((Cmp xi)f^1 f^2)eqd(Cmp xi)f^1((fIn xi)s f^2)")

;; PropCompose
;; Cowrite f -> CoWrite g -> Cowrite (f g)
(set-goal "allnc f^1,f^2(CoWrite f^1 -> CoWrite f^2 ->
                         CoWrite((Cmp xi)f^1 f^2))")
(assume "f^1" "f^2" "CoWf1" "CoWf2")
(assert "exr f^3,f^4(CoWrite f^3 andd CoWrite f^4 andl
                     (Cmp xi)f^1 f^2 eqd(Cmp xi)f^3 f^4)")
 (intro 0 (pt "f^1"))
 (intro 0 (pt "f^2"))
 (split)
 (use "CoWf1")
 (split)
 (use "CoWf2")
 (use "InitEqD")
(assume "P(f1 o f2)")
(coind "P(f1 o f2)")
(drop "P(f1 o f2)")
(assume "f^3" "Pf3")
(by-assume "Pf3" "f^4" "Pf3 2")
(by-assume "Pf3 2" "f^5" "Hyp")
(inst-with-to "Hyp" 'left "CoWf4")
(inst-with-to "Hyp" 'right 'left "CoWf5")
(inst-with-to "Hyp" 'right 'right "Eq")
(drop "Hyp")
(inst-with-to "CoWriteClause" (pt "f^4") "CoWf4" "Clause f4")
(inst-with-to "CoWriteClause" (pt "f^5") "CoWf5" "Clause f5")
(simp "Eq")
;; Case id f4 or R f4
(elim "Clause f4")
(drop "Clause f4")
(assume "f4=Id")
(simp "f4=Id")
(drop "f4=Id")
(simp "AxCmpIdL")
;; Case id f5 or R f5
(elim "Clause f5")
;; id id
(assume "f5=Id")
(simp "f5=Id")
(intro 0)
(use "InitEqD")
;; id Read
(assume "Ex Read f5")
(by-assume "Ex Read f5" "f^6" "Read f5")
(inst-with-to "Read f5" 'left "Read f6")
(elim "Read f5")
(drop "Read f5")
(assume "Read f6 2" "f5=f6")
(drop "Read f6 2")
(simp "f5=f6")
(intro 1)
(intro 0 (pt "f^6"))
(split)
(elim "Read f6")
(drop "Read f6")
(assume "f^7" "s" "f[I] sub I_d" "CoWrite outd f")
(intro 0 (pt "s"))
(use "f[I] sub I_d")
(intro 0)
(use "CoWrite outd f")
;; 61
(assume "f^7" "Read L" "IH L" "Read M" "IH M" "Read R" "IH R")
(intro 1)
(use "IH L")
(use "IH M")
(use "IH R")
(use "InitEqD")
;; 34
(assume "Ex Read f4")
(by-assume "Ex Read f4" "f^6" "Read f6")
(elim "Read f6")
(assume "Useless1" "f4=f6")
(drop "Useless1")
(simp "f4=f6")
(elim "Clause f5")
;; R id
(assume "f5=Id")
(simp "f5=Id")
(simp "AxCmpIdR")
(intro 1)
(intro 0 (pt "f^6"))
(split)
(inst-with-to "Read f6" 'left "Read f6 3")
(elim "Read f6 3")
(assume "f^7" "s" "f[I] sub I_d" "CoWrite outd f")
(intro 0 (pt "s"))
(use "f[I] sub I_d")
(intro 0)
(use "CoWrite outd f")
(assume "f^7" "Read L" "IH L" "Read M" "IH M" "Read R" "IH R")
(intro 1)
(use "IH L")
(use "IH M")
(use "IH R")
(use "InitEqD")
;; R R
(assume "Ex Read f5")
(by-assume "Ex Read f5" "f^7" "Read f7")
(elim "Read f7")
(assume "Useless2" "f5=f7")
(drop "Useless2")
(simp "f5=f7")
(inst-with-to "Read f6" 'left "Read f6 inst")
;; (inst-with-to "Read f7" 'left "Read f7 inst")
(cut "allnc f^0(CoWrite f^0 -> (Sub xi)f^0 0 Zero 0 Zero ->
      exr f^(
       (Read (cterm (f^0) CoWrite f^0 ord
              exr f^1,f^2(CoWrite f^1 andd CoWrite f^2 andl
                          f^0 eqd(Cmp xi)f^1 f^2)))
       f^ andl (Cmp xi)f^6 f^0 eqd f^))")
 (assume "Hyp2")
 (inst-with-to "Hyp2" (pt "f^5") "CoWf5" "Hyp2 inst")
 (intro 1)
 (simp "<-" "f5=f7")
 (use "Hyp2 inst")
 (use "AxUcfBound")
;; Main Ind
(elim "Read f6 inst")
(drop "Read f6 inst")
;; Base case
(assume "f^" "s" "f[I] sub I_s" "CoWrite outd s f"
	"f^0" "CoWf0" "f0 in I")
(intro 0 (pt "(Cmp xi)f^ f^0"))
(split)
(intro 0 (pt "s"))
(use "AxCmpBound")
(use "f[I] sub I_s")
(intro 1)
(intro 0 (pt "(Outf xi)s f^"))
(intro 0 (pt "f^0"))
(split)
(use "CoWrite outd s f")
(split)
(use "CoWf0")
(simp "AxAssocOutCmp")
(use "InitEqD")
(use "f[I] sub I_s")
(use "InitEqD")
;; Step case
(assume "f^" "ReadL" "IHL" "ReadM" "IHM" "ReadR" "IHR" "f^8" "CoWf8" "f8 in I")
(drop "ReadL" "IHL" "ReadM" "IHM" "ReadR" "IHR")
(inst-with-to "CoWriteClause" (pt "f^8") "CoWf8" "Case f8")
(elim "Case f8") ;141-142
(drop "Case f8")
;; Left. f8=Id
(assume "f8=Id")
(simp "f8=Id")
(simp "AxCmpIdR")
(intro 0 (pt "f^"))
(split)
(intro 1)
(inst-with-to "IHL" (pt "f^8") "CoWf8" "f8 in I" "IHLinst")
(by-assume "IHLinst" "f^9" "HypL and")
(inst-with-to "HypL and" 'left "HypL")
(simp-with "<-" "AxCmpIdR" (pt "(fIn xi)SdL f^"))
(simp "<-" "f8=Id")
(elim "HypL and")
(drop "HypL and")
(assume "Useless3" "Heq3")
(simp "Heq3")
(drop "Useless3" "Heq3")
(use "HypL")
;; 150
(inst-with-to "IHM" (pt "f^8") "CoWf8" "f8 in I" "IHMinst")
(by-assume "IHMinst" "f^9" "HypM and")
(inst-with-to "HypM and" 'right "HeqM")
(simp-with "<-" "AxCmpIdR" (pt "(fIn xi)SdM f^"))
(simp "<-" "f8=Id")
(simp "HeqM")
(use "HypM and")
;; 151
(inst-with-to "IHR" (pt "f^8") "CoWf8" "f8 in I" "IHRinst")
(by-assume "IHRinst" "f^9" "HypR and")
(simp-with "<-" "AxCmpIdR" (pt "(fIn xi)SdR f^"))
(simp "<-" "f8=Id")
(inst-with-to "HypR and" 'right "HeqR")
(simp "HeqR")
(use "HypR and")
;; 148
(use "InitEqD")
;; 141
(drop "Case f8")
;; Right. Readf8
(assume "Hex Readf8")
(by-assume "Hex Readf8" "f^9" "Hand Readf9")
(inst-with-to "Hand Readf9" 'left "Readf9")
(assert "CoWrite f^8")
 (use "CoWf8")
(elim "Hand Readf9")
(drop "Hand Readf9")
(assume "Useless4" "f8=f9")
(simp "f8=f9")
(drop "Useless4" "f8=f9")
;; 199
;; Sub ind
(elim "Readf9")
(drop "Readf9")
;; Sub base
(assume "f^10" "s" "f10[I] sub I_s" "CoWrite out f10" "CoWf10")
(assert "(Sub xi)((Outf xi)s f^10)0 Zero 0 Zero")
 (use "AxOutIntroI")
 (use "f10[I] sub I_s")
(assume "Outf f10 in I")
(simp-with "AxInOutId" (pt "f^") (pt "f^10") (pt "s")
	   "f10[I] sub I_s")
(cases (pt "s"))
;; 209-211
(assume "Case R")
(assert "CoWrite((Outf xi)SdR f^10)")
 (simp "<-" "Case R")
 (use "CoWrite out f10")
(assume "CoWrite outR f10")
(simphyp-with-to "Outf f10 in I" "Case R" "Outf R f10 in I")
(inst-with-to "IHR" (pt "(Outf xi)SdR f^10") "CoWrite outR f10"
	      "Outf R f10 in I" "Hex IHR")
(use "Hex IHR")
;; 210
(assume "Case M")
(assert "CoWrite((Outf xi)SdM f^10)")
 (simp "<-" "Case M")
 (use "CoWrite out f10")
(assume "CoWrite outM f10")
(simphyp-with-to "Outf f10 in I" "Case M" "Outf M f10 in I")
(inst-with-to "IHM" (pt "(Outf xi)SdM f^10") "CoWrite outM f10"
	      "Outf M f10 in I" "Hex IHM")
(use "Hex IHM")
;; 211
(assume "Case L")
(assert "CoWrite((Outf xi)SdL f^10)")
 (simp "<-" "Case L")
 (use "CoWrite out f10")
(assume "CoWrite outL f10")
(simphyp-with-to "Outf f10 in I" "Case L" "Outf L f10 in I")
(inst-with-to "IHL" (pt "(Outf xi)SdL f^10") "CoWrite outL f10"
	      "Outf L f10 in I" "Hex IHL")
(use "Hex IHL")
;; 201
;; Sub step
(assume "f^10" "SubReadL" "SubIHL" "SubReadM" "SubIHM" "SubReadR" "SubIHR"
	"CoWf10")
(inst-with-to "CoWriteIn" (pt "f^10") (pt "SdL") "CoWf10" "CoWf10 inL")
(inst-with-to "SubIHL" "CoWf10 inL" "Hex SubIHL")
(drop "SubIHL" "CoWf10 inL")
(inst-with-to "CoWriteIn" (pt "f^10") (pt "SdM") "CoWf10" "CoWf10 inM")
(inst-with-to "SubIHM" "CoWf10 inM" "Hex SubIHM")
(drop "SubIHM" "CoWf10 inM")
(inst-with-to "CoWriteIn" (pt "f^10") (pt "SdR") "CoWf10" "CoWf10 inR")
(inst-with-to "SubIHR" "CoWf10 inR" "Hex SubIHR")
(drop "SubIHR" "CoWf10 inR")
;; 254
(intro 0 (pt "(Cmp xi)f^ f^10"))
(split)
(intro 1)
(by-assume "Hex SubIHL" "f^11" "Hand SubIHL")
(simp "AxAssocCmpIn")
(elim "Hand SubIHL")
(assume "Hand SubIHL L" "HeqL")
(simp "HeqL")
(use "Hand SubIHL L")
;; 259
(by-assume "Hex SubIHM" "f^11" "Hand SubIHM")
(simp "AxAssocCmpIn")
(elim "Hand SubIHM")
(assume "HandSubIHML" "HandSubIHMR")
(simp "HandSubIHMR")
(use "HandSubIHML")
;; 269
(by-assume "Hex SubIHR" "f^11" "Hand SubIHR")
(simp "AxAssocCmpIn")
(elim "Hand SubIHR")
(assume "HandSubIHRL" "HandSubIHRR")
(simp "HandSubIHRR")
(use "HandSubIHRL")
;; 257
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "PropCompose")

(define eterm-cmp (proof-to-extracted-term))

(add-var-name "rq" (py "algread(algwrite ysum algwrite yprod algwrite)"))
(add-var-name
 "fwrq" (py "algwrite=>algread(algwrite ysum algwrite yprod algwrite)"))
(add-var-name "ww" (py "algwrite yprod algwrite"))

(define neterm-cmp (rename-variables (nt eterm-cmp)))

(pp neterm-cmp)

;; [w,w0]
;;  (CoRec algwrite yprod algwrite=>algwrite)(w pair w0)
;;  ([ww]
;;    [if (Des clft ww)
;;      [if (Des crht ww)
;;       (DummyL algread(algwrite ysum algwrite yprod algwrite))
;;       ([rw]
;;        Inr((Rec algread algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;            rw
;;            ([s,w1]
;;              (Put algwrite ysum algwrite yprod algwrite)s
;;              ((InL algwrite (algwrite yprod algwrite))w1))
;;            ([rw0,rq,rw1,rq0,rw2]
;;              (Get algwrite ysum algwrite yprod algwrite)rq rq0)))]
;;      ([rw]
;;       [if (Des crht ww)
;;         (Inr((Rec algread algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;             rw
;;             ([s,w1]
;;               (Put algwrite ysum algwrite yprod algwrite)s
;;               ((InL algwrite (algwrite yprod algwrite))w1))
;;             ([rw0,rq,rw1,rq0,rw2]
;;               (Get algwrite ysum algwrite yprod algwrite)rq rq0)))
;;         ([rw0]
;;          Inr((Rec algread algwrite=>algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;              rw
;;              ([s,w1,w2]
;;                (Put algwrite ysum algwrite yprod algwrite)s
;;                ((InR (algwrite yprod algwrite) algwrite)(w1 pair w2)))
;;              ([rw1,fwrq,rw2,fwrq0,rw3,fwrq1,w1]
;;                [if (Des w1)
;;                  ((Get algwrite ysum algwrite yprod algwrite)(fwrq w1)
;;                  (fwrq0 w1)
;;                  (fwrq1 w1))
;;                  ([rw4]
;;                   (Rec algread algwrite=>algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;                   rw4
;;                   ([s,w2,w3][if s (fwrq1 w2) (fwrq0 w2) (fwrq w2)])
;;                   ([rw5,fwrq2,rw6,fwrq3,rw7,fwrq4,w2]
;;                     (Get algwrite ysum algwrite yprod algwrite)
;;                     (fwrq2(cCoWriteIn SdL w2))
;;                     (fwrq3(cCoWriteIn SdM w2))
;;                     (fwrq4(cCoWriteIn SdR w2)))
;;                   w1)])
;;              crht ww))])])

(ppc neterm-cmp)

;; [w,w0]
;;  (CoRec algwrite yprod algwrite=>algwrite)(w pair w0)
;;  ([ww]
;;    [case (Des clft ww)
;;      (DummyL -> 
;;      [case (Des crht ww)
;;        (DummyL -> DummyL)
;;        (Inr rw -> 
;;        Inr((Rec algread algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;            rw
;;            ([s,w1]Put s(InL w1))
;;            ([rw0,rq,rw1,rq0,rw2]Get rq rq0)))])
;;      (Inr rw -> 
;;      [case (Des crht ww)
;;        (DummyL -> 
;;        Inr((Rec algread algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;            rw
;;            ([s,w1]Put s(InL w1))
;;            ([rw0,rq,rw1,rq0,rw2]Get rq rq0)))
;;        (Inr rw0 -> 
;;        Inr((Rec algread algwrite=>algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;            rw
;;            ([s,w1,w2]Put s(InR(w1 pair w2)))
;;            ([rw1,fwrq,rw2,fwrq0,rw3,fwrq1,w1]
;;              [case (Des w1)
;;                (DummyL -> Get(fwrq w1)(fwrq0 w1)(fwrq1 w1))
;;                (Inr rw4 -> 
;;                (Rec algread algwrite=>algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;                rw4
;;                ([s,w2,w3]
;;                  [case s (SdR -> fwrq1 w2) (SdM -> fwrq0 w2) (SdL -> fwrq w2)])
;;                ([rw5,fwrq2,rw6,fwrq3,rw7,fwrq4,w2]
;;                  Get(fwrq2(cCoWriteIn SdL w2))(fwrq3(cCoWriteIn SdM w2))
;;                  (fwrq4(cCoWriteIn SdR w2)))
;;                w1)])
;;            crht ww))])])

(animate "CoWriteIn")

(define neterm-cmp (rename-variables (nt eterm-cmp)))
(pp neterm-cmp)
;; 100 lines

(deanimate "CoWriteIn")

;; 5. Definite integration of a type-0 ucf
;; =======================================

;; 1/2 * (Integral f), which is in [-1,1]
(add-program-constant "HInt" (py "xi=>r"))
(add-program-constant "H" (py "r=>r"))
(add-program-constant "P" (py "r=>r=>r"))

(add-global-assumption
 "AxHIntInI"
 "all f^ (Elem r)((HInt xi r)f^)0 Zero")

(add-global-assumption
 "AxHIntOutMod"
 "all f^,s((HInt xi r)f^ eqd((Av r)((HInt xi r)((Outf xi)s f^))s))")

(add-global-assumption
 "AxElemAv"
 "all x^,a,s,n((Elem r)x^ a n ->
  (Elem r)((Av r)x^ s)((1#2)*(a+SdToInt s))(Succ n))")

(add-global-assumption
 "AxHIntIn"
 "all f^((HInt xi r)f^ eqd
         (H r)((P r)((HInt xi r)((fIn xi)SdL f^))
                    ((HInt xi r)((fIn xi)SdR f^))))")

(add-global-assumption
 "AxAvrg"
 "all x^1,x^2,a1,a2,n((Elem r)x^1 a1 n -> (Elem r)x^2 a2 n ->
                      (Elem r)((H r)((P r)x^1 x^2))((1#2)*(a1+a2)) n)")

(add-global-assumption
 "AxHIntIdF"
 "(HInt xi r)(IdF xi)eqd(Z r)")

(add-global-assumption
 "AxZ"
 "all n (Elem r)(Z r)(0#1)n")

;; PropInt
;; CoWrite f -> all n ex p (Int f) in I p n
(set-goal "allnc f^(CoWrite f^ -> all n exl a((Elem r)((HInt xi r)f^)a n))")
(cut "all n allnc f^(CoWrite f^ -> exl a((Elem r)((HInt xi r)f^)a n))")
 (assume "H0" "f^" "CoWf" "n")
 (use "H0")
 (use "CoWf")
(ind)
;; Base case
(assume "f^" "CoWf")
(intro 0 (pt "0#1"))
(use "AxHIntInI")
;; Step case
(assume "n" "IH" "f^" "CoWf")
(inst-with-to "CoWriteClause" (pt "f^") "CoWf" "Hcase")
(elim "Hcase")
;; Left case
(assume "f=IdF")
(simp "f=IdF")
(intro 0 (pt "0#1"))
(simp "AxHIntIdF")
(use "AxZ")
;; Right case
(assume "HRead")
(by-assume "HRead" "f^0" "Hand")
(inst-with-to "Hand" 'left "Read f0")
(inst-with-to "Hand" 'right "f=f0")
(simp "f=f0")
(elim "Read f0")
;; Side base case
(assume "f^1" "s" "f1[I] sub I_s" "CoWrite Outf f1")
(inst-with-to "IH" (pt "(Outf xi)s f^1") "CoWrite Outf f1" "IHinst")
(elim "IHinst")
(assume "a" "H1")
(intro 0 (pt "(1#2)*(a+(SdToInt s))"))
(simp "AxHIntOutMod" (pt "s"))
(use "AxElemAv")
(use "H1")
;; Side step case
(assume "f^1" "ReadL" "IHL" "ReadM" "IHM" "ReadR" "IHR")
(by-assume "IHL" "a1" "HElem a1")
(by-assume "IHR" "a2" "HElem a2")
(intro 0 (pt "(1#2)*(a1+a2)"))
(simp "AxHIntIn")
(use "AxAvrg")
(use "HElem a1")
(use "HElem a2")
;; Proof finished.
;; (cp)
(save "PropInt")

(define eterm-int (proof-to-extracted-term))
(define neterm-int (rename-variables (nt eterm-int)))

(pp neterm-int)

;; [w,n]
;;  (Rec nat=>algwrite=>rat)n([w0]0)
;;  ([n0,(algwrite=>rat),w0]
;;    [if (Des w0)
;;      0
;;      ([rw]
;;       (Rec algread algwrite=>rat)rw
;;       ([s,w1](1#2)*((algwrite=>rat)w1+SdToInt s))
;;       ([rw0,a,rw1,a0,rw2,a1](1#2)*(a+a1)))])
;;  w

(ppc neterm-int)

;; [w,n]
;;  (Rec nat=>algwrite=>rat)n([w0]0)
;;  ([n0,(algwrite=>rat),w0]
;;    [case (Des w0)
;;      (DummyL -> 0)
;;      (Inr rw -> 
;;      (Rec algread algwrite=>rat)rw
;;      ([s,w1](1#2)*((algwrite=>rat)w1+SdToInt s))
;;      ([rw0,a,rw1,a0,rw2,a1](1#2)*(a+a1)))])
;;  w

;; 6. Experiments
;; ==============

;; For Haskell extraction: animate after defining neterm-a, so that
;; the extracted function calls the extracted functions from the
;; lemmas instead of inlining them.

(animate "PropInt")
(animate "PropCompose") ;uses cCoWriteIn
(animate "CoWriteIn")
(animate "PropApply") ;probably not needed
(animate "LemmaApply")
(animate "CoWriteToCont") ;uses cOutElimCor cStandardSplit
(animate "OutElimCor")
(animate "ContToCoWrite") ;uses cContToCoWriteAux
(animate "ContToCoWriteAux") ;uses cFind cId
;; (animate "Id") ;not needed for Haskell translation
(animate "FindSd") ;uses cStandardSplit
(animate "StandardSplit")
(animate "Lft")
(animate "Rht")

(add-program-constant "sqrt" (py "rat=>nat=>rat"))

(add-computation-rules
 "sqrt a Zero" "Succ Zero"
 "sqrt a(Succ n)" "(sqrt a n+a/sqrt a n)/2")

;; (pp (nt (pt "sqrt 2(PosToNat 3)")))

;; f1(x) = -x
(define f1 (pt "[n]Succ n pair([a]0-a)"))

;; f2(x) = sqrt(x+2) - 1
;; In this case, the uniform Cauchy modulus is M(n)=n+1.

(define f2 (pt "[n]n--1 pair([a]sqrt(a+2)(n+1)-1)"))

;; f3(x) = 2x^2 - 1
(define f3 (pt "[n]n+1 pair([a]2*a*a-1)"))

'(
(terms-to-haskell-program
 "~/temp/readwrite.hs"
 (list (list neterm-a "type1to0")
       (list neterm-b "type0to1")
       (list neterm-apply "application")
       (list neterm-cmp "composition")
       (list neterm-int "integration")
       (list f1 "f1")
       (list f2 "f2")
       (list f3 "f3")))
)

;; To run the Haskell program, copy into readwrite.hs the definitions
;; of takeIv nd the ones bolow for pretty-printing read-write machines

'(
{- takeIv -}
takeIv _ II = []
takeIv 0 (C d x) = []
takeIv n (C d x) = (show d) : (takeIv (n-1) x)

{- pretty-printing read-write machines -}

spc l = concat $ replicate l " "

ppW _ l Stop = "Stop"
ppW 0 l (Cont x) = "Stop"
ppW n l (Cont x) = "Cont " ++ (ppR n (l+5) x)
ppR n l (Put d x) = "Put " ++ (show d) ++ " " ++ (ppW (n-1) (l+6) x)
ppR n l (Get x y z) = concat ["Get ", ppR n (l+4) x, "\n", spc (l+4),
                              ppR n (l+4) y, "\n", spc (l+4),
                              ppR n (l+4) z]
pp n w = putStrLn (ppW n 0 w)
)

;; Then in a terminal type ghci readwrite.hs (to quit To quit type *Main> :q)

(deanimate "PropInt")
(deanimate "PropCompose") ;uses cCoWriteIn
(deanimate "CoWriteIn")
(deanimate "PropApply") ;probably not needed
(deanimate "LemmaApply")
(deanimate "CoWriteToCont") ;uses cOutElimCor cStandardSplit
(deanimate "OutElimCor")
(deanimate "ContToCoWrite") ;uses cContToCoWriteAux
(deanimate "ContToCoWriteAux") ;uses cFind cId
;; (animate "Id") ;not needed for Haskell translation
(deanimate "FindSd") ;uses cStandardSplit
(deanimate "StandardSplit")
(deanimate "Lft")
(deanimate "Rht")

;; 6.1 type-1 to type-0
;; ====================

;; Main> pp 1 (type1to0 f1)

;; Cont Get Get Get Put SdR Stop
;;                  Put SdR Stop
;;                  Put SdR Stop
;;              Get Put SdR Stop
;;                  Put SdR Stop
;;                  Put SdR Stop
;;              Get Put SdR Stop
;;                  Put SdR Stop
;;                  Put SdM Stop
;;          Get Get Put SdR Stop
;;                  Put SdR Stop
;;                  Put SdM Stop
;;              Get Put SdM Stop
;;                  Put SdM Stop
;;                  Put SdM Stop
;;              Get Put SdM Stop
;;                  Put SdM Stop
;;                  Put SdL Stop
;;          Get Get Put SdM Stop
;;                  Put SdM Stop
;;                  Put SdL Stop
;;              Get Put SdL Stop
;;                  Put SdL Stop
;;                  Put SdL Stop
;;              Get Put SdL Stop
;;                  Put SdL Stop
;;                  Put SdL Stop

;; 6.2 Application
;; ===============

;; Main> takeIv 10 (application (type1to0 f1) (C SdL(C SdL(C SdL(C SdL II)))))

;; ["SdR","SdR","SdR","SdR","SdM","SdM","SdM","SdM","SdM","SdM"]

;; 6.3 Composition
;; ===============

;; Main> takeIv 10 $ application (composition (type1to0 f1) (type1to0 f3)) (C SdM(C SdM(C SdM(C SdM II))))

;; ["SdL","SdL","SdL","SdL","SdL","SdL","SdL","SdL","SdL","SdL"]

;; 6.4 Definite integration
;; ========================

;; Main> integration (type1to0 f2) 4

;; 817 % 2048

;; Main> integration (composition (type1to0 f3) (type1to0 f1)) 1

;; (-1) % 32

;; Main> integration (type1to0 f3) 3

;; (-2549) % 8192 {- result -}

;; Main> integration (type1to0 f3) 4

;; (-683003) % 2097152

;; 6.5 Some experiments in Minlog
;; ==============================

(animate "PropInt")
(animate "PropCompose") ;uses cCoWriteIn
(animate "CoWriteIn")
(animate "PropApply") ;probably not needed
(animate "LemmaApply")
(animate "CoWriteToCont") ;uses cOutElimCor cStandardSpli
(animate "OutElimCor")
(animate "ContToCoWrite") ;uses cContToCoWriteAux
(animate "ContToCoWriteAux") ;uses cFind cId
(animate "Id")
(animate "FindSd") ;uses cStandardSpli
(animate "StandardSplit")
(animate "Lft")
(animate "Rht")

(pp (nt (undelay-delayed-corec (mk-term-in-app-form neterm-a f1) 1)))

;; Cont
;; ((Get algwrite)
;;  ((Get algwrite)
;;   ((Get algwrite)
;;    ((Put algwrite)SdR
;;     ((CoRec (nat=>nat yprod(rat=>rat))=>algwrite) ...

(define minusone
  (pt "C SdL(C SdL(C SdL(C SdL(C SdL(C SdL(C SdL(C SdL II)))))))"))

(define app-flip-minusone
  (undelay-delayed-corec
   (mk-term-in-app-form
    neterm-apply (make-term-in-app-form neterm-a f1) minusone)
   2))

(pp (nt app-flip-minusone))

;; C SdR
;; (C SdR
;;  ((CoRec algwrite yprod iv=>iv)
;;   ((CoRec (nat=>nat yprod(rat=>rat))=>algwrite) ...

(pp (nt (mk-term-in-app-form
	 neterm-int
	 (pt "Cont((Get algwrite)
                      ((Put algwrite) SdR Stop)
                      ((Put algwrite) SdR Stop)
                      ((Put algwrite) SdR Stop))")
	 (pt "Succ Zero"))))

;; 1#2

(pp (nt
     (undelay-delayed-corec
      (mk-term-in-app-form
       neterm-int
       (undelay-delayed-corec (make-term-in-app-form neterm-a f2) 2)
       (pt "PosToNat 2"))
      1)))

;; 3#8

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2014-10-11 examples/analysis/readwrite.scm.  Abstract treatment of
;; uniformly continuous real functions.  Based on Kenji Miyamoto's thesis.

;; Log text

;; B n m f written explicitly as all a ex b sub f a n b m.  Variable
;; names made compatible with numbers.scm.  AxUcfInputSucc and AxUcfId
;; replaced by the more general AxUcfWeak.

;; End of log text

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "numbers.scm")
(libload "simpreal.scm")
(libload "real.scm")
(set! COMMENT-FLAG #t)

;; Contents
;; 1. A type-1 uniformly continuous function to a type-0 ucf
;; 2. A type-0 ucf to a type-1 ucf
;; 3. Applying a type-0 ucf to a type-0 real number
;; 4. Composing ucfs
;; 5. Definite integration of a type-0 ucf
;; 6. Experiments

;; 1. A type-1 uniformly continuous function to a type-0 ucf
;; =========================================================

(add-tvar-name "xi") ;type of uniformly continuous functions
(add-var-name "f" (py "xi"))
(add-pvar-name "X" (make-arity (py "xi")))

(add-alg "sd" '("Lft" "sd") '("Mid" "sd") '("Rht" "sd"))
(add-totality "sd")

(add-program-constant "SDToInt" (py "sd=>int"))

(add-computation-rules
 "SDToInt Lft" "IntN 1"
 "SDToInt Mid" "IntZero"
 "SDToInt Rht" "IntP 1")

(set-goal (rename-variables (term-to-totality-formula (pt "SDToInt"))))
(assume "sd^" "Td")
(elim "Td")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosOne")
(ng #t)
(use "TotalIntIntZero")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
; Proof finished.
(save "SDToIntTotal")

(add-program-constant "Out" (py "sd=>xi=>xi")) ;Out sd f means (Out_sd \circ f)
(add-program-constant "In" (py "sd=>xi=>xi")) ;In sd f means (f \circ In_sd)

;; sub f a m b n means f[I_{a,m}] \subseteq I_{b,n}
(add-program-constant "Sub" (py "xi=>rat=>nat=>rat=>nat=>boole"))

(add-program-constant "IdF" (py "xi"))

(add-global-assumption
 "AxOutIntro"
 "all f^,sd,a,m,b,n(
 (Sub xi)f^ 0 Zero(SDToInt sd#2)(Succ Zero) ->
 (Sub xi)f^ a m b(Succ n) -> (Sub xi)((Out xi)sd f^)a m(2*b-SDToInt sd)n)")

(add-global-assumption
 "AxOutElim"
 "all f^,sd,a,m,b,n(
  (Sub xi)f^ 0 Zero(SDToInt sd#2)(Succ Zero) ->
  (Sub xi)((Out xi)sd f^)a m b n -> (Sub xi)f^ a m((b+SDToInt sd)/2)(Succ n))")

(add-global-assumption
 "AxInIntro"
 "all f^,sd,a,m,b,n(
 (Sub xi)f^((a+SDToInt sd)/2)(Succ m)b n -> (Sub xi)((In xi)sd f^)a m b n)")

(add-global-assumption
 "AxInElim"
 "all f^,sd,a,m,b,n(
 (Sub xi)((In xi)sd f^)(2*a-SDToInt sd)m b n -> (Sub xi)f^ a(Succ m)b n)")
;; (remove-global-assumption "AxInElim")

;; (add-global-assumption
;;  "AxUcfWeak"
;;  "all f^,a,m,b,n((Sub xi)f^ a m b n -> (Sub xi)f^ a(Succ m)b n)")

(add-global-assumption
 "AxUcfWeak"
 "all f^,a,m1,m2,b,n(m1<=m2 -> (Sub xi)f^ a m1 b n -> (Sub xi)f^ a m2 b n)")

(add-global-assumption
 "AxUcfBound"
 "allnc f^ all a,m(Sub xi)f^ a m 0 Zero")

(add-global-assumption
 "AxUcfIdF"
 "all a,m(Sub xi)(IdF xi)a m a m")

(add-global-assumption
 "AxUcfLft"
 "all f^,b((Sub xi)f^ 0 Zero b(Succ(Succ Zero)) -> b<(IntN 1#4) ->
 (Sub xi)f^ 0 Zero(IntN 1#2)(Succ Zero))")

(add-global-assumption
 "AxUcfMid"
 "all f^,b((Sub xi)f^ 0 Zero b(Succ(Succ Zero)) -> (IntN 1#4)<=b -> b<(1#4) ->
 (Sub xi)f^ 0 Zero(0#2)(Succ Zero))")

(add-global-assumption
 "AxUcfRht"
 "all f^,b((Sub xi)f^ 0 Zero b(Succ(Succ Zero)) -> (1#4)<=b ->
 (Sub xi)f^ 0 Zero(1#2)(Succ Zero))")

;; To enable normalization it is better to work with / rather than #

;; Standard Split
(set-goal "all a(a<IntN 1/4 orr IntN 1/4<=a & a<1/4 oru 1/4<=a)")
(cases)
(cases)
(assume "p" "q")
(ng #t)
(intro 1)
(cases (pt "SZero(SZero p)<q"))
(assume "4p<q")
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4p<q -> F")
(intro 1)
(use "PosNotLtToLe")
(use "4p<q -> F")
;; 4
(assume "p")
(ng #t)
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
;; 5
(assume "p" "q")
(ng #t)
(cases (pt "SZero(SZero p)<=q"))
(assume "4p<=q")
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4p<=q -> F")
(intro 0)
(use "PosNotLeToLt")
(use "4p<=q -> F")
;; Proof finished.
(save "StandardSplit")

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "StandardSplit")))))

;; [a]
;;  [case a
;;    (k#p ->
;;    [case k
;;      (p0 -> Inr(SZero(SZero p0)<p))
;;      (0 -> Inr True)
;;      (IntN p0 ->
;;      [case (SZero(SZero p0)<=p)
;;        (True -> Inr True)
;;        (False -> (DummyL boole))])])]

;; FindSd
;; L5: f[I] sub I_{b,2} -> ex d f[I] sub I_d
(set-goal
 "allnc f^ all b((Sub xi)f^ 0 Zero b(Succ(Succ Zero)) ->
  ex sd (Sub xi)f^ 0 Zero(SDToInt sd#2)(Succ Zero))")
(assume "f^" "b" "f[I] sub I_{b,2}")
(inst-with-to "StandardSplit" (pt "b") "StandardSplitInst")
(elim "StandardSplitInst")
(drop "StandardSplitInst")
(assume "b<-1/4")
(ex-intro (pt "Lft"))
(use "AxUcfLft" (pt "b"))
(use "f[I] sub I_{b,2}")
(use "b<-1/4")
(assume "MidOrRht")
(elim "MidOrRht")
(drop "MidOrRht")
(assume "(IntN 1/4)<=b & b<1/4") ;Middle
(ex-intro (pt "Mid"))
(use "AxUcfMid" (pt "b"))
(use "f[I] sub I_{b,2}")
(use "(IntN 1/4)<=b & b<1/4")
(use "(IntN 1/4)<=b & b<1/4")
(assume "1/4<=b")
(ex-intro (pt "Rht"))
(use "AxUcfRht" (pt "b"))
(use "f[I] sub I_{b,2}")
(use "1/4<=b")
;; Proof finished.
(save "FindSd")

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "FindSd")))))

;; [a]
;;  [case (cStandardSplit a)
;;    ((DummyL boole) -> Lft)
;;    (Inr boole -> [case boole (True -> Mid) (False -> Rht)])]

(animate "StandardSplit")

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "FindSd")))))

;; [a]
;;  [case a
;;    (k#p ->
;;    [case k
;;      (p0 -> [case (SZero(SZero p0)<p) (True -> Mid) (False -> Rht)])
;;      (0 -> Mid)
;;      (IntN p0 -> [case (SZero(SZero p0)<=p) (True -> Mid) (False -> Lft)])])]

(deanimate "StandardSplit")

(add-algs "algread"
	  '("sd=>alpha=>algread" "Put")
	  '("algread=>algread=>algread=>algread" "Get"))

(add-ids
 (list (list "Read" (make-arity (py "xi")) "algread"))
 '("allnc f^ all sd(
   (Sub xi)f^ 0 Zero(SDToInt sd#2)(Succ Zero) -> X((Out xi)sd f^) -> Read f^)"
   "InitRead")
 '("allnc f^(
    Read((In xi)Lft f^) -> Read((In xi)Mid f^) -> Read((In xi)Rht f^) ->
    Read f^)"
   "GenRead"))

(add-algs "algwrite"
	  '("algwrite" "Stop")
	  '("algread algwrite=>algwrite" "Cont"))

(add-ids
 (list (list "Write" (make-arity (py "xi")) "algwrite"))
 '("Write(IdF xi)" "InitWrite")
 '("allnc f^((Read(cterm (f^) Write f^))f^ -> Write f^)" "GenWrite"))

(add-co "Write")

;; We now aim at ContToCoWrite: C f -> CoWrite f.  This will
;; essentially depend on an auxiliary lemma ContToCoWriteAux proved by
;; induction: all m(B m 2 f -> C f -> Read(CoWrite or C)f)

;; ContToCoWriteAux
;; Lemma 6
;; all m(B m 2 f -> C f -> Read(CoWrite or C)f)
(set-goal "all m allnc f^(
 all a ex b (Sub xi)f^ a m b(Succ(Succ Zero)) ->
 all n ex m all a ex b (Sub xi)f^ a m b n ->
 (Read(cterm (f^) CoWrite f^ ord all n ex m all a ex b (Sub xi)f^ a m b n))f^)")
(ind)
;; Base case m=0
(assume "f^" "B02f" "Cf")
(inst-with-to "B02f" (pt "IntZero#1") "B02fInst")
(by-assume "B02fInst" "b" "bProp")
(cut "ex sd (Sub xi)f^ 0 Zero(SDToInt sd#2)(Succ Zero)")
;; (use "Id") ;slow.  Use use-with instead:
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "sd" "sdProp")
;; (use "InitRead" (pt "sd"))
(use-with "InitRead"
	  (make-cterm
	   (pv "f^")
	   (pf "CoWrite f^ ord all n ex m all a ex b (Sub xi)f^ a m b n"))
	   (pt "f^") (pt "sd") "?" "?")
(use "sdProp")
(intro 1)
(assume "n")
(inst-with-to "Cf" (pt "n+1") "CfInst")
(by-assume "CfInst" "m" "mProp")
(ex-intro (pt "m"))
(assume "a")
(inst-with-to "mProp" (pt "a") "mPropInst")
(by-assume "mPropInst" "b1" "b1Prop")
(ex-intro (pt "2*b1-SDToInt sd"))
(use "AxOutIntro")
(use "sdProp")
(use "b1Prop")
(use "FindSd" (pt "b"))
(use "bProp")
;; 3 Step case
(assume "m" "IH" "f^" "B(m+1)2" "Cf")
;; (use "GenRead")
(use-with "GenRead"
	  (make-cterm
	   (pv "f^")
	   (pf "CoWrite f^ ord all n ex m all a ex b (Sub xi)f^ a m b n"))
	  (pt "f^") "?" "?" "?") ;38-40
(use "IH") ;here we need f^ since In is not total.
(drop "IH")
(assume "a")
(inst-with-to "B(m+1)2" (pt "(a+SDToInt Lft)/2") "B(m+1)2Inst")
(by-assume "B(m+1)2Inst" "b" "bProp")
(ex-intro (pt "b"))
(use "AxInIntro")
(use "bProp")
(drop "IH")
(assume "n")
(inst-with-to "Cf" (pt "n") "CfInst")
(by-assume "CfInst" "m1" "m1Prop")
(ex-intro (pt "m1"))
(assume "a")
(inst-with-to "m1Prop" (pt "(a+SDToInt Lft)/2") "m1PropInst")
(by-assume "m1PropInst" "b" "bProp")
(ex-intro (pt "b"))
(use "AxInIntro")
(use "AxUcfWeak" (pt "m1"))
(use "Truth")
(use "bProp")
;; 39
(use "IH")
(drop "IH")
(assume "a")
(inst-with-to "B(m+1)2" (pt "(a+SDToInt Mid)/2") "B(m+1)2Inst")
(by-assume "B(m+1)2Inst" "b" "bProp")
(ex-intro (pt "b"))
(use "AxInIntro")
(use "bProp")
(drop "IH")
(assume "n")
(inst-with-to "Cf" (pt "n") "CfInst")
(by-assume "CfInst" "m1" "m1Prop")
(ex-intro (pt "m1"))
(assume "a")
(inst-with-to "m1Prop" (pt "(a+SDToInt Mid)/2") "m1PropInst")
(by-assume "m1PropInst" "b" "bProp")
(ex-intro (pt "b"))
(use "AxInIntro")
(use "AxUcfWeak" (pt "m1"))
(use "Truth")
(use "bProp")
;; 40
(use "IH")
(drop "IH")
(assume "a")
(inst-with-to "B(m+1)2" (pt "(a+SDToInt Rht)/2") "B(m+1)2Inst")
(by-assume "B(m+1)2Inst" "b" "bProp")
(ex-intro (pt "b"))
(use "AxInIntro")
(use "bProp")
(drop "IH")
(assume "n")
(inst-with-to "Cf" (pt "n") "CfInst")
(by-assume "CfInst" "m1" "m1Prop")
(ex-intro (pt "m1"))
(assume "a")
(inst-with-to "m1Prop" (pt "(a+SDToInt Rht)/2") "m1PropInst")
(by-assume "m1PropInst" "b" "bProp")
(ex-intro (pt "b"))
(use "AxInIntro")
(use "AxUcfWeak" (pt "m1"))
(use "Truth")
(use "bProp")
;; Proof finished.
(save "ContToCoWriteAux")

;; ContToCoWrite
;; C f -> CoWrite f
(set-goal "allnc f^(all n ex m all a ex b (Sub xi)f^ a m b n -> CoWrite f^)")
(assume "f^" "Cf")
(coind "Cf")
(assume "f^1" "Cf1")
(intro 1)
(intro 0 (pt "f^1"))
(split)
(inst-with-to "Cf1" (pt "Succ(Succ Zero)") "Cf1Inst")
(by-assume "Cf1Inst" "m" "mProp")
(use "ContToCoWriteAux" (pt "m"))
(use "mProp")
(use "Cf1")
(use "InitEqD")
;; Proof finished.
(save "ContToCoWrite")

(define eterm-a
  (proof-to-extracted-term (theorem-name-to-proof "ContToCoWrite")))

(add-var-name "oh" (py "nat=>nat@@(rat=>rat)")) ;o for the modulus omega
;; (remove-var-name "oh")

(define neterm-a (nt eterm-a))

(pp (rename-variables neterm-a))

;; [oh]
;;  (CoRec (nat=>nat@@(rat=>rat))=>algwrite)oh
;;  ([oh0]
;;    Inr(cContToCoWriteAux left(oh0(Succ(Succ Zero)))
;;        right(oh0(Succ(Succ Zero)))
;;        oh0))

(animate "ContToCoWriteAux")

;; st for step
(add-var-name
 "st" (py "(rat=>rat)=>(nat=>nat@@(rat=>rat))=>
           algread(algwrite ysum(nat=>nat@@(rat=>rat)))"))
(add-var-name "g" (py "rat=>rat"))

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "ContToCoWrite")))))

;; [oh]
;;  (CoRec (nat=>nat@@(rat=>rat))=>algwrite)oh
;;  ([oh0]
;;    Inr((Rec nat=>(rat=>rat)=>(nat=>nat@@(rat=>rat))=>algread(algwrite ysum(nat=>nat@@(rat=>rat))))
;;        left(oh0(Succ(Succ Zero)))
;;        ([g,oh1]
;;          [let sd
;;            (cFindSd(g 0))
;;            ((Put algwrite ysum(nat=>nat@@(rat=>rat)))sd
;;            ((InR nat=>nat@@(rat=>rat) algwrite)
;;             ([n]left(oh1(Succ n))@([a]2*right(oh1(Succ n))a-SDToInt sd))))])
;;        ([n,st,g,oh1]
;;          (Get algwrite ysum(nat=>nat@@(rat=>rat)))
;;          (st([a]g((a+IntN 1)/2))
;;           ([n0]left(oh1 n0)@([a]right(oh1 n0)((a+IntN 1)/2))))
;;          (st([a]g(a/2))([n0]left(oh1 n0)@([a]right(oh1 n0)(a/2))))
;;          (st([a]g((a+1)/2))([n0]left(oh1 n0)@([a]right(oh1 n0)((a+1)/2)))))
;;        right(oh0(Succ(Succ Zero)))
;;        oh0))

;; Note that let sd ... avoids a double occurrence of cFindSd(g 0)

(animate "FindSd")
(animate "StandardSplit")

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "ContToCoWrite")))))

;; [oh]
;;  (CoRec (nat=>nat@@(rat=>rat))=>algwrite)oh
;;  ([oh0]
;;    Inr((Rec nat=>(rat=>rat)=>(nat=>nat@@(rat=>rat))=>algread(algwrite ysum(nat=>nat@@(rat=>rat))))
;;        left(oh0(Succ(Succ Zero)))
;;        ([g,oh1]
;;          [let sd
;;            [case (g 0)
;;             (k#p ->
;;             [case k
;;               (p0 -> [case (SZero(SZero p0)<p) (True -> Mid) (False -> Rht)])
;;               (0 -> Mid)
;;               (IntN p0 ->
;;               [case (SZero(SZero p0)<=p) (True -> Mid) (False -> Lft)])])]
;;            ((Put algwrite ysum(nat=>nat@@(rat=>rat)))sd
;;            ((InR nat=>nat@@(rat=>rat) algwrite)
;;             ([n]left(oh1(Succ n))@([a]2*right(oh1(Succ n))a-SDToInt sd))))])
;;        ([n,st,g,oh1]
;;          (Get algwrite ysum(nat=>nat@@(rat=>rat)))
;;          (st([a]g((a+IntN 1)/2))
;;           ([n0]left(oh1 n0)@([a]right(oh1 n0)((a+IntN 1)/2))))
;;          (st([a]g(a/2))([n0]left(oh1 n0)@([a]right(oh1 n0)(a/2))))
;;          (st([a]g((a+1)/2))([n0]left(oh1 n0)@([a]right(oh1 n0)((a+1)/2)))))
;;        right(oh0(Succ(Succ Zero)))
;;        oh0))

(deanimate "ContToCoWriteAux")
(deanimate "FindSd")
(deanimate "StandardSplit")

;; 2. A type-0 ucf to a type-1 ucf
;; ===============================

;; We now aim at the converse, CoWriteToCon

;; LemmaNine
;; OutElimCor
(set-goal "allnc f^ all sd,m,n(
 (Sub xi)f^ 0 Zero(SDToInt sd#2)(Succ Zero) ->
 all a ex b (Sub xi)((Out xi)sd f^)a m b n ->
 all a ex b (Sub xi)f^ a m b(Succ n))")
(assume "f^" "sd" "m" "n" "f[I]subId" "BOut" "a")
(inst-with-to "BOut" (pt "a") "BOutInst")
(by-assume "BOutInst" "b" "bProp")
(ex-intro (pt "(b+SDToInt sd)/2"))
(use "AxOutElim")
(use "f[I]subId")
(use "bProp")
;; Proof finished.
(save "OutElimCor")

;; CoWriteToCon
(set-goal "allnc f^(CoWrite f^ -> all n ex m all a ex b (Sub xi)f^ a m b n)")
(cut "all n allnc f^(CoWrite f^ -> ex m all a ex b (Sub xi)f^ a m b n)")
 (assume "CutHyp" "f^" "CoWf" "n")
 (use "CutHyp")
 (use "CoWf")
(ind)
;; Base n=0
(assume "f^" "CoWf")
(ex-intro (pt "Zero"))
(assume "a")
(ex-intro (pt "0#1"))
(use "AxUcfBound")
;; Step n -> n+1
(assume "n" "IH" "f^" "CoWf")
(inst-with-to "CoWriteClause" (pt "f^") "CoWf" "ClauseHyp")
(elim "ClauseHyp")
;; Case IdF
(assume "f=IdF")
(ex-intro (pt "Succ n"))
(assume "a")
(ex-intro (pt "a"))
(simp "f=IdF")
(use "AxUcfIdF")
;; Case Read
(assume "ExHyp")
(by-assume "ExHyp" "f^0" "Conj")
(elim "Conj")
(assume "Readf0" "f=f0")
(simp "f=f0")
(elim "Readf0")
;; Side induction base
;; ?_29:allnc f^
;;       all sd(
;;        (Sub xi)f^ 0 Zero(SDToInt sd#2)(Succ Zero) ->
;;        CoWrite((Out xi)sd f^) -> ex m all a ex b (Sub xi)f^ a m b(Succ n))
(assume "f^1" "sd" "SubHyp" "CoWHyp")
(inst-with-to "IH" (pt "(Out xi)sd f^1") "CoWHyp" "IHInst")
(by-assume "IHInst" "m" "mProp")
(ex-intro (pt "m"))
(use "OutElimCor" (pt "sd"))
(use "SubHyp")
(use "mProp")
;; Side induction step
;; ?_30:allnc f^(
;;       (Read (cterm (f^0) CoWrite f^0))((In xi)Lft f^) ->
;;       ex m all a ex b (Sub xi)((In xi)Lft f^)a m b(Succ n) ->
;;       (Read (cterm (f^0) CoWrite f^0))((In xi)Mid f^) ->
;;       ex m all a ex b (Sub xi)((In xi)Mid f^)a m b(Succ n) ->
;;       (Read (cterm (f^0) CoWrite f^0))((In xi)Rht f^) ->
;;       ex m all a ex b (Sub xi)((In xi)Rht f^)a m b(Succ n) ->
;;       ex m all a ex b (Sub xi)f^ a m b(Succ n))
(assume "f^1" "HReadL" "IHL" "HReadM" "IHM" "HReadR" "IHR")
(by-assume "IHL" "m0" "m0Prop")
(by-assume "IHM" "m1" "m1Prop")
(by-assume "IHR" "m2" "m2Prop")
(ex-intro (pt "Succ(m0 max m1 max m2)"))
(assume "a")
(inst-with-to "StandardSplit" (pt "a") "StandardSplitInst")
(elim "StandardSplitInst")
(assume "a<-1#4")
(inst-with-to "m0Prop" (pt "(2*a-SDToInt Lft)") "m0PropInst")
(by-assume "m0PropInst" "b" "bProp")
(ex-intro (pt "b"))
(assert "(Sub xi)f^1 a(Succ m0)b(Succ n)")
 (use "AxInElim" (pt "Lft"))
 (use "bProp")
(assume "(Sub xi)f^1 a(Succ m0)b(Succ n)")
(use "AxUcfWeak" (pt "Succ m0"))
(ng #t)
(use "NatLeTrans" (pt "m0 max m1"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "(Sub xi)f^1 a(Succ m0)b(Succ n)")
;; 55
(assume "MidOrRight")
(elim "MidOrRight")
(assume "(IntN 1#4)<=a & a<(1#4)")
(inst-with-to "m1Prop" (pt "(2*a-SDToInt Mid)") "m1PropInst")
(by-assume "m1PropInst" "b" "bProp")
(ex-intro (pt "b"))
(assert "(Sub xi)f^1 a(Succ m1)b(Succ n)")
 (use "AxInElim" (pt "Mid"))
 (use "bProp")
(assume "(Sub xi)f^1 a(Succ m1)b(Succ n)")
(use "AxUcfWeak" (pt "Succ m1"))
(ng #t)
(use "NatLeTrans" (pt "m0 max m1"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "(Sub xi)f^1 a(Succ m1)b(Succ n)")
;; 74
(assume "(1#4)<=a")
(inst-with-to "m2Prop" (pt "(2*a-SDToInt Rht)") "m2PropInst")
(by-assume "m2PropInst" "b" "bProp")
(ex-intro (pt "b"))
(assert "(Sub xi)f^1 a(Succ m2)b(Succ n)")
 (use "AxInElim" (pt "Rht"))
 (use "bProp")
(assume "(Sub xi)f^1 a(Succ m2)b(Succ n)")
(use "AxUcfWeak" (pt "Succ m2"))
(ng #t)
(use "NatMaxUB2")
(use "(Sub xi)f^1 a(Succ m2)b(Succ n)")
;; Proof finished.
(save "CoWriteToCont")

(add-var-name "mg" (py "nat@@(rat=>rat)"))
(add-var-name "mgs" (py "algwrite=>nat@@(rat=>rat)"))
(add-var-name "rw" (py "algread algwrite"))
(add-var-name "w" (py "algwrite"))

(define eterm-b
  (proof-to-extracted-term (theorem-name-to-proof "CoWriteToCont")))
(define neterm-b (rename-variables (nt eterm-b)))
(ppc neterm-b)

;; [w,n]
;;  (Rec nat=>algwrite=>nat@@(rat=>rat))n([w0]Zero@([a]0))
;;  ([n0,mgs,w0]
;;    [case (Des w0)
;;      ((DummyL algread algwrite) -> Succ n0@([a]a))
;;      (Inr rw ->
;;      (Rec algread algwrite=>nat@@(rat=>rat))rw
;;      ([sd,w1]left(mgs w1)@cOutElimCor sd left(mgs w1)n0 right(mgs w1))
;;      ([rw0,mg,rw1,mg0,rw2,mg1]
;;        Succ(left mg max left mg0 max left mg1)@
;;        ([a]
;;          [case (cStandardSplit a)
;;            ((DummyL boole) -> right mg(2*a-IntN 1))
;;            (Inr boole ->
;;            [case boole
;; 	     (True -> right mg0(2*a))
;; 	     (False -> right mg1(2*a-1))])])))])
;;  w

(animate "OutElimCor")
(animate "StandardSplit")

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "CoWriteToCont")))))

;; [w,n]
;;  (Rec nat=>algwrite=>nat@@(rat=>rat))n([w0]Zero@([a]0))
;;  ([n0,mgs,w0]
;;    [case (Des w0)
;;      ((DummyL algread algwrite) -> Succ n0@([a]a))
;;      (Inr rw ->
;;      (Rec algread algwrite=>nat@@(rat=>rat))rw
;;      ([sd,w1]left(mgs w1)@([a](right(mgs w1)a+SDToInt sd)/2))
;;      ([rw0,mg,rw1,mg0,rw2,mg1]
;;        Succ(left mg max left mg0 max left mg1)@
;;        ([a]
;;          [case a
;;            (k#p ->
;;            [case k
;;              (p0 ->
;;              [case (SZero(SZero p0)<p)
;;                (True -> right mg0(2*a))
;;                (False -> right mg1(2*a-1))])
;;              (0 -> right mg0(2*a))
;;              (IntN p0 ->
;;              [case (SZero(SZero p0)<=p)
;;                (True -> right mg0(2*a))
;;                (False -> right mg(2*a-IntN 1))])])])))])
;;  w

(deanimate "OutElimCor")
(deanimate "StandardSplit")

;; 3. Applying a type-0 ucf to a type-0 real number
;; ================================================

;; This section is related to examples/analysis/average.scm.  There we
;; axiomatized (by somewhat ad hoc rewrite rules) the constants IntToR
;; P (plus) and H (half).  Here we use axioms for Z (zero) Av
;; (average) Va (inverse of average) and Elem (x in I_{a,n}) instead.

(remove-var-name "x" "y" "z") ;will be used for abstract reals
(add-tvar-name "r") ;abstract real
(add-var-name "x" "y" "z" (py "r"))

(add-program-constant "Z" (py "r")) ;zero
(add-program-constant "Av" (py "r=>sd=>r")) ;average
(add-program-constant "Va" (py "r=>sd=>r")) ;inverse of average
(add-program-constant "Elem" (py "r=>rat=>nat=>boole"))

(add-algs "iv" '("II" "iv") '("C" "sd=>iv=>iv"))

;; We inductively define a set I of reals.

(add-ids (list (list "I" (make-arity (py "r")) "iv"))
	 '("I(Z r)" "InitI")
	 '("allnc x^ all sd(I x^ -> I((Av r)x^ sd))" "GenI"))

(add-co "I")

(add-program-constant "App" (py "xi=>r=>r"))

(add-global-assumption
 "AxAvVaId"
 "all x^,sd((Elem r)x^(SDToInt sd#2)(Succ Zero) ->
            x^ eqd(Av r)((Va r)x^ sd)sd)")

(add-global-assumption
 "AxVaAvId"
 "all x^,sd(x^ eqd(Va r)((Av r)x^ sd)sd)")

(add-global-assumption
 "AxAvZero"
 "(Av r)(Z r)Mid eqd (Z r)")

(add-global-assumption
 "AxAppId"
 "all x^((App xi r)(IdF xi)x^ eqd x^)")

(add-global-assumption
 "AxApohubElem"
 "all f^,x^,b,n((Sub xi)f^ 0 Zero b n -> (Elem r)((App xi r)f^ x^)b n)")

(add-global-assumption
 "AxVaOut"
 "all f^,x^,sd((Sub xi)f^ 0 Zero(SDToInt sd#2)(Succ Zero) ->
   (Va r)((App xi r)f^ x^)sd eqd(App xi r)((Out xi)sd f^)x^)")

(add-global-assumption
 "AxAvIn"
 "all f^,x^,sd((App xi r)f^((Av r)x^ sd)eqd(App xi r)((In xi)sd f^)x^)")

;; LemmaApply
(set-goal "allnc f^0(
     (Read (cterm (f^) CoWrite f^))f^0 ->
     allnc x^0(
      CoI x^0 ->
      (App xi r)f^0 x^0 eqd(Z r) orr
      exr y^
       ex sd(
        (CoI y^ ord
         exr f^1,x^1(y^ eqd(App xi r)f^1 x^1 & CoWrite f^1 & CoI x^1)) andl
        (App xi r)f^0 x^0 eqd(Av r)y^ sd)))")
(assume "f^0" "Read f0")
(elim "Read f0") ;3,4
(assume "f^1" "sd" "Cod f sub I_sd" "CoW(Out sd f)" "x^0" "CoI x0")
(intro 1)
(intro 0 (pt "(App xi r)((Out xi) sd f^1)x^0"))
(ex-intro (pt "sd"))
(split)
(intro 1)
(intro 0 (pt "(Out xi)sd f^1"))
(intro 0 (pt "x^0"))
(split)
(use "InitEqD")
(split)
(use "CoW(Out sd f)")
(use "CoI x0")
(simp "<-" "AxVaOut")
(simp "<-" "AxAvVaId")
(use "InitEqD")
(use "AxApohubElem")
(use "Cod f sub I_sd")
(use "Cod f sub I_sd")
;; 4
(assume "f^" "HypRL" "IHL" "HypRM" "IHM" "HypRR" "IHR" "x^0" "CoI x0")
(inst-with-to "CoIClause" (pt "x^0") "CoI x0" "HCases CoI x0")
(elim "HCases CoI x0")
;; Left case
(assume "x0=0")
(inst-with-to "IHM" (pt "x^0") "CoI x0" "IHMInst")
(assert "(App xi r)f^ x^0 eqd(App xi r)((In xi)Mid f^)x^0")
 (simp "x0=0")
 (simp "<-" "AxAvIn")
 (simp "AxAvZero")
 (use "InitEqD")
(assume "Heq")
(simp "Heq")
(use "IHMInst")
;; Right case
(assume "Hexex")
(elim "Hexex")
(assume "x^1" "Hex")
(by-assume "Hex" "sd1" "H0")
(inst-with-to "H0" 'left "CoI x1")
(cases (pt "sd1"))
;; Three subcases: L
(assume "CaseL")
(inst-with-to "IHL" (pt "x^1") "CoI x1" "IHLInst")
(elim "H0")
(assume "H0L" "H0R")
(simp "H0R" 'right)
(simp "CaseL")
(simp "AxAvIn")
(use "IHLInst")
;; Three subcases: M
(assume "CaseM")
(inst-with-to "IHM" (pt "x^1") "CoI x1" "IHMInst")
(elim "H0")
(assume "H0L" "H0R")
(simp "H0R" 'right)
(simp "CaseM")
(simp "AxAvIn")
(use "IHMInst")
;; Three subcases: R
(assume "CaseR")
(inst-with-to "IHR" (pt "x^1") "CoI x1" "IHRInst")
(elim "H0")
(assume "H0L" "H0R")
(simp "H0R" 'right)
(simp "CaseR")
(simp "AxAvIn")
(use "IHRInst")
;; Proof finished.
(save "LemmaApply")

(add-var-name "niv" (py "iv=>uysum(sd@@(iv ysum algwrite@@iv))"))

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "LemmaApply")))))

;; [rw]
;;  (Rec algread algwrite=>iv=>uysum(sd@@(iv ysum algwrite@@iv)))rw
;;  ([sd,w,iv0]Inr(sd@(InR algwrite@@iv iv)(w@iv0)))
;;  ([rw0,niv,rw1,niv0,rw2,niv1,iv]
;;    [case (Des iv)
;;      ((DummyL sd@@iv) -> niv0 iv)
;;      (Inr(sd@@iv)_0 ->
;;      [case (left(sd@@iv)_0)
;;        (Lft -> niv right(sd@@iv)_0)
;;        (Mid -> niv0 right(sd@@iv)_0)
;;        (Rht -> niv1 right(sd@@iv)_0)])])

;; PropApply
(set-goal "allnc f^,x^(CoWrite f^ -> CoI x^ -> CoI((App xi r)f^ x^))")
(assume "f^" "x^" "CoW f" "CoI x")
;; Preparing our competitor
(assert "exnci f^1,x^1((App xi r)f^ x^ eqd(App xi r)f^1 x^1 &
                        CoWrite f^1 & CoI x^1)")
 (intro 0 (pt "f^"))
 (intro 0 (pt "x^"))
 (split)
 (use "InitEqD")
 (split)
 (use "CoW f")
 (use "CoI x")
;; Assuming our competitor
(assume "Q z")
(coind "Q z")
(assume "z^0" "Q z0")
(elim "Q z0")
(assume "f^0" "Hex")
(elim "Hex")
(assume "x^0" "Hand")
(inst-with-to "Hand" 'right 'left "CoW f0")
(inst-with-to "Hand" 'right 'right "CoI x0")
(inst-with-to "CoWriteClause" (pt "f^0") "CoW f0" "HCases")
(elim "HCases") ;24,25
;; Case f0 = Id
(assume "f0 eqd Id")
(inst-with-to "CoIClause" (pt "x^0") "CoI x0" "HCases x0")
(elim "HCases x0")
(assume "x0=0")
(intro 0)
(simp "Hand")
(simp "f0 eqd Id")
(simp "x0=0")
(use "AxAppId")
(assume "Hexrex")
(intro 1)
(elim "Hexrex")
(assume "x^1" "Hex 2")
(intro 0 (pt "x^1"))
(by-assume "Hex 2" "sd" "Heqd")
(ex-intro (pt "sd"))
(split)
(intro 0)
(use "Heqd")
(simp "Hand")
(simp "f0 eqd Id")
(elim "Heqd")
(assume "HeqdL" "HeqdR")
(simp "HeqdR")
(use "AxAppId")
;; 25
;; ?_25:exr f^((Read (cterm (f^1) CoWrite f^1))f^ andl f^0 eqd f^) ->
;;      z^0 eqd(Z r) orr
;;      exr x^
;;       ex sd(
;;        (CoI x^ ord
;;        exr f^,x^0(x^ eqd(App xi r)f^ x^0 & CoWrite f^ & CoI x^0)) andl
;;        z^0 eqd(Av r)x^ sd)
(assume "HypRead")
(assert "(Read (cterm (f^1) CoWrite f^1))f^0")
 (elim "HypRead")
 (assume "f^1" "H1")
 (elim "H1")
 (assume "H1L" "H1R")
 (simp "H1R")
 (use "H1")
(assume "HRead")
(assert "(App xi r)f^0 x^0 eqd(Z r) orr
      exr x^
       ex sd(
        (CoI x^ ord
         exr f^,x^0(x^ eqd(App xi r)f^ x^0 & CoWrite f^ & CoI x^0)) andl
        (App xi r)f^0 x^0 eqd(Av r)x^ sd)")
 (use "LemmaApply")
 (use "HRead")
 (use "CoI x0")
(assume "H2")
(elim "H2")
(assume "Hleft")
(intro 0)
(simp "Hand")
(use "Hleft")
(assume "Hright")
(intro 1)
(simp "Hand")
(use "Hright")
;; Proof finished.
(save "PropApply")

(define eterm-apply
  (proof-to-extracted-term (theorem-name-to-proof "PropApply")))

(add-var-name "wiv" (py "algwrite@@iv"))
(add-var-name "div" (py "sd@@iv"))
;; (add-var-name "divpwiv" (py "sd@@(iv ysum algwrite@@iv)"))
(define neterm-apply (rename-variables (nt eterm-apply)))

(pp neterm-apply)

;; [w,iv]
;;  (CoRec algwrite@@iv=>iv)(w@iv)
;;  ([wiv]
;;    [if (Des left wiv)
;;      [if (Des right wiv)
;;       (DummyL sd@@(iv ysum algwrite@@iv))
;;       ([div]Inr(left div@(InL iv algwrite@@iv)right div))]
;;      ([rw]
;;       [if (cLemmaApply rw right wiv)
;;         (DummyL sd@@(iv ysum algwrite@@iv))
;;         (InrUysum sd@@(iv ysum algwrite@@iv))])])

(animate "LemmaApply")

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "PropApply")))))

;; [w,iv]
;;  (CoRec algwrite@@iv=>iv)(w@iv)
;;  ([wiv]
;;    [if (Des left wiv)
;;      [if (Des right wiv)
;;       (DummyL sd@@(iv ysum algwrite@@iv))
;;       ([div]Inr(left div@(InL iv algwrite@@iv)right div))]
;;      ([rw]
;;       [if ((Rec algread algwrite=>iv=>uysum(sd@@(iv ysum algwrite@@iv)))rw
;;             ([sd0,w0,iv1]Inr(sd0@(InR algwrite@@iv iv)(w0@iv1)))
;;             ([rw0,niv,rw1,niv0,rw2,niv1,iv0]
;;               [if (Des iv0)
;;                 (niv0 iv0)
;;                 ([div]
;;                  [if (left div)
;;                    (niv right div)
;;                    (niv0 right div)
;;                    (niv1 right div)])])
;;             right wiv)
;;         (DummyL sd@@(iv ysum algwrite@@iv))
;;         (InrUysum sd@@(iv ysum algwrite@@iv))])])

(deanimate "LemmaApply")

;; 4. Composing ucfs
;; =================

(add-global-assumption
 "AxIdIn"
 "all sd (Sub xi)((In xi)sd(IdF xi))0 Zero(SDToInt sd#2)(Succ Zero)")

(add-global-assumption
 "AxOutInId"
 "all sd (Out xi)sd((In xi)sd(IdF xi))eqd(IdF xi)")

(add-global-assumption
 "AxUcfIn"
 "all f^,b,n,sd((Sub xi)f^ 0 Zero b n -> (Sub xi)((In xi)sd f^)0 Zero b n)")

(add-global-assumption
 "AxUcfOutInInOut"
 "all f^,sd1,sd2(
  (Sub xi)f^ 0 Zero(SDToInt sd1#2)(Succ Zero) ->
  (Out xi)sd1((In xi)sd2 f^)eqd(In xi)sd2((Out xi)sd1 f^))")

;; CoWriteIn
(set-goal "allnc f^ all sd(CoWrite f^ -> CoWrite((In xi)sd f^))")
(assume "f^" "sd" "CoWf")
(assert "exr f^1(CoWrite f^1 andl (In xi)sd f^ eqd (In xi)sd f^1)")
 (intro 0 (pt "f^"))
 (split)
 (use "CoWf")
 (use "InitEqD")
(assume "Pf")
(coind "Pf")
(assume "f^1" "Pf1")
(by-assume "Pf1" "f^2" "Hyp1")
(inst-with-to "Hyp1" 'left "CoWf2")
(inst-with-to "Hyp1" 'right "Eq")
(simp "Eq")
(inst-with-to "CoWriteClause" (pt "f^2") "CoWf2" "Case f2")
(elim "Case f2")
;; lef
(assume "f2=Id")
(intro 1)
(simp "f2=Id")
(intro 0 (pt "(In xi)sd(IdF xi)"))
(split)
(intro 0 (pt "sd"))
(use "AxIdIn")
(simp "AxOutInId")
(intro 0)
(simp "<-" "f2=Id")
(use "CoWf2")
(use "InitEqD")
;; righ
(assume "Hyp2")
(by-assume "Hyp2" "f^3" "Read f3 and eq")
(intro 1)
(inst-with-to "Read f3 and eq" 'left "Read f3")
(intro 0 (pt "(In xi)sd f^2"))
(split)
(elim "Read f3 and eq")
(assume "Read f3 2" "Heq")
(simp "Heq")
(elim "Read f3")
(assume "f^4" "sd1" "f[I] sub I_sd1" "CoWrite out f")
(intro 0 (pt "sd1"))
(use "AxUcfIn")
(use "f[I] sub I_sd1")
(intro 1)
(intro 0 (pt "(Out xi)sd1 f^4"))
(split)
(use "CoWrite out f")
(use "AxUcfOutInInOut")
(use "f[I] sub I_sd1")
;; 48
(assume "f^4" "Read L" "IH L" "Read M" "IH M" "Read R" "IH R")
(cases (pt "sd")) ;59-61
(assume "Case L")
(elim "Read L")
(assume "f^5" "sd1" "f5[I] sub I_sd1" "CoWrite out f5")
(intro 0 (pt "sd1"))
(use "f5[I] sub I_sd1")
(intro 0)
(use "CoWrite out f5")
(assume "f^5" "Sub Read L" "Sub IH L" "Sub Read M"
	"Sub IH M" "Sub Read R" "Sub IH R")
(intro 1)
(use "Sub IH L")
(use "Sub IH M")
(use "Sub IH R")
;; 60
(assume "Case M")
(elim "Read M")
(assume "f^5" "sd1" "f5[I] sub I_sd1" "CoWrite out f5")
(intro 0 (pt "sd1"))
(use "f5[I] sub I_sd1")
(intro 0)
(use "CoWrite out f5")
(assume "f^5" "Sub Read L" "Sub IH L" "Sub Read M" "Sub IH M"
	"Sub Read R" "Sub IH R")
(intro 1)
(use "Sub IH L")
(use "Sub IH M")
(use "Sub IH R")
;; 61
(assume "Case R")
(elim "Read R")
(assume "f^5" "sd1" "f5[I] sub I_sd1" "CoWrite out f5")
(intro 0 (pt "sd1"))
(use "f5[I] sub I_sd1")
(intro 0)
(use "CoWrite out f5")
(assume "f^5" "Sub Read L" "Sub IH L" "Sub Read M" "Sub IH M"
	"Sub Read R" "Sub IH R")
(intro 1)
(use "Sub IH L")
(use "Sub IH M")
(use "Sub IH R")
;;
(use "InitEqD")
;; Proof finished.
(save "CoWriteIn") ;was Lemma 10

(add-var-name "rww" (py "algread(algwrite ysum algwrite)"))

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "CoWriteIn")))))

;; [sd,w]
;;  (CoRec algwrite=>algwrite)w
;;  ([w0]
;;    [if (Des w0)
;;      (Inr((Put algwrite ysum algwrite)sd((InL algwrite algwrite)w0)))
;;      ([rw]
;;       Inr((Rec algread algwrite=>algread(algwrite ysum algwrite))rw
;;           ([sd0,w1]
;;             (Put algwrite ysum algwrite)sd0((InR algwrite algwrite)w1))
;;           ([rw0,rww,rw1,rww0,rw2,rww1]
;;             [if sd
;;               ((Rec algread algwrite=>algread(algwrite ysum algwrite))rw0
;;               ([sd0,w1]
;;                 (Put algwrite ysum algwrite)sd0((InL algwrite algwrite)w1))
;;               ([rw3,rww2,rw4,rww3,rw5](Get algwrite ysum algwrite)rww2 rww3))
;;               ((Rec algread algwrite=>algread(algwrite ysum algwrite))rw1
;;               ([sd0,w1]
;;                 (Put algwrite ysum algwrite)sd0((InL algwrite algwrite)w1))
;;               ([rw3,rww2,rw4,rww3,rw5](Get algwrite ysum algwrite)rww2 rww3))
;;               ((Rec algread algwrite=>algread(algwrite ysum algwrite))rw2
;;               ([sd0,w1]
;;                 (Put algwrite ysum algwrite)sd0((InL algwrite algwrite)w1))
;;               ([rw3,rww2,rw4,rww3,rw5]
;; 	       (Get algwrite ysum algwrite)rww2 rww3))])))])

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "CoWriteIn")))))

;; [sd,w]
;;  (CoRec algwrite=>algwrite)w
;;  ([w0]
;;    [case (Des w0)
;;      ((DummyL algread algwrite) ->
;;      Inr((Put algwrite ysum algwrite)sd((InL algwrite algwrite)w0)))
;;      (Inr rw ->
;;      Inr((Rec algread algwrite=>algread(algwrite ysum algwrite))rw
;;          ([sd0,w1](Put algwrite ysum algwrite)sd0((InR algwrite algwrite)w1))
;;          ([rw0,rww,rw1,rww0,rw2,rww1]
;;            [case sd
;;              (Lft ->
;;              (Rec algread algwrite=>algread(algwrite ysum algwrite))rw0
;;              ([sd0,w1]
;;                (Put algwrite ysum algwrite)sd0((InL algwrite algwrite)w1))
;;              ([rw3,rww2,rw4,rww3,rw5](Get algwrite ysum algwrite)rww2 rww3))
;;              (Mid ->
;;              (Rec algread algwrite=>algread(algwrite ysum algwrite))rw1
;;              ([sd0,w1]
;;                (Put algwrite ysum algwrite)sd0((InL algwrite algwrite)w1))
;;              ([rw3,rww2,rw4,rww3,rw5](Get algwrite ysum algwrite)rww2 rww3))
;;              (Rht ->
;;              (Rec algread algwrite=>algread(algwrite ysum algwrite))rw2
;;              ([sd0,w1]
;;                (Put algwrite ysum algwrite)sd0((InL algwrite algwrite)w1))
;;              ([rw3,rww2,rw4,rww3,rw5]
;; 	      (Get algwrite ysum algwrite)rww2 rww3))])))])

(add-program-constant "Cmp" (py "xi=>xi=>xi"))

(add-global-assumption
 "AxCmpIdL"
 "all f^((Cmp xi)(IdF xi)f^ eqd f^)")

(add-global-assumption
 "AxCmpIdR"
 "all f^((Cmp xi)f^(IdF xi)eqd f^)")

(add-global-assumption
 "AxCmpBound"
 "all f^1,f^2,sd((Sub xi)f^1 0 Zero(SDToInt sd#2)(Succ Zero) ->
  (Sub xi)((Cmp xi)f^1 f^2) 0 Zero(SDToInt sd#2)(Succ Zero))")

(add-global-assumption
 "AxAssocOutCmp"
 "all f^1,f^2,sd((Sub xi)f^1 0 Zero(SDToInt sd#2)(Succ Zero) ->
  (Cmp xi)((Out xi)sd f^1)f^2 eqd(Out xi)sd((Cmp xi)f^1 f^2))")

(add-global-assumption
 "AxOutIntroI"
 "all f^,sd(
 (Sub xi)f^ 0 Zero(SDToInt sd#2)(Succ Zero) ->
 (Sub xi)((Out xi)sd f^)0 Zero 0 Zero)")

(add-global-assumption
 "AxInOutId"
 "all f^1,f^2,sd((Sub xi)f^2 0 Zero(SDToInt sd#2)(Succ Zero) ->
   (Cmp xi)f^1 f^2 eqd(Cmp xi)((In xi)sd f^1)((Out xi)sd f^2))")

(add-global-assumption
 "AxAssocCmpIn"
 "all f^1,f^2,sd (In xi)sd((Cmp xi)f^1 f^2)eqd(Cmp xi)f^1((In xi)sd f^2)")

;; PropCompose
;; Cowrite f -> CoWrite g -> Cowrite (f g)
(set-goal "allnc f^1,f^2(CoWrite f^1 -> CoWrite f^2 ->
                         CoWrite((Cmp xi)f^1 f^2))")
(assume "f^1" "f^2" "CoWf1" "CoWf2")
(assert "exr f^3,f^4(CoWrite f^3 andd CoWrite f^4 andl
                     (Cmp xi)f^1 f^2 eqd(Cmp xi)f^3 f^4)")
 (intro 0 (pt "f^1"))
 (intro 0 (pt "f^2"))
 (split)
 (use "CoWf1")
 (split)
 (use "CoWf2")
 (use "InitEqD")
(assume "P(f1 o f2)")
(coind "P(f1 o f2)")
(drop "P(f1 o f2)")
(assume "f^3" "Pf3")
(by-assume "Pf3" "f^4" "Pf3 2")
(by-assume "Pf3 2" "f^5" "Hyp")
(inst-with-to "Hyp" 'left "CoWf4")
(inst-with-to "Hyp" 'right 'left "CoWf5")
(inst-with-to "Hyp" 'right 'right "Eq")
(drop "Hyp")
(inst-with-to "CoWriteClause" (pt "f^4") "CoWf4" "Clause f4")
(inst-with-to "CoWriteClause" (pt "f^5") "CoWf5" "Clause f5")
(simp "Eq")
;; Case id f4 or R f4
(elim "Clause f4")
(drop "Clause f4")
(assume "f4=Id")
(simp "f4=Id")
(drop "f4=Id")
(simp "AxCmpIdL")
;; Case id f5 or R f5
(elim "Clause f5")
;; id id
(assume "f5=Id")
(simp "f5=Id")
(intro 0)
(use "InitEqD")
;; id Read
(assume "Ex Read f5")
(by-assume "Ex Read f5" "f^6" "Read f5")
(inst-with-to "Read f5" 'left "Read f6")
(elim "Read f5")
(drop "Read f5")
(assume "Read f6 2" "f5=f6")
(drop "Read f6 2")
(simp "f5=f6")
(intro 1)
(intro 0 (pt "f^6"))
(split)
(elim "Read f6")
(drop "Read f6")
(assume "f^7" "sd" "f[I] sub I_d" "CoWrite outd f")
(intro 0 (pt "sd"))
(use "f[I] sub I_d")
(intro 0)
(use "CoWrite outd f")
;; 61
(assume "f^7" "Read L" "IH L" "Read M" "IH M" "Read R" "IH R")
(intro 1)
(use "IH L")
(use "IH M")
(use "IH R")
(use "InitEqD")
;; 34
(assume "Ex Read f4")
(by-assume "Ex Read f4" "f^6" "Read f6")
(elim "Read f6")
(assume "Useless1" "f4=f6")
(drop "Useless1")
(simp "f4=f6")
(elim "Clause f5")
;; R id
(assume "f5=Id")
(simp "f5=Id")
(simp "AxCmpIdR")
(intro 1)
(intro 0 (pt "f^6"))
(split)
(inst-with-to "Read f6" 'left "Read f6 3")
(elim "Read f6 3")
(assume "f^7" "sd" "f[I] sub I_d" "CoWrite outd f")
(intro 0 (pt "sd"))
(use "f[I] sub I_d")
(intro 0)
(use "CoWrite outd f")
(assume "f^7" "Read L" "IH L" "Read M" "IH M" "Read R" "IH R")
(intro 1)
(use "IH L")
(use "IH M")
(use "IH R")
(use "InitEqD")
;; R R
(assume "Ex Read f5")
(by-assume "Ex Read f5" "f^7" "Read f7")
(elim "Read f7")
(assume "Useless2" "f5=f7")
(drop "Useless2")
(simp "f5=f7")
(inst-with-to "Read f6" 'left "Read f6 inst")
;; (inst-with-to "Read f7" 'left "Read f7 inst")
(cut "allnc f^0(CoWrite f^0 -> (Sub xi)f^0 0 Zero 0 Zero ->
      exr f^(
       (Read (cterm (f^0) CoWrite f^0 ord
              exr f^1,f^2(CoWrite f^1 andd CoWrite f^2 andl
                          f^0 eqd(Cmp xi)f^1 f^2)))
       f^ andl (Cmp xi)f^6 f^0 eqd f^))")
 (assume "Hyp2")
 (inst-with-to "Hyp2" (pt "f^5") "CoWf5" "Hyp2 inst")
 (intro 1)
 (simp "<-" "f5=f7")
 (use "Hyp2 inst")
 (use "AxUcfBound")
;; Main Ind
(elim "Read f6 inst")
(drop "Read f6 inst")
;; Base case
(assume "f^" "sd" "f[I] sub I_sd" "CoWrite outd sd f"
	"f^0" "CoWf0" "f0 in I")
(intro 0 (pt "(Cmp xi)f^ f^0"))
(split)
(intro 0 (pt "sd"))
(use "AxCmpBound")
(use "f[I] sub I_sd")
(intro 1)
(intro 0 (pt "(Out xi)sd f^"))
(intro 0 (pt "f^0"))
(split)
(use "CoWrite outd sd f")
(split)
(use "CoWf0")
(simp "AxAssocOutCmp")
(use "InitEqD")
(use "f[I] sub I_sd")
(use "InitEqD")
;; Step case
(assume "f^" "ReadL" "IHL" "ReadM" "IHM" "ReadR" "IHR" "f^8" "CoWf8" "f8 in I")
(drop "ReadL" "IHL" "ReadM" "IHM" "ReadR" "IHR")
(inst-with-to "CoWriteClause" (pt "f^8") "CoWf8" "Case f8")
(elim "Case f8") ;141-142
(drop "Case f8")
;; Left. f8=Id
(assume "f8=Id")
(simp "f8=Id")
(simp "AxCmpIdR")
(intro 0 (pt "f^"))
(split)
(intro 1)
(inst-with-to "IHL" (pt "f^8") "CoWf8" "f8 in I" "IHLinst")
(by-assume "IHLinst" "f^9" "HypL and")
(inst-with-to "HypL and" 'left "HypL")
(simp-with "<-" "AxCmpIdR" (pt "(In xi)Lft f^"))
(simp "<-" "f8=Id")
(elim "HypL and")
(drop "HypL and")
(assume "Useless3" "Heq3")
(simp "Heq3")
(drop "Useless3" "Heq3")
(use "HypL")
;; 151
(inst-with-to "IHM" (pt "f^8") "CoWf8" "f8 in I" "IHMinst")
(by-assume "IHMinst" "f^9" "HypM and")
(inst-with-to "HypM and" 'right "HeqM")
(simp-with "<-" "AxCmpIdR" (pt "(In xi)Mid f^"))
(simp "<-" "f8=Id")
(simp "HeqM")
(use "HypM and")
;; 152
(inst-with-to "IHR" (pt "f^8") "CoWf8" "f8 in I" "IHRinst")
(by-assume "IHRinst" "f^9" "HypR and")
(simp-with "<-" "AxCmpIdR" (pt "(In xi)Rht f^"))
(simp "<-" "f8=Id")
(inst-with-to "HypR and" 'right "HeqR")
(simp "HeqR")
(use "HypR and")
;; 149
(use "InitEqD")
;; 142
(drop "Case f8")
;; Right. Readf8
(assume "Hex Readf8")
(by-assume "Hex Readf8" "f^9" "Hand Readf9")
(inst-with-to "Hand Readf9" 'left "Readf9")
(assert "CoWrite f^8")
 (use "CoWf8")
(elim "Hand Readf9")
(drop "Hand Readf9")
(assume "Useless4" "f8=f9")
(simp "f8=f9")
(drop "Useless4" "f8=f9")
;; 200
;; Sub ind
(elim "Readf9")
(drop "Readf9")
;; Sub base
(assume "f^10" "sd" "f10[I] sub I_sd" "CoWrite out f10" "CoWf10")
(assert "(Sub xi)((Out xi)sd f^10)0 Zero 0 Zero")
 (use "AxOutIntroI")
 (use "f10[I] sub I_sd")
(assume "Out f10 in I")
(simp-with "AxInOutId" (pt "f^") (pt "f^10") (pt "sd")
	   "f10[I] sub I_sd")
(cases (pt "sd")) ;210-212
(assume "Case L")
(assert "CoWrite((Out xi)Lft f^10)")
 (simp "<-" "Case L")
 (use "CoWrite out f10")
(assume "CoWrite outL f10")
(simphyp-with-to "Out f10 in I" "Case L" "Out L f10 in I")
(inst-with-to "IHL" (pt "(Out xi)Lft f^10") "CoWrite outL f10"
	      "Out L f10 in I" "Hex IHL")
(use "Hex IHL")
;; 211
(assume "Case M")
(assert "CoWrite((Out xi)Mid f^10)")
 (simp "<-" "Case M")
 (use "CoWrite out f10")
(assume "CoWrite outM f10")
(simphyp-with-to "Out f10 in I" "Case M" "Out M f10 in I")
(inst-with-to "IHM" (pt "(Out xi)Mid f^10") "CoWrite outM f10"
	      "Out M f10 in I" "Hex IHM")
(use "Hex IHM")
;; 212
(assume "Case R")
(assert "CoWrite((Out xi)Rht f^10)")
 (simp "<-" "Case R")
 (use "CoWrite out f10")
(assume "CoWrite outR f10")
(simphyp-with-to "Out f10 in I" "Case R" "Out R f10 in I")
(inst-with-to "IHR" (pt "(Out xi)Rht f^10") "CoWrite outR f10"
	      "Out R f10 in I" "Hex IHR")
(use "Hex IHR")
;; 202
;; Sub step
(assume "f^10" "SubReadL" "SubIHL" "SubReadM" "SubIHM" "SubReadR" "SubIHR"
	"CoWf10")
(inst-with-to "CoWriteIn" (pt "f^10") (pt "Lft") "CoWf10" "CoWf10 inL")
(inst-with-to "SubIHL" "CoWf10 inL" "Hex SubIHL")
(drop "SubIHL" "CoWf10 inL")
(inst-with-to "CoWriteIn" (pt "f^10") (pt "Mid") "CoWf10" "CoWf10 inM")
(inst-with-to "SubIHM" "CoWf10 inM" "Hex SubIHM")
(drop "SubIHM" "CoWf10 inM")
(inst-with-to "CoWriteIn" (pt "f^10") (pt "Rht") "CoWf10" "CoWf10 inR")
(inst-with-to "SubIHR" "CoWf10 inR" "Hex SubIHR")
(drop "SubIHR" "CoWf10 inR")
;; 255
(intro 0 (pt "(Cmp xi)f^ f^10"))
(split)
(intro 1)
(by-assume "Hex SubIHL" "f^11" "Hand SubIHL")
(simp "AxAssocCmpIn")
(elim "Hand SubIHL")
(assume "Hand SubIHL L" "HeqL")
(simp "HeqL")
(use "Hand SubIHL L")
;; 260
(by-assume "Hex SubIHM" "f^11" "Hand SubIHM")
(simp "AxAssocCmpIn")
(elim "Hand SubIHM")
(assume "HandSubIHML" "HandSubIHMR")
(simp "HandSubIHMR")
(use "HandSubIHML")
;; 261
(by-assume "Hex SubIHR" "f^11" "Hand SubIHR")
(simp "AxAssocCmpIn")
(elim "Hand SubIHR")
(assume "HandSubIHRL" "HandSubIHRR")
(simp "HandSubIHRR")
(use "HandSubIHRL")
;; 258
(use "InitEqD")
;; Proof finished.
(save "PropCompose")

(define eterm-cmp
  (proof-to-extracted-term (theorem-name-to-proof "PropCompose")))

(add-var-name "rq" (py "algread(algwrite ysum algwrite yprod algwrite)"))
(add-var-name
 "fwrq" (py "algwrite=>algread(algwrite ysum algwrite yprod algwrite)"))
(add-var-name "ww" (py "algwrite yprod algwrite"))

(define neterm-cmp (rename-variables (nt eterm-cmp)))

(pp neterm-cmp)

;; [w,w0]
;;  (CoRec algwrite yprod algwrite=>algwrite)(w pair w0)
;;  ([ww]
;;    [if (Des[if ww ([w1,w2]w1)])
;;      [if (Des[if ww ([w1,w2]w2)])
;;       (DummyL algread(algwrite ysum algwrite yprod algwrite))
;;       ([rw]
;;        Inr((Rec algread algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;            rw
;;            ([sd,w1]
;;              (Put algwrite ysum algwrite yprod algwrite)sd
;;              ((InL algwrite (algwrite yprod algwrite))w1))
;;            ([rw0,rq,rw1,rq0,rw2]
;;              (Get algwrite ysum algwrite yprod algwrite)rq rq0)))]
;;      ([rw]
;;       [if (Des[if ww ([w1,w2]w2)])
;;         (Inr((Rec algread algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;             rw
;;             ([sd,w1]
;;               (Put algwrite ysum algwrite yprod algwrite)sd
;;               ((InL algwrite (algwrite yprod algwrite))w1))
;;             ([rw0,rq,rw1,rq0,rw2]
;;               (Get algwrite ysum algwrite yprod algwrite)rq rq0)))
;;         ([rw0]
;;          Inr((Rec algread algwrite=>algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;              rw
;;              ([sd,w1,w2]
;;                (Put algwrite ysum algwrite yprod algwrite)sd
;;                ((InR (algwrite yprod algwrite) algwrite)(w1 pair w2)))
;;              ([rw1,fwrq,rw2,fwrq0,rw3,fwrq1,w1]
;;                [if (Des w1)
;;                  ((Get algwrite ysum algwrite yprod algwrite)(fwrq w1)
;;                  (fwrq0 w1)
;;                  (fwrq1 w1))
;;                  ([rw4]
;;                   (Rec algread algwrite=>algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;                   rw4
;;                   ([sd,w2,w3][if sd (fwrq w2) (fwrq0 w2) (fwrq1 w2)])
;;                   ([rw5,fwrq2,rw6,fwrq3,rw7,fwrq4,w2]
;;                     (Get algwrite ysum algwrite yprod algwrite)
;;                     (fwrq2(cCoWriteIn Lft w2))
;;                     (fwrq3(cCoWriteIn Mid w2))
;;                     (fwrq4(cCoWriteIn Rht w2)))
;;                   w1)])
;;              [if ww ([w1,w2]w2)]))])])

(ppc neterm-cmp)

;; [w,w0]
;;  (CoRec algwrite yprod algwrite=>algwrite)(w pair w0)
;;  ([ww]
;;    [case (Des[case ww (w1 pair w2 -> w1)])
;;      ((DummyL algread algwrite) ->
;;      [case (Des[case ww (w1 pair w2 -> w2)])
;;        ((DummyL algread algwrite) ->
;;        (DummyL algread(algwrite ysum algwrite yprod algwrite)))
;;        (Inr rw ->
;;        Inr((Rec algread algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;            rw
;;            ([sd,w1]
;;              (Put algwrite ysum algwrite yprod algwrite)sd
;;              ((InL algwrite (algwrite yprod algwrite))w1))
;;            ([rw0,rq,rw1,rq0,rw2]
;;              (Get algwrite ysum algwrite yprod algwrite)rq rq0)))])
;;      (Inr rw ->
;;      [case (Des[case ww (w1 pair w2 -> w2)])
;;        ((DummyL algread algwrite) ->
;;        Inr((Rec algread algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;            rw
;;            ([sd,w1]
;;              (Put algwrite ysum algwrite yprod algwrite)sd
;;              ((InL algwrite (algwrite yprod algwrite))w1))
;;            ([rw0,rq,rw1,rq0,rw2]
;;              (Get algwrite ysum algwrite yprod algwrite)rq rq0)))
;;        (Inr rw0 ->
;;        Inr((Rec algread algwrite=>algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;            rw
;;            ([sd,w1,w2]
;;              (Put algwrite ysum algwrite yprod algwrite)sd
;;              ((InR (algwrite yprod algwrite) algwrite)(w1 pair w2)))
;;            ([rw1,fwrq,rw2,fwrq0,rw3,fwrq1,w1]
;;              [case (Des w1)
;;                ((DummyL algread algwrite) ->
;;                (Get algwrite ysum algwrite yprod algwrite)(fwrq w1)
;;                (fwrq0 w1)
;;                (fwrq1 w1))
;;                (Inr rw4 ->
;;                (Rec algread algwrite=>algwrite=>algread(algwrite ysum algwrite yprod algwrite))
;;                rw4
;;                ([sd,w2,w3]
;;                  [case sd
;;                    (Lft -> fwrq w2)
;;                    (Mid -> fwrq0 w2)
;;                    (Rht -> fwrq1 w2)])
;;                ([rw5,fwrq2,rw6,fwrq3,rw7,fwrq4,w2]
;;                  (Get algwrite ysum algwrite yprod algwrite)
;;                  (fwrq2(cCoWriteIn Lft w2))
;;                  (fwrq3(cCoWriteIn Mid w2))
;;                  (fwrq4(cCoWriteIn Rht w2)))
;;                w1)])
;;            [case ww (w1 pair w2 -> w2)]))])])

(animate "CoWriteIn")

;; (pp (nt (proof-to-extracted-term (theorem-name-to-proof "PropCompose"))))
;; 100 lines

(deanimate "CoWriteIn")

;; 5. Definite integration of a type-0 ucf
;; =======================================

;; 1/2 * (Integral f), which is in [-1,1]
(add-program-constant "HInt" (py "xi=>r"))
(add-program-constant "H" (py "r=>r"))
(add-program-constant "P" (py "r=>r=>r"))

(add-global-assumption
 "AxHIntInI"
 "all f^ (Elem r)((HInt xi r)f^)0 Zero")

(add-global-assumption
 "AxHIntOutMod"
 "all f^,sd((HInt xi r)f^ eqd((Av r)((HInt xi r)((Out xi)sd f^))sd))")

(add-global-assumption
 "AxElemAv"
 "all x^,a,sd,n((Elem r)x^ a n ->
  (Elem r)((Av r)x^ sd)((a+SDToInt sd)/2)(Succ n))")

(add-global-assumption
 "AxHIntIn"
 "all f^((HInt xi r)f^ eqd
         (H r)((P r)((HInt xi r)((In xi)Lft f^))
                    ((HInt xi r)((In xi)Rht f^))))")

(add-global-assumption
 "AxAvrg"
 "all x^1,x^2,a1,a2,n((Elem r)x^1 a1 n -> (Elem r)x^2 a2 n ->
                      (Elem r)((H r)((P r)x^1 x^2))((a1+a2)/2) n)")

(add-global-assumption
 "AxHIntIdF"
 "(HInt xi r)(IdF xi)eqd(Z r)")

(add-global-assumption
 "AxZ"
 "all n (Elem r)(Z r)(0#1)n")

;; PropInt
;; CoWrite f -> all n ex p (Int f) in I p n
(set-goal "allnc f^(CoWrite f^ -> all n exl a((Elem r)((HInt xi r)f^)a n))")
(cut "all n allnc f^(CoWrite f^ -> exl a((Elem r)((HInt xi r)f^)a n))")
 (assume "H0" "f^" "CoWf" "n")
 (use "H0")
 (use "CoWf")
(ind)
;; Base case
(assume "f^" "CoWf")
(intro 0 (pt "0#1"))
(use "AxHIntInI")
;; Step case
(assume "n" "IH" "f^" "CoWf")
(inst-with-to "CoWriteClause" (pt "f^") "CoWf" "Hcase")
(elim "Hcase")
;; Left case
(assume "f=IdF")
(simp "f=IdF")
(intro 0 (pt "0#1"))
(simp "AxHIntIdF")
(use "AxZ")
;; Right case
(assume "HRead")
(by-assume "HRead" "f^0" "Hand")
(inst-with-to "Hand" 'left "Read f0")
(inst-with-to "Hand" 'right "f=f0")
(simp "f=f0")
(elim "Read f0")
;; Side base case
(assume "f^1" "sd" "f1[I] sub I_sd" "CoWrite Out f1")
(inst-with-to "IH" (pt "(Out xi)sd f^1") "CoWrite Out f1" "IHinst")
(elim "IHinst")
(assume "a" "H1")
(intro 0 (pt "(a+(SDToInt sd))/2"))
(simp "AxHIntOutMod" (pt "sd"))
(use "AxElemAv")
(use "H1")
;; Side step case
(assume "f^1" "ReadL" "IHL" "ReadM" "IHM" "ReadR" "IHR")
(by-assume "IHL" "a1" "HElem a1")
(by-assume "IHR" "a2" "HElem a2")
(intro 0 (pt "(a1+a2)/2"))
(simp "AxHIntIn")
(use "AxAvrg")
(use "HElem a1")
(use "HElem a2")
;; Proof finished.
(save "PropInt")

(define eterm-int (proof-to-extracted-term (theorem-name-to-proof "PropInt")))
(define neterm-int (rename-variables (nt eterm-int)))

(pp neterm-int)

;; [w,n]
;;  (Rec nat=>algwrite=>rat)n([w0]0)
;;  ([n0,(algwrite=>rat),w0]
;;    [if (Des w0)
;;      0
;;      ([rw]
;;       (Rec algread algwrite=>rat)rw
;;       ([sd0,w1]((algwrite=>rat)w1+SDToInt sd0)/2)
;;       ([rw0,a,rw1,a0,rw2,a1](a+a1)/2))])
;;  w

(ppc neterm-int)

;; [w,n]
;;  (Rec nat=>algwrite=>rat)n([w0]0)
;;  ([n0,(algwrite=>rat),w0]
;;    [case (Des w0)
;;      ((DummyL algread algwrite) -> 0)
;;      (Inr rw ->
;;      (Rec algread algwrite=>rat)rw
;;      ([sd0,w1]((algwrite=>rat)w1+SDToInt sd0)/2)
;;      ([rw0,a,rw1,a0,rw2,a1](a+a1)/2))])
;;  w

;; 6. Experiments
;; ==============

;; For Haskell extraction: animate after defining neterm-a, so that
;; the extracted function calls the extracted functions from the
;; lemmas instead of inlining them.

(animate "PropInt")
(animate "PropCompose") ;uses cCoWriteIn
(animate "CoWriteIn")
(animate "PropApply") ;probably not needed
(animate "LemmaApply")
(animate "CoWriteToCont") ;uses cOutElimCor cStandardSpli
(animate "OutElimCor")
(animate "ContToCoWrite") ;uses cContToCoWriteAux
(animate "ContToCoWriteAux") ;uses cFind cId
;; (animate "Id") ;not needed for Haskell translation
(animate "FindSd") ;uses cStandardSpli
(animate "StandardSplit")

(add-program-constant "sqrt" (py "rat=>nat=>rat"))

(add-computation-rules
 "sqrt a Zero" "Succ Zero"
 "sqrt a(Succ n)" "(sqrt a n+a/sqrt a n)/2")

;; (pp (nt (pt "sqrt 2(PosToNat 3)")))

;; f1(x) = -x
(define f1 (pt "[n]Succ n@([a]0-a)"))

;; f2(x) = sqrt(x+2) - 1
;; In this case, the uniform Cauchy modulus is M(n)=n+1.

(define f2 (pt "[n]n--1@([a]sqrt(a+2)(n+1)-1)"))

;; f3(x) = 2x^2 - 1
(define f3 (pt "[n]n+1@([a]2*a*a-1)"))

'(
(terms-to-haskell-program
 "~/temp/readwrite.hs"
 (list (list neterm-a "type1to0")
       (list neterm-b "type0to1")
       (list neterm-apply "application")
       (list neterm-cmp "composition")
       (list neterm-int "integration")
       (list f1 "f1")
       (list f2 "f2")
       (list f3 "f3")))
)

'(
{- takeIv -}
takeIv _ II = []
takeIv 0 (C d x) = []
takeIv n (C d x) = (show d) : (takeIv (n-1) x)

{- pretty-printing read-write machines -}

spc l = concat $ replicate l " "

ppW _ l Stop = "Stop"
ppW 0 l (Cont x) = "Stop"
ppW n l (Cont x) = "Cont " ++ (ppR n (l+5) x)
ppR n l (Put d x) = "Put " ++ (show d) ++ " " ++ (ppW (n-1) (l+6) x)
ppR n l (Get x y z) = concat ["Get ", ppR n (l+4) x, "\n", spc (l+4),
			      ppR n (l+4) y, "\n", spc (l+4),
			      ppR n (l+4) z]
pp n w = putStrLn (ppW n 0 w)
)

(deanimate "PropInt")
(deanimate "PropCompose") ;uses cCoWriteIn
(deanimate "CoWriteIn")
(deanimate "PropApply") ;probably not needed
(deanimate "LemmaApply")
(deanimate "CoWriteToCont") ;uses cOutElimCor cStandardSpli
(deanimate "OutElimCor")
(deanimate "ContToCoWrite") ;uses cContToCoWriteAux
(deanimate "ContToCoWriteAux") ;uses cFind cId
;; (deanimate "Id")
(deanimate "FindSd") ;uses cStandardSpli
(deanimate "StandardSplit")

;; 6.1 type-1 to type-0
;; ====================

;; Main> pp 1 (type1to0 f1)

;; Cont Get Get Get Put Rht Stop
;;                  Put Rht Stop
;;                  Put Rht Stop
;;              Get Put Rht Stop
;;                  Put Rht Stop
;;                  Put Rht Stop
;;              Get Put Rht Stop
;;                  Put Rht Stop
;;                  Put Mid Stop
;;          Get Get Put Rht Stop
;;                  Put Rht Stop
;;                  Put Mid Stop
;;              Get Put Mid Stop
;;                  Put Mid Stop
;;                  Put Mid Stop
;;              Get Put Mid Stop
;;                  Put Mid Stop
;;                  Put Lft Stop
;;          Get Get Put Mid Stop
;;                  Put Mid Stop
;;                  Put Lft Stop
;;              Get Put Lft Stop
;;                  Put Lft Stop
;;                  Put Lft Stop
;;              Get Put Lft Stop
;;                  Put Lft Stop
;;                  Put Lft Stop

;; 6.2 Application
;; ===============

;; Main> takeIv 10 (application (type1to0 f1) (C Lft(C Lft(C Lft(C Lft II)))))

;; ["Rht","Rht","Rht","Rht","Mid","Mid","Mid","Mid","Mid","Mid"]

;; 6.3 Composition
;; ===============

;; Main> takeIv 10 $ application (composition (type1to0 f1) (type1to0 f3)) (C Mid(C Mid(C Mid(C Mid II))))

;; ["Rht","Rht","Rht","Rht","Rht","Rht","Rht","Rht","Rht","Rht"] {- result -}

;; 6.4 Definite integration
;; ========================

;; Main> integration (type1to0 f2) 4

;; 817 % 2048 {- result -}

;; Main> integration (composition (type1to0 f3) (type1to0 f1)) 1

;; (-3) % 16 {- result -}

;; Main> integration (type1to0 f3) 3

;; (-2549) % 8192 {- result -}

;; Main> integration (type1to0 f3) 4

;; (-683003) % 2097152

;; 6.5 Some experiments in Minlog
;; ==============================

(animate "PropInt")
(animate "PropCompose") ;uses cCoWriteIn
(animate "CoWriteIn")
(animate "PropApply") ;probably not needed
(animate "LemmaApply")
(animate "CoWriteToCont") ;uses cOutElimCor cStandardSpli
(animate "OutElimCor")
(animate "ContToCoWrite") ;uses cContToCoWriteAux
(animate "ContToCoWriteAux") ;uses cFind cId
(animate "Id")
(animate "FindSd") ;uses cStandardSpli
(animate "StandardSplit")

(pp (nt (undelay-delayed-corec (mk-term-in-app-form neterm-a f1) 1)))

;; profile
    ;; 103 collections
    ;; 2537 ms elaohed cpu time, including 51 ms collecting
    ;; 5020 ms elaohed real time, including 52 ms collecting
    ;; 873135808 bytes allocated, including 863858320 bytes reclaimed

;; Cont
;; ((Get algwrite)
;;  ((Get algwrite)
;;   ((Get algwrite)
;;    ((Put algwrite)Rht
;;     ((CoRec (nat=>nat@@(rat=>rat))=>algwrite) ...

(define minusone
  (pt "C Lft(C Lft(C Lft(C Lft(C Lft(C Lft(C Lft(C Lft II)))))))"))

(define app-flip-minusone
  (undelay-delayed-corec
   (mk-term-in-app-form
    neterm-apply (make-term-in-app-form neterm-a f1) minusone)
   2))

(pp (nt app-flip-minusone))

;; profile
    ;; 358 collections
    ;; 8401 ms elaohed cpu time, including 246 ms collecting
    ;; 8433 ms elaohed real time, including 269 ms collecting
    ;; 3011682800 bytes allocated, including 3017611808 bytes reclaimed

;; C Rht
;; (C Rht
;;  ((CoRec algwrite@@iv=>iv)
;;   ((CoRec (nat=>nat@@(rat=>rat))=>algwrite) ...

(pp (nt (mk-term-in-app-form
	 neterm-int
	 (pt "Cont((Get algwrite)
                      ((Put algwrite) Rht Stop)
                      ((Put algwrite) Rht Stop)
                      ((Put algwrite) Rht Stop))")
	 (pt "Succ Zero"))))
;; 1#2

(pp (nt
     (undelay-delayed-corec
      (mk-term-in-app-form
       neterm-int
       (undelay-delayed-corec (make-term-in-app-form neterm-a f2) 2)
       (pt "PosToNat 2"))
      1)))

;; profile
    ;; 1448 collections
    ;; 35675 ms elapsed cpu time, including 824 ms collecting
    ;; 35693 ms elapsed real time, including 838 ms collecting
    ;; 12194461968 bytes allocated, including 12199298544 bytes reclaimed

;; 3#8

