;; 2021-03-04.  ivt.scm

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")
(libload "cont.scm")
;; (set! COMMENT-FLAG #t)

(display "loading ivt.scm ...") (newline)

;; Intermediate value theorem, with 1/2^l a lower bound on the slope:

;; Approximate splitting principle.

;; (pp "ApproxSplit")
;; all x,y,z,p(Real x -> Real y -> Real z -> RealLt x y p -> z<<=y oru x<<=z)

;; We use a formulation of ApproxSplit without disjunction.

;; ApproxSplitBoole
(set-goal "all x1,x2,x3,p(Real x1 -> Real x2 -> Real x3 ->
                    RealLt x1 x2 p -> exl boole(
                    (boole -> x3<<=x2) andi ((boole -> F) -> x1<<=x3)))")
(assume "x1" "x2" "x3" "p" "Rx1" "Rx2" "Rx3" "x1<x2")
(assert "x3<<=x2 oru x1<<=x3")
 (use "ApproxSplit" (pt "p"))
 (use "Rx1")
 (use "Rx2")
 (use "Rx3")
 (use "x1<x2")
(assume "Disj")
(elim "Disj")
(drop "Disj")
(assume "x3<=x2")
(intro 0 (pt "True"))
(split)
(assume "Useless")
(use "x3<=x2")
(assume "Absurd")
(use "EfRealLe")
(use "Absurd")
(use "Truth")
;; 11
(assume "x1<=x3")
(intro 0 (pt "False"))
(split)
(assume "Absurd")
(use "EfRealLe")
(use "Absurd")
(assume "Useless")
(use "x1<=x3")
;; Proof finished.
;; (cdp)
(save "ApproxSplitBoole")

(add-sound "ApproxSplitBoole")

;; ok, ApproxSplitBooleSound has been added as a new theorem:

;; allnc x,x0,x1,p(
;;  Real x -> 
;;  Real x0 -> 
;;  Real x1 -> 
;;  RealLt x x0 p -> 
;;  (ExLTMR (cterm (boole) (boole -> x1<<=x0) andnc ((boole -> F) -> x<<=x1)))
;;  (cApproxSplitBoole x x0 x1 p))

;; with computation rule

;; cApproxSplitBoole eqd cApproxSplitPos

;; We do not deanimate ApproxSplitBoole since the extracted term is short.

;; We first prove an auxiliary lemma IVTAux, for the construction step.

;; First we define a (formally inductive) correctness predicate:

(add-ids
 (list (list "Corr" (make-arity (py "cont") (py "rat") (py "rat") (py "pos"))))
 '("all f,c,d,p(
     f doml<=c -> d<=f domr -> c+(1#2**p)<=d ->
     f c<<=0 -> 0<<=f d ->
     Corr f c d p)" "CorrIntro"))

;; Now the properties of Corr.

(set-goal "all f,c,d,p(Corr f c d p -> f doml<=c)")
(assume "f" "c" "d" "p")
(elim)
(search)
(save "CorrElim1")

(set-goal "all f,c,d,p(Corr f c d p -> d<=f domr)")
(assume "f" "c" "d" "p")
(elim)
(search)
(save "CorrElim2")

(set-goal "all f,c,d,p(Corr f c d p -> c+(1#2**p)<=d)")
(assume "f" "c" "d" "p")
(elim)
(search)
(save "CorrElim3")

(set-goal "all f,c,d,p(Corr f c d p -> f c<<=0)")
(assume "f" "c" "d" "p")
(elim)
(search)
(save "CorrElim4")

(set-goal "all f,c,d,p(Corr f c d p -> 0<<=f d)")
(assume "f" "c" "d" "p")
(elim)
(search)
(save "CorrElim5")

;; We also will use a corollary to CorrElim3
;; CorrElim3Cor
(set-goal "all f,c,d,p(Corr f c d p -> c<=d)")
(assume "f" "c" "d" "p" "CorrHyp")
(use "RatLeTrans" (pt "c+(1#2**p)"))
(use "RatLeTrans" (pt "c+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "CorrElim3" (pt "f"))
(use "CorrHyp")
;; Proof finished.
(save "CorrElim3Cor")

;; RatTwoTimes
(set-goal "all a 2*a==a+a")
(simp (pf "(2#1)=RatPlus 1 1"))
(assume "a")
(simprat "RatTimesPlusDistrLeft")
(ng)
(use "Truth")
(use "Truth")
;; Proof fnished.
(save "RatTwoTimes")

;; RatThreeTimes
(set-goal "all a 3*a==a+a+a")
(simp (pf "(3#1)=RatPlus(RatPlus 1 1)1"))
(assume "a")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(use "Truth")
(use "Truth")
;; Proof fnished.
(save "RatThreeTimes")

;; (pp "RatLe6RewRule")
;; all p,q,a,b ((p#q)*a<=(p#q)*b)=(a<=b)

;; IVTAux11
(set-goal "all c,d,p( c+(1#2**p)<=d -> c+(1#2**PosS p)<=(1#3)*(c+d+d))")
(assume "c" "d" "p" "LeHyp")
(use "RatLeTrans" (pt "(1#2)*(c+d)"))
;; 3,4
;; ?^3:c+(1#2**PosS p)<=(1#2)*(c+d)
(inst-with-to
 "RatLe6RewRule"
 (pt "2") (pt "1") (pt "c+(1#2**PosS p)") (pt "(1#2)*(c+d)")
 "RatLe6RewRuleInst")
(simp "<-" "RatLe6RewRuleInst")
(drop "RatLe6RewRuleInst")
(ng)
(simprat "RatTimesPlusDistr")
(simprat "RatTwoTimes")
(simp "<-" "RatPlusAssoc")
(simp "RatLe2RewRule")
(ng)
(assert "(2#2**PosS p)==(1#2**p)")
 (ng)
 (simp (pf "PosS p=Succ p"))
 (use "Truth")
 (use "PosSSucc")
;; Assertion proved.
(assume "Assertion")
(simprat "Assertion")
(use "LeHyp")
;; 4
;; ?^4:(1#2)*(c+d)<=(1#3)*(c+d+d)
(inst-with-to
 "RatLe6RewRule"
 (pt "6") (pt "1") (pt "(1#2)*(c+d)") (pt "(1#3)*(c+d+d)")
 "RatLe6RewRuleInst")
(simp "<-" "RatLe6RewRuleInst")
(drop "RatLe6RewRuleInst")
(ng)
(simprat "RatTimesPlusDistr")
(simprat "RatThreeTimes")
(simprat "RatThreeTimes")
(simprat "RatTwoTimes")
(ng)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "RatLe2RewRule")
(use "RatLeMonPlus")
(use "RatLeTrans" (pt "c+(1#2**p)"))
(use "RatLeTrans" (pt "c+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "LeHyp")
(simp "RatPlusComm")
(use "Truth")
;; Proof finished.
(save "IVTAux11")

;; IVTAux1
(set-goal "all f,c,d,p(Cont f -> Corr f c d p -> 0<<=f((1#3)*(c+d+d)) ->
                       Corr f c((1#3)*(c+d+d))(PosS p))")
(assume "f" "c" "d" "p" "Cont f" "Corr f c d p" "0<<=f d1")
(cut "f doml<=c")
(assume "a<=c")
(cut "d<=f domr")
(assume "d<=b")
(cut "c+(1#2**p)<=d")
(assume "c<_p d")
(cut "f c<<=0")
(assume "f c<<=0")
(cut "0<<=f d")
(assume "0<<=f d")
;; ?^17:Corr f c((1#3)*(c+d+d))(PosS p)
(use "CorrIntro")
(auto)
;; ?^19:(1#3)*(c+d+d)<=f domr
(use "RatLeTrans" (pt "(1#3)*(3*d)"))
(simprat "RatThreeTimes") 
(ng #t)
(use "RatLeTrans" (pt "c+(1#2**p)"))
(use "RatLeTrans" (pt "c+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "c<_p d")
(ng #t)
(use "d<=b")
;; ?^20:c+(1#2**PosS p)<=(1#3)*(c+d+d)
(use "IVTAux11")
(use "c<_p d")
;; ?^21:f c<<=0
(use "f c<<=0")
;; ?^22:0<<=f((1#3)*(c+d+d))
(use "0<<=f d1")
;; ?^16:0<<=f d
(use-with "CorrElim5" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
;; ?^13:f c<<=0
(use-with "CorrElim4" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
(use-with "CorrElim3" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
(use-with "CorrElim2" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
(use-with "CorrElim1" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
;; Proof finished.
;; (cdp)
(save "IVTAux1")

;; IVTAux21
(set-goal "all c,d,p(c+(1#2**p)<=d -> (1#3)*(c+c+d)+(1#2**PosS p)<=d)")
(assume "c" "d" "p" "LeHyp")
(use "RatLeTrans" (pt "(1#2)*(c+d)+(1#2**PosS p)"))
;; 3,4
;; ?^3:(1#3)*(c+c+d)+(1#2**PosS p)<=(1#2)*(c+d)+(1#2**PosS p)
(ng #t)
;; ?^5:(1#3)*(c+c+d)<=(1#2)*(c+d)
(inst-with-to
 "RatLe6RewRule"
 (pt "6") (pt "1") (pt "(1#3)*(c+c+d)") (pt "(1#2)*(c+d)")
 "RatLe6RewRuleInst")
(simp "<-" "RatLe6RewRuleInst")
(drop "RatLe6RewRuleInst")
(ng)
(simprat "RatTimesPlusDistr")
(simprat "RatTwoTimes")
(simprat "RatTwoTimes")
(simprat "RatThreeTimes")
(ng)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "RatLe2RewRule")
(use "RatLeMonPlus")
(use "RatLeTrans" (pt "c+(1#2**p)"))
(use "RatLeTrans" (pt "c+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "LeHyp")
(simp "RatPlusComm")
(use "Truth")
;; ?^4:(1#2)*(c+d)+(1#2**PosS p)<=d
(inst-with-to
 "RatLe6RewRule"
 (pt "2") (pt "1") (pt "(1#2)*(c+d)+(1#2**PosS p)") (pt "d")
 "RatLe6RewRuleInst")
(simp "<-" "RatLe6RewRuleInst")
(drop "RatLe6RewRuleInst")
(simprat "RatTimesPlusDistr")
(ng)
(assert "(2#2**PosS p)==(1#2**p)")
 (ng)
 (simp (pf "PosS p=Succ p"))
 (use "Truth")
 (use "PosSSucc")
;; Assertion proved.
(assume "Assertion")
(simprat "Assertion")
(simprat "RatTwoTimes")
(simp (pf "c+d=d+c"))
(drop "Assertion")
(simp "<-" "RatPlusAssoc")
(use "RatLeMonPlus")
(use "Truth")
(use "LeHyp")
(use "RatPlusComm")
;; Proof finished.
(save "IVTAux21")

;; IVTAux2
(set-goal "all f,c,d,p(Cont f -> Corr f c d p -> f((1#3)*(c+c+d))<<=0 ->
                       Corr f((1#3)*(c+c+d))d(PosS p))")
(assume "f" "c" "d" "p" "Cont f" "Corr f c d p" "f c1<<=0")
(cut "f doml<=c")
(assume "a<=c")
(cut "d<=f domr")
(assume "d<=b")
(cut "c+(1#2**p)<=d")
(assume "c<_p d")
(cut "f c<<=0")
(assume "f c<<=0")
(cut "0<<=f d")
(assume "0<<=f d")
;; ?^17:Corr f((1#3)*(c+c+d))d(PosS p)
(use "CorrIntro")
;; ?^18:f doml<=(1#3)*(c+c+d)
(use "RatLeTrans" (pt "c"))
(auto)
;; ?^24:c<=(1#3)*(c+c+d)
(use "RatLeTrans" (pt "(1#3)*(3*c)"))
(use "Truth")
(simprat "RatThreeTimes")
(ng #t)
(use "RatLeTrans" (pt "c+(1#2**p)"))
(use "RatLeTrans" (pt "c+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "c<_p d")
;; ?^19:d<=f domr
(use-with "CorrElim2" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
;; ?^20:(1#3)*(c+c+d)+(1#2**PosS p)<=d
(use "IVTAux21")
(use "c<_p d")
(use "f c1<<=0")
;; ?^22:0<<=f d
(use-with "CorrElim5" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
;; ?^16:0<<=f d
(use-with "CorrElim5" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
(use-with "CorrElim4" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
(use-with "CorrElim3" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
(use-with "CorrElim2" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
(use-with "CorrElim1" (pt "f") (pt "c") (pt "d") (pt "p") "Corr f c d p")
;; Proof finished.
(save "IVTAux2")

;; Now we prove IVTAux

(add-var-name "cd" (make-yprod (py "rat") (py "rat")))

;; We prove d1-c=(2#3)(d-c)

;; LeftEst
(set-goal "(1#3)*(c+d+d)+ ~c==(2#3)*(d+ ~c)")
(assume "c" "d")
(use "RatEqvPlusCancelR" (pt "c"))
(simprat "RatEqvPlusMinus")
(use "RatEqvTimesCancelL" (pt "(3#1)"))
(use "Truth")
(ng)
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(ng)
(simprat "RatTwoTimes")
(simprat "RatTwoTimes")
(simprat "RatThreeTimes")
(ng)
(simprat (pf "c+d+d==d+d+c"))
(simp "RatEqv3RewRule")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "RatEqv4RewRule")
(use "RatEqvTrans" (pt "d+0"))
(use "Truth")
(simp "RatEqv4RewRule")
(use "RatEqvTrans" (pt "0+ ~c+c"))
(simprat "RatEqvPlusMinus")
(use "Truth")
(simp "RatPlus1RewRule")
(simp "RatEqv4RewRule")
(ng)
(simprat (pf "~c+c==0"))
(use "Truth")
(use "Truth")
(simprat "<-" "RatTwoTimes")
(simp "<-" "RatPlusAssoc")
(simprat "<-" "RatTwoTimes")
(simp "RatPlusComm")
(use "Truth")
;; Proof finished.
(save "LeftEst")

;; RightEst
(set-goal "all c,d d+ ~((1#3)*(c+c+d))==(2#3)*(d+ ~c)")
(assume "c" "d")
(use "RatEqvPlusCancelR" (pt "((1#3)*(c+c+d))"))
(simprat "RatEqvPlusMinus")
(use "RatEqvTimesCancelL" (pt "(3#1)"))
(use "Truth")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(ng)
(simprat "RatTwoTimes")
(simprat "RatTwoTimes")
(simprat "RatThreeTimes")
(simp "RatEqv3RewRule")
(simp "<-" "RatPlusAssoc")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RightEst")

;; EstAux
(set-goal "all p (1#2**Succ(Succ p))<=(1#3)*(1#2**p)")
(assume "p")
(use "RatLeTrans" (pt "(1#4)*(1#2**p)"))
(ng)
(use "Truth")
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "EstAux")

;; Est
(set-goal "all c,d,p( c+(1#2**p)<=d ->
  (1#3)*(c+c+d)+(1#3)*(1#2**p)<=(1#3)*(c+d+d))")
(assume "c" "d" "p" "LeHyp")
(use "RatLeTimesCancelL" (pt "(3#1)"))
(use "Truth")
(simprat "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(ng)
(simp (pf "c+c+d+(1#2**p)=c+c+(d+(1#2**p))"))
(simp (pf "d+(1#2**p)=(1#2**p)+d"))
(ng)
(simp "<-" "RatPlusAssoc")
(use "RatLeMonPlus")
(use "Truth")
(use "LeHyp")
(use "RatPlusComm")
(use "Truth")
;; Proof finished.
(save "Est")

;; IVTAux
(set-goal "all f,q(
     Cont f -> 
     f f doml<<=0 -> 
     0<<=f f domr -> 
     all c,d,p(
      f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
     all p,cd(
      Corr f(lft cd)(rht cd)p -> 
      exl cd1(
       Corr f(lft cd1)(rht cd1)(PosS p) andnc 
       lft cd<=lft cd1 andnc 
       rht cd1<=rht cd andnc rht cd1-lft cd1==(2#3)*(rht cd-lft cd))))")
(assume
 "f" "q" "Cont f" "f a<<=0" "0<<=f b" "HypSlope" "p" "cd" "Corr f c d p")
(cut "f doml<=lft cd")
(assume "a<=c")
(cut "rht cd<=f domr")
(assume "d<=b")
(cut "lft cd<=rht cd")
(assume "c<=d")

(cut "exl cd0(lft cd0=(1#3)*(lft cd+lft cd+rht cd) andi
              rht cd0=(1#3)*(lft cd+rht cd+rht cd))")
(use "Id")
(assume "ExHyp")
(by-assume "ExHyp" "cd0" "cd0-Def")
(inst-with-to "cd0-Def" 'left "c0-Def")
(inst-with-to "cd0-Def" 'right "d0-Def")
(drop "cd0-Def")

(cut "exl boole((boole -> 0<<=f(rht cd0)) andi
                ((boole -> F) -> f(lft cd0)<<=0))")
(assume "ExBooleHyp")
(by-assume "ExBooleHyp" "boole" "ExKernel")
(cases (pt "boole"))

;; Case 1
(assume "Left")
(cut "0<<=f(rht cd0)")
(assume "0<<=f d0")
(intro 0 (pt "lft cd pair rht cd0"))
(split)
(ng #t)

;; Corr f(lft cd)(rht cd0)(PosS p)
(simp "d0-Def")
(use "IVTAux1")
(use "Cont f")
(use "Corr f c d p")
(simp "<-" "d0-Def")
(use "0<<=f d0")
;; ?^38:lft cd<=lft(lft cd pair rht cd0) andnc 
;;      rht(lft cd pair rht cd0)<=rht cd andnc 
;;      rht(lft cd pair rht cd0)-lft(lft cd pair rht cd0)=(2#3)*(rht cd-lft cd)
(ng #t)
(split)
(use "Truth")
(split)
(simp "d0-Def")
(use "RatLeTrans" (pt "(1#3)*(rht cd+rht cd+rht cd)"))
(ng #t)
(use "c<=d")
(simprat "<-" "RatThreeTimes")
(use "Truth")
;; ?^49:rht cd0+ ~lft cd=(2#3)*(rht cd+ ~lft cd)
(simp "d0-Def")
(use "LeftEst")
(use "ExKernel")
(use "Left")

;; Case 2
(assume "Right")
(cut "f(lft cd0)<<=0")
(assume "f c0<<=0")
(intro 0 (pt "lft cd0 pair rht cd"))
(split)
(ng #t)

;; Corr f(lft cd0)(rht cd)(PosS p)
(simp "c0-Def")
(use "IVTAux2")
(use "Cont f")
(use "Corr f c d p")
(simp "<-" "c0-Def")
(use "f c0<<=0")
;; ?^63:lft cd<=lft(lft cd0 pair rht cd) andnc 
;;      rht(lft cd0 pair rht cd)<=rht cd andnc 
;;      rht(lft cd0 pair rht cd)-lft(lft cd0 pair rht cd)==
;;      (2#3)*(rht cd-lft cd)
(ng #t)
(split)
(simp "c0-Def")
(use "RatLeTrans" (pt "(1#3)*(lft cd+lft cd+lft cd)"))
(ng #t)
(simprat "<-" "RatThreeTimes")
(use "Truth")
(ng #t)
(use "c<=d")
(split)
(use "Truth")
;; ?^80:rht cd+ ~lft cd0==(2#3)*(rht cd+ ~lft cd)
(simp "c0-Def")
(use "RightEst")
(use "ExKernel")
(use "Right")
;;?_25:exl boole((boole -> 0<<=f rht cd0) andnc ((boole -> F) -> f lft cd0<<=0))
(cut "f doml<=lft cd0")
(assume "a<=c0")
(cut "lft cd0<=f domr")
(assume "c0<=b")
(cut "f doml<=rht cd0")
(assume "a<=d0")
(cut "rht cd0<=f domr")
(assume "d0<=b")
;; (pp "ApproxSplitBoole")

(use "ApproxSplitBoole" (pt "2+(p+q)"))
;; (use "ApproxSplitBoole" (pt "NatToPos((PosToNat 2)+(p+q))"))
;; (use "ApproxSplitBoole" (pt "NatToPos(Succ(Succ p))+q"))

;; Real(f(lft cd0))
;; (add-global-assumption
;;  "ContValsReal"
;;  "all f,x(Cont f -> Real x -> f doml<<=x -> x<<=f domr -> Real(f x))")
;; (add-global-assumption
;;  "ContRatValsReal"
;;  "all f,c(Cont f -> f doml<=c -> c<=f domr -> Real(f c))")
;; (use "ContRatValsReal")
(use "ContReal")
(use "Cont f")
(use "RatLeTrans" (pt "lft cd"))
(use "a<=c")
(use "RatLeTrans" (pt "rht cd"))
(use "c<=d")
(use "d<=b")
(use "RealRat")
;; ?^96:Real(f rht cd0)
(use "ContReal")
(use "Cont f")
(use "RatLeTrans" (pt "lft cd"))
(use "a<=c")
(use "RatLeTrans" (pt "rht cd"))
(use "c<=d")
(use "d<=b")
(use "RealRat")

;; Real 0
(use "RealRat")

;; RealLt(f lft cd0)(f rht cd0)(2+(p+q))
;; RealLt(f(lft cd0))(f(rht cd0))(p+2+l)
;; RealLt(f lft cd0)(f rht cd0)(NatToPos(NatPlus(PosToNat 2)(PosToNat(p+q))))
(use "HypSlope")
(auto)

;; ?^115:lft cd0+(1#2**(2+p))<=rht cd0
;; ?^107:lft cd0+(1#2**(p+2))<=rht cd0
(simp "c0-Def")
(simp "d0-Def")

;;?^117:(1#3)*(lft cd+lft cd+rht cd)+(1#2**(2+p))<=(1#3)*(lft cd+rht cd+rht cd)

(simp (pf "(1#2**(2+p))=(1#4)*(1#2**p)"))
(use "RatLeTrans" (pt "(1#3)*(lft cd+lft cd+rht cd)+(1#3)*(1#2**p)"))
(simp "RatLe2RewRule")
(simp "RatLe5RewRule")
(use "Truth")
;; (1#3)*(lft cd+lft cd+rht cd)+(1#3)*(1#2**p)<=(1#3)*(lft cd+rht cd+rht cd)
(use "Est")
(use "CorrElim3" (pt "f"))
(use "Corr f c d p")
;; ?^119:(1#2**(2+p))=(1#4)*(1#2**p)
(simp "<-" "PosExpTwoPosPlus")

;; ;; We even have more generally
;; ;; PosExpPosPlus
;; (set-goal "all r,p,q r**(p+q)=r**p*r**q")
;; (assume "r" "p" "q")
;; (assert "all n r**(n+q)=r**n*r**q")
;;  (ind)
;;  (use "Truth")
;;  (assume "n" "IH")
;;  (ng)
;;  (simp "IH")
;;  (simp "<-" "PosTimesAssoc")
;;  (simp "<-" "PosTimesAssoc")
;;  (simp (pf "r**q*r=r*r**q"))
;;  (use "Truth")
;;  (use "PosTimesComm")
;; ;; Assertion proved.
;; (assume "Assertion")
;; (simp "<-" "Assertion")
;; (simp "<-" "PosToNatPlus")
;; (use "Truth")
;; ;; Proof finished.

(ng #t)
(use "Truth")

;; Now we need to prove the 4 estimates cut in earlier.

;; ?^93:rht cd0<=f domr
(use "RatLeTrans" (pt "rht cd"))
;; rht cd0<=rht cd
(simp "d0-Def")
(use "RatLeTrans" (pt "(1#3)*(rht cd+rht cd+rht cd)"))
(ng #t)
(use "c<=d")
(simprat "<-" "RatThreeTimes")
(use "Truth")
(use "d<=b")

;; ?^90:f doml<=rht cd0
(simp "d0-Def")
(use "RatLeTrans" (pt "lft cd"))
(use "a<=c")
(use "RatLeTrans" (pt "(1#3)*(lft cd+lft cd+lft cd)"))
(simprat "<-" "RatThreeTimes")
(use "Truth")
(ng #t)
(use "RatLeMonPlus")
(ng #t)
(use "c<=d")
(use "c<=d")

;; ?^87:lft cd0<=f domr
(simp "c0-Def")
(use "RatLeTrans" (pt "(1#3)*(rht cd+rht cd+rht cd)"))
(ng #t)
(use "RatLeMonPlus")
(use "c<=d")
(use "c<=d")
(simprat "<-" "RatThreeTimes")
(ng #t)
(use "d<=b")

;; ?^84:f doml<=lft cd0
(simp "c0-Def")
(use "RatLeTrans" (pt "(1#3)*(lft cd+lft cd+lft cd)"))
(simprat "<-" "RatThreeTimes")
(ng #t)
(use "a<=c")
(ng #t)
(use "c<=d")

;; ?_13:exl cd0(
;;       lft cd0=(1#3)*(lft cd+lft cd+rht cd) andnc 
;;       rht cd0=(1#3)*(lft cd+rht cd+rht cd))

(intro 0 (pt "(1#3)*(lft cd+lft cd+rht cd) pair (1#3)*(lft cd+rht cd+rht cd)"))
(ng #t)
(split)
(use "Truth")
(use "Truth")

;; ?^10:lft cd<=rht cd
(use "CorrElim3Cor" (pt "f") (pt "p"))
(use "Corr f c d p")

;; (use "RatLeTrans" (pt "lft cd+(1#2**p)"))
;; (use "RatLeTrans" (pt "lft cd+0"))
;; (use "Truth")
;; (use "RatLeMonPlus")
;; (use "Truth")
;; (use "Truth")
;; (use "CorrElim3" (pt "f"))
;; (use "Corr f c d p")

;; ?^7:rht cd<=f domr
(use-with
 "CorrElim2" (pt "f") (pt "lft cd") (pt "rht cd") (pt "p") "Corr f c d p")

;; ?^4:f doml<=lft cd
(use-with
 "CorrElim1" (pt "f") (pt "lft cd") (pt "rht cd") (pt "p") "Corr f c d p")
;; Proof finished.
;; (cdp)
(save "IVTAux")

(define eterm (proof-to-extracted-term))
(define IVTAux-neterm (rename-variables (nt eterm)))
;; (ppc IVTAux-neterm)

;; [f,p,p0,cd]
;;  [let cd0
;;    ((1#3)*(lft cd+lft cd+rht cd)pair(1#3)*(lft cd+rht cd+rht cd))
;;    [case (cApproxSplitPos
;;           (RealConstr(f approx(lft cd0 max f doml min f domr))
;;            ([p1]f uMod(PosS p1)))
;;           (RealConstr(f approx(rht cd0 max f doml min f domr))
;;            ([p1]f uMod(PosS p1)))
;;           0
;;           (2+p0+p))
;;     (True -> lft cd pair rht cd0)
;;     (False -> lft cd0 pair rht cd)]]

(animate "Id") ;needed for add-sound since let is present
(add-sound "IVTAux")

;; ok, IVTAuxSound has been added as a new theorem:

;; allnc f,q(
;;  Cont f -> 
;;  f f doml<<=0 -> 
;;  0<<=f f domr -> 
;;  all c,d,p(f doml<=c -> d<=f domr -> c+(1#2**p)<=d ->
;;            RealLt(f c)(f d)(p+q)) -> 
;;  allnc p,cd(
;;   Corr f(lft cd)(rht cd)p -> 
;;   (ExLTMR (cterm (cd0) 
;;             Corr f(lft cd0)(rht cd0)(PosS p) andnc 
;;             lft cd<=lft cd0 andnc 
;;             rht cd0<=rht cd andnc rht cd0-lft cd0==(2#3)*(rht cd-lft cd)))
;;   (cIVTAux f q p cd)))

;; with computation rule

;; cIVTAux eqd
;; ([f,p,p0,cd]
;;   [if (cApproxSplitPos
;;         (RealConstr
;;          (f approx((1#3)*(lft cd+lft cd+rht cd)max f doml min f domr))
;;          ([p1]f uMod(PosS p1)))
;;         (RealConstr
;;          (f approx((1#3)*(lft cd+rht cd+rht cd)max f doml min f domr))
;;          ([p1]f uMod(PosS p1)))
;;         0
;;         (2+p0+p))
;;     (lft cd pair(1#3)*(lft cd+rht cd+rht cd))
;;     ((1#3)*(lft cd+lft cd+rht cd)pair rht cd)])

(deanimate "IVTAux")
(deanimate "Id")

;; IVTAuxSoundCor
(set-goal "allnc f,q(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 allnc c,d,p(
  f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
 allnc p,cd(
  Corr f(lft cd)(rht cd)p -> 
  exnc cd0(cd0 eqd cIVTAux f q p cd andnc
   Corr f(lft cd0)(rht cd0)(PosS p) andnc 
   lft cd<=lft cd0 andnc 
   rht cd0<=rht cd andnc rht cd0-lft cd0==(2#3)*(rht cd-lft cd))))")
(assume "f" "q" "Cf" "fa<=0" "0<=fb" "HypSlope" "p" "cd" "CorrHyp")
(intro 0 (pt "cIVTAux f q p cd"))
(split)
(use "InitEqD")
(use-with
 "ExLTMRElim" (py "rat yprod rat")
 (make-cterm (pv "cd0")
	     (pf "Corr f(lft cd0)(rht cd0)(PosS p) andnc 
            lft cd<=lft cd0 andnc 
            rht cd0<=rht cd andnc rht cd0-lft cd0==(2#3)*(rht cd-lft cd)"))
 (pt "cIVTAux f q p cd")
 "?")
(use "IVTAuxSound")
(auto)
;; Proof finished.
;; (cdp)
(save "IVTAuxSoundCor")

(add-var-name "xx" "yy" (py "alpha"))
(add-var-name "xxs" (py "nat=>alpha"))
(add-pvar-name "RR" (make-arity (py "nat") (py "alpha")))
(add-pvar-name "SS" (make-arity (py "nat") (py "alpha") (py "alpha")))
(add-var-name "g" (py "nat=>alpha=>alpha"))

;; DC
(set-goal "all xx0,g(
 RR^ Zero xx0 -> 
 all n,xx(RR^ n xx -> (RR^(Succ n)(g n xx) andnc SS^ n xx (g n xx))) -> 
 exl xxs(
  xxs Zero eqd xx0 andnc
  all n RR^ n(xxs n) andnc all n SS^ n(xxs n)(xxs(Succ n))))")
(assume "xx0" "g" "Init" "Step")
(intro 0 (pt "[n]((Rec nat=>alpha)n xx0 g)"))
(ng)
(split)
(use "InitEqD")
(assert "all xxs(all n xxs n eqd (Rec nat=>alpha)n xx0 g ->
 all n(RR^ n(xxs n) andnc RR^(n+1)(xxs(n+1)) andnc SS^ n(xxs n)(xxs(n+1))))")
(assume "xxs" "xxsDef")
(ind)
(split)
(simp "xxsDef")
(ng)
(use "Init")
;; 13
(split)
;; 16,17
(simp "xxsDef")
(ng)
(use "Step")
(use "Init")
;; 17
(simp "xxsDef")
(ng)
(simp "xxsDef")
(ng)
(use "Step")
(use "Init")
;; 11
(assume "n" "IH")
(split)
;; 27,28
(use "IH")
;; 28
(split)
(simp "xxsDef")
(ng)
(use "Step")
(simp "<-" "xxsDef")
(use "Step")
(use "IH")
;; 30
(simp "xxsDef")
(simp "xxsDef")
(ng)
(use "Step")
(simp "<-" "xxsDef")
(use "Step")
(use "IH")
;; Assertion proved.
(assume "Assertion")
(split)
(assume "n")
(use-with "Assertion" (pt "[n](Rec nat=>alpha)n xx0 g") "?" (pt "n") 'left)
(assume "n1")
(use "InitEqD")
;; 44
(assume "n")
(use-with "Assertion"
	  (pt "[n](Rec nat=>alpha)n xx0 g") "?" (pt "n") 'right 'right)
(assume "n1")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "DC")

(define eterm (proof-to-extracted-term))
(define DC-neterm (rename-variables (nt eterm)))
(pp DC-neterm)
;; [xx,g,n](Rec nat=>alpha)n xx g

(add-sound "DC")

;; ok, DCSound has been added as a new theorem:

;; allnc xx,g(
;;  RR^ Zero xx -> 
;;  all n,xx0(RR^ n xx0 -> RR^(Succ n)(g n xx0) andnc SS^ n xx0(g n xx0)) -> 
;;  (ExLTMR (cterm (xxs) 
;;            xxs Zero eqd xx andnc 
;;            all n RR^ n(xxs n) andnc all n SS^ n(xxs n)(xxs(Succ n))))
;;  ((cDC alpha)xx g))

;; with computation rule

;; (cDC alpha)eqd([xx,g,n](Rec nat=>alpha)n xx g)

;; We do not deanimate DC since the extracted term is short.

(add-var-name "cds" (py "nat=>rat yprod rat"))

;; IVTcds
(set-goal "all f,q,p0(
     Cont f -> 
     f f doml<<=0 -> 
     0<<=f f domr -> 
     f doml+(1#2**p0)<=f domr -> 
     all c,d,p(
      f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
     exl cds(
      cds Zero eqd(f doml pair f domr) andnc 
      all n Corr f(lft(cds n))(rht(cds n))(NatToPos(p0+n)) andnc 
      all n(
       lft(cds n)<=lft(cds(Succ n)) andnc 
       rht(cds(Succ n))<=rht(cds n) andnc 
       rht(cds(Succ n))-lft(cds(Succ n))==(2#3)*(rht(cds n)-lft(cds n)))))")
(assume "f" "q" "p0" "Cont f" "f a<<=0" "0<<=f b" "a <_p0 b" "HypSlope")
(use-with
 "DC"
 (py "rat yprod rat")
 (make-cterm (pv "n") (pv "cd") (pf "Corr f(lft cd)(rht cd)(NatToPos(p0+n))"))
 (make-cterm (pv "n") (pv "cd") (pv "cd1")
	     (pf "lft cd<=lft cd1 andnc rht cd1<=rht cd andnc
                  rht cd1-lft cd1==(2#3)*(rht cd-lft cd)"))
 (pt "f doml pair f domr")
 (pt "[n,cd]cIVTAux f q(NatToPos(p0+n))cd")
 ;; (pt "[n,cd]cIVTAux f q p0 cd")
 "?" "?")
;; Corr f(lft(f doml pair f domr))(rht(f doml pair f domr))(NatToPos(p0+Zero))
(use "CorrIntro")
(use "Truth")
(use "Truth")
(simp "NatPlus0CompRule")
(simp "NatToPosToNatId")
(use "a <_p0 b")
(use "f a<<=0")
(use "0<<=f b")

;; Now the step hypothesis, to be proved by means of IVTAux
(assume "n" "cd" "Corr-Hyp")
(simp "NatToPosNatPlusSucc")
;; (split)
(inst-with-to
 "IVTAuxSoundCor"
 (pt "f") (pt "q") "Cont f" "f a<<=0" "0<<=f b" "HypSlope"
 (pt "NatToPos(p0+n)") (pt "cd")
 "Corr-Hyp"
 "Inst")
(by-assume "Inst" "cd0" "cd0Prop")
(assert "cd0 eqd cIVTAux f q(NatToPos(p0+n))cd")
 (use "cd0Prop")
(assume "cd0Def")
(simp (pf "([n0,cd0]cIVTAux f q(NatToPos(p0+n0))cd0)n cd eqd
           cIVTAux f q(NatToPos(p0+n))cd"))
(simp "<-" "cd0Def")
(use "cd0Prop")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "IVTcds")

(define eterm (proof-to-extracted-term)) 
(define IVTcds-neterm (rename-variables (nt eterm)))
(pp IVTcds-neterm)

;; [f,p,p0,n]
;;  (Rec nat=>rat yprod rat)n(f doml pair f domr)
;;  ([n0]
;;    cIVTAux f p
;;    [if (NatEven(p0+n0))
;;      (SZero
;;      ((GRecGuard nat pos)([n1]n1)(NatHalf(p0+n0))
;;       ([n1,(nat=>pos)]
;;         [if (NatEven n1)
;;           (SZero((nat=>pos)(NatHalf n1)))
;;           [if (n1=Succ Zero) 1 (SOne((nat=>pos)(NatHalf n1)))]])
;;       (NatHalf(p0+n0)<p0+n0)))
;;      [if (p0+n0=Succ Zero)
;;       1
;;       (SOne
;;       ((GRecGuard nat pos)([n1]n1)(NatHalf(p0+n0))
;;        ([n1,(nat=>pos)]
;;          [if (NatEven n1)
;;            (SZero((nat=>pos)(NatHalf n1)))
;;            [if (n1=Succ Zero) 1 (SOne((nat=>pos)(NatHalf n1)))]])
;;        (NatHalf(p0+n0)<p0+n0)))]])

;; Might be shortened with cPosSNatToPos, for
;; PosSNatToPos
;; (set-goal "all p exl p1 p1 eqd PosS(NatToPos p))")
;; Postponed.

;; (pp "IVTcds")

(add-sound "IVTcds")

;; ok, IVTcdsSound has been added as a new theorem:

;; allnc f,q,p(
;;  Cont f -> 
;;  f f doml<<=0 -> 
;;  0<<=f f domr -> 
;;  f doml+(1#2**p)<=f domr -> 
;;  all c,d,p0(
;;   f doml<=c -> d<=f domr -> c+(1#2**p0)<=d -> RealLt(f c)(f d)(p0+q)) -> 
;;  (ExLTMR (cterm (cds) 
;;            cds Zero eqd(f doml pair f domr) andnc 
;;            all n Corr f(lft(cds n))(rht(cds n))(NatToPos(p+n)) andnc 
;;            all n(
;;             lft(cds n)<=lft(cds(Succ n)) andnc 
;;             rht(cds(Succ n))<=rht(cds n) andnc 
;;             rht(cds(Succ n))-lft(cds(Succ n))==
;;              (2#3)*(rht(cds n)-lft(cds n)))))
;;  (cIVTcds f q p))

;; with computation rule

;; cIVTcds eqd
;; ([f,p,p0,n]
;;   (Rec nat=>rat yprod rat)n(f doml pair f domr)
;;   ([n0]
;;     cIVTAux f p
;;     [if (NatEven(p0+n0))
;;       (SZero
;;       ((GRecGuard nat pos)([n1]n1)(NatHalf(p0+n0))
;;        ([n1,(nat=>pos)]
;;          [if (NatEven n1)
;;            (SZero((nat=>pos)(NatHalf n1)))
;;            [if (n1=Succ Zero) 1 (SOne((nat=>pos)(NatHalf n1)))]])
;;        (NatHalf(p0+n0)<p0+n0)))
;;       [if (p0+n0=Succ Zero)
;;        1
;;        (SOne
;;        ((GRecGuard nat pos)([n1]n1)(NatHalf(p0+n0))
;;         ([n1,(nat=>pos)]
;;           [if (NatEven n1)
;;             (SZero((nat=>pos)(NatHalf n1)))
;;             [if (n1=Succ Zero) 1 (SOne((nat=>pos)(NatHalf n1)))]])
;;         (NatHalf(p0+n0)<p0+n0)))]]))

(deanimate "IVTcds")

;; We now prove that [p]lft(cds n+p) increases.

;; IVTLeftIncr
(set-goal "all f,q,p0(
     Cont f -> 
     f f doml<<=0 -> 
     0<<=f f domr -> 
     f doml+(1#2**p0)<=f domr -> 
     all c,d,p(
      f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
     all cds(
      cds Zero eqd(f doml pair f domr) andnc 
      all n Corr f(lft(cds n))(rht(cds n))(NatToPos(p0+n)) andnc 
      all n(
       lft(cds n)<=lft(cds(Succ n)) andnc 
       rht(cds(Succ n))<=rht(cds n) andnc 
       rht(cds(Succ n))-lft(cds(Succ n))==(2#3)*(rht(cds n)-lft(cds n))) -> 
      all n,m lft(cds n)<=lft(cds(n+m))))")
(assume "f" "q" "p0" "Cont f" "f a<<=0" "0<<=f b" "a <_p0 b" "HypSlope"
	"cds" "Hcds" "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "RatLeTrans" (pt "lft(cds(n+m))"))
(use "IH")
(use "Hcds")
;; Proof finished.
;; (cdp)
(save "IVTLeftIncr")

;; The corresponding proof of d(n+p)<=dn:

;; IVTRightDecr
(set-goal "all cds(
 all n rht(cds(Succ n))<=rht(cds n) -> 
 all n,m rht(cds(n+m))<=rht(cds n))")
(assume "cds" "Step" "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "RatLeTrans" (pt "rht(cds(n+m))"))
(auto)
;; Proof finished.
;; (cdp)
(save "IVTRightDecr")

;; IVTDiff
(set-goal "all f,cds(
 cds Zero eqd(f doml pair f domr) -> 
 all n rht(cds(Succ n))-lft(cds(Succ n))==
       (2#3)*(rht(cds n)-lft(cds n)) -> 
 all n rht(cds n)-lft(cds n)==(2#3)**n*(f domr-f doml))")
(assume "f" "cds" "EqZero" "Step")
(ind)
  (simp "EqZero")
  (use "Truth")
(assume "n" "IH")
(simprat "Step")
(simprat "IH")
(simprat "RatExpSucc")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IVTDiff")

;; Proof that (lft(cds n)) is a Cauchy sequence with modulus 2*(n+p)

;; TwoThirdExpNatZeroSeq
(set-goal "all p exl n (2#3)**n<=(1#2**p)")
;; For both step cases of the induction on p we need
(assert "all n,p((2#3)**n<=(1#2**p) -> (2#3)**(n+n)<=(1#2**SZero p))")
 (assume "n" "p" "nProp")
 (simprat "RatExpNatPlus")
 (use "RatLeTrans" (pt "(1#2**p)*(1#2**p)"))
 (use "RatLeMonTimesTwo")
 (use "Truth")
 (use "Truth")
 (use "nProp")
 (use "nProp")
 (ng)
 (simp "<-" "NatDoublePlusEq")
 (simp "PosExpTwoPosPlus")
 (use "NatLeMonTwoExp")
 (simp "PosToNatPlus")
 (use "Truth")
;; Assertion proved
(assume "Assertion")
(ind)
;; Base
(intro 0 (pt "Succ(Succ Zero)"))
(use "Truth")
;; Step SZero
(assume "p" "IH")
(by-assume "IH" "n" "nProp")
(intro 0 (pt "n+n"))
(use "Assertion")
(use "nProp")
;; Step SOne
(assume "p" "IH")
(by-assume "IH" "n" "nProp")
(simp (pf "SOne p=SZero p+1"))
(intro 0 (pt "n+n+2"))

(simprat "RatExpNatPlus")
(use "RatLeTrans" (pt "(4#9)*(2#3)**(n+n)"))
(use "RatLeMonTimes")
(use "Truth")
(use "Truth")
(simp (pf "(4#9)=(2#3)**2"))

(simp (pf "(1#2**(SZero p+1))=(1#2)*(1#2**SZero p)"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Assertion")
(use "nProp")
(ng)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "TwoThirdExpNatZeroSeq")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [p](Rec pos=>nat)p(Succ(Succ Zero))([p0,n]n+n)([p0,n]Succ(Succ(n+n)))

(add-sound "TwoThirdExpNatZeroSeq")

;; ok, TwoThirdExpNatZeroSeqSound has been added as a new theorem:

;; allnc p (ExLTMR (cterm (n) (2#3)**n<=(1#2**p)))(cTwoThirdExpNatZeroSeq p)

;; with computation rule

;; cTwoThirdExpNatZeroSeq eqd
;; ([p](Rec pos=>nat)p(Succ(Succ Zero))([p0,n]n+n)([p0,n]Succ(Succ(n+n))))

(deanimate "TwoThirdExpNatZeroSeq")

;; Alternative with explicit content

(add-program-constant "TwoThirdExpBd" (py "pos=>nat"))
;; (remove-program-constant "TwoThirdExpBd")

(add-computation-rules
 "TwoThirdExpBd One" "Succ(Succ Zero)"
 "TwoThirdExpBd(SZero p)" "NatDouble(TwoThirdExpBd p)"
 "TwoThirdExpBd(SOne p)" "NatDouble(TwoThirdExpBd p)+2")

(set-goal "all p TwoThirdExpBd p=2*p")
(ind)
(use "Truth")
(assume "p" "IHEven")
(ng)
(simp "IHEven")
(use "Truth")
(assume "p" "IHOdd")
(ng)
(simp "IHOdd")
(use "Truth")
;; Proof finished.

;; TwoThirdExpBdTotal
(set-totality-goal "TwoThirdExpBd")
(fold-alltotal)
(ind)
;; Base
(ng)
(use "NatTotalVar")
;; 4
(assume "p" "IH")
(ng #t)
(use "NatDoubleTotal")
(use "IH")
;; 5
(assume "p" "IH")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatSucc")
(use "NatDoubleTotal")
(use "IH")
;; Proof finished.
(save-totality)

;; TwoThirdExpNatZeroSeqNc
(set-goal "all p (2#3)**TwoThirdExpBd p<=(1#2**p)")
(assert "all n,p((2#3)**n<=(1#2**p) -> (2#3)**NatDouble n<=(1#2**SZero p))")
 (assume "n" "p" "nProp")
 (simp "<-" "NatDoublePlusEq")
 (simprat "RatExpNatPlus")
 (use "RatLeTrans" (pt "(1#2**p)*(1#2**p)"))
 (use "RatLeMonTimesTwo")
 (use "Truth")
 (use "Truth")
 (use "nProp")
 (use "nProp")
 (ng)
 (simp "<-" "NatDoublePlusEq")
 (simp "PosExpTwoPosPlus")
 (use "NatLeMonTwoExp")
 (simp "PosToNatPlus")
 (use "Truth")
;; Assertion proved
(assume "Assertion")
(ind)
(use "Truth")
;; 3
(assume "p" "IH")
(ng #t)
(use "Assertion")
(use "IH")
;; 21
;; Step SOne
(assume "p" "IH")
(simp "TwoThirdExpBd2CompRule")
;;  Assertion:all n,p((2#3)**n<=(1#2**p) -> (2#3)**NatDouble n<=(1#2**SZero p))
;;   p50286  p  IH:(2#3)**TwoThirdExpBd p<=(1#2**p)
;; -----------------------------------------------------------------------------
;; ?^26:(2#3)**Succ(Succ(NatDouble(TwoThirdExpBd p)))<=(1#2**SOne p)

(simp (pf "SOne p=SZero p+1"))
(simprat "RatExpNatPlus")
(use "RatLeTrans" (pt "(4#9)*(2#3)**NatDouble(TwoThirdExpBd p)"))
(use "RatLeMonTimes")
(use "Truth")
(use "Truth")
(simp (pf "(4#9)=(2#3)**2"))

(simp (pf "(1#2**(SZero p+1))=(1#2)*(1#2**SZero p)"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Assertion")
(use "IH")
(ng)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "TwoThirdExpNatZeroSeqNc")

;; Later in IVTRealLeft we will need monotonicity of TwoThirdExpBd

;; TwoThirdExpBdChar
(set-goal "all p TwoThirdExpBd p=NatDouble(PosToNat p)")
(ind)
(use "Truth")
(assume "p" "IH")
(ng)
(simp "IH")
(use "Truth")
(assume "p" "IH")
(ng)
(simp "IH")
(use "Truth")
;; Proof finished.
(save "TwoThirdExpBdChar")

;; TwoThirdExpBdMon
(set-goal "all p,q(p<=q -> TwoThirdExpBd p<=TwoThirdExpBd q)")
(assume "p" "q" "p<=q")
(simp "TwoThirdExpBdChar")
(simp "TwoThirdExpBdChar")
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "p<=q")
;; Proof finished.
(save "TwoThirdExpBdMon")

;; We will need a general criterion for Cauchyness, in order to avoid
;; doing a symmetric argument twice, in a concrete case.  To be called
;; CauchyCrit.

;; CauchyCrit
(set-goal "all as,M(all p,n,m(M p<=n -> n<=m -> abs(as n-as m)<=(1#2**p)) ->
                    Cauchy as M)")
(assume "as" "M" "Hyp")
(use "CauchyIntro")

;; ?^3:all p,n,m(M p<=n -> M p<=m -> abs(as n+ ~(as m))<=(1#2**p))
(assume "p" "n" "m" "M p<=n" "M p<=m")
(use "NatLeLin" (pt "n") (pt "m"))

;; n<=m -> abs(as n-as m)<=(1#2**p)
(assume "n<=m")
(auto)

;; m<=n -> abs(as n-as m)<=(1#2**p)
(assume "m<=n")
(simp "<-" "RatAbs0RewRule")
(ng #t)
(simp "RatPlusComm")
(use "Hyp")
(use "M p<=m")
(use "m<=n")
;; Proof finished.
;; (cdp)
(save "CauchyCrit")

;; Now the Cauchy modulus.

;; IVTRealLeft
(set-goal 
 "all a,b,p1(0<=b-a ->
 b-a<=2**p1 -> 
 all cds(
  all n,m(n<=m -> lft(cds n)<=lft(cds m)) -> 
  all n,m(n<=m -> rht(cds m)<=rht(cds n)) -> 
  all n lft(cds n)<=rht(cds n) -> 
  all n rht(cds n)-lft(cds n)==(2#3)**n*(b-a) -> 
  Real(RealConstr([n]lft(cds n))([p]TwoThirdExpBd(p+p1)))))")
(assume
 "a" "b" "p1" "0<=b-a" "b-a<=2**p1" "cds" "cIncr" "dDecr" "cs<=ds" "cdDiff")
(use "RealIntro")
;; 3,4
;; Cauchyness
(use "CauchyCrit")
(ng #t)
;; ?^6:all p,n,m(
;;      TwoThirdExpBd(p+p1)<=n -> 
;;      n<=m -> abs(lft(cds n)+ ~lft(cds m))<=(1#2**p))

;; ?^6:all p,n,m(
;;      cTwoThirdExpNatZeroSeq(p+p1)<=n -> 
;;      n<=m -> abs(lft(cds n)+ ~lft(cds m))<=(1#2**p))
(assume "p" "n" "m" "MBd" "n<=m")

;; abs(lft(cds n)-lft(cds m))<=(1#2**p)
(simprat (pf "abs(lft(cds n)-lft(cds m))==lft(cds m)-lft(cds n)"))

;; ?^8:lft(cds m)+ ~lft(cds n)<=(1#2**p)
(use "RatLeTrans" (pt "rht(cds n)-lft(cds n)"))
(ng #t)
(use "RatLeTrans" (pt "rht(cds m)"))
(use "cs<=ds")
(use "dDecr")
(use "n<=m")
(simprat "cdDiff")
(simprat (pf "(1#2**p)==(1#2**(p+p1))*2**p1"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "0<=b-a")

;;   a  b  p1  0<=b-a:0<=b-a
;;   b-a<=2**p1:b-a<=2**p1
;;   cds  cIncr:all n,m(n<=m -> lft(cds n)<=lft(cds m))
;;   dDecr:all n,m(n<=m -> rht(cds m)<=rht(cds n))
;;   cs<=ds:all n lft(cds n)<=rht(cds n)
;;   cdDiff:all n rht(cds n)-lft(cds n)=(2#3)**n*(b-a)
;;   p  n  m  Mp<=n:TwoThirdExpBd(p+p1)<=n
;;   n<=m:n<=m
;; ---------------------------------------------------------------------------
;; ?^21:(2#3)**n<=(1#2**(p+p1))

;; (pp "TwoThirdExpNatZeroSeq")
;; (pp "TwoThirdExpNatZeroSeqNc")
;; all p (2#3)**TwoThirdExpBd p<=(1#2**p)
(use "RatLeTrans" (pt "(2#3)**TwoThirdExpBd(p+p1)"))
(use "RatLeMonExpDecr")
(use "Truth")
(use "Truth")
(use "MBd")
(use "TwoThirdExpNatZeroSeqNc")
(use "b-a<=2**p1")
;; ?^18:(1#2**p)==(1#2**(p+p1))*2**p1
(simp "PosPlusComm")
(ng #t)
(simp "PosExpTwoPosPlus")
(use "Truth")
;; ?^9:abs(lft(cds n)-lft(cds m))==lft(cds m)-lft(cds n)
(ng #t)
(simp (pf "abs(lft(cds n)+ ~lft(cds m))=abs~(lft(cds n)+ ~lft(cds m))"))
(ng #t)
(simp "RatPlusComm")
(simp "RatAbsId")
(use "Truth")
(use "RatLeTrans" (pt "0+lft(cds n)+ ~lft(cds n)"))
(simprat "RatEqvPlusMinusRev")
(use "Truth")
(ng #t)
(use "cIncr")
(use "n<=m")
(simp "RatAbs0RewRule")
(use "Truth")
;; ?^4:Mon((RealConstr([n]lft(cds n))([p]TwoThirdExpBd(p+p1)))mod)
(ng #t)
;; ?^44:Mon([p]TwoThirdExpBd(p+p1))
(use "MonIntro")
(ng #t)
;; ?^46:all p,q(p<=q -> TwoThirdExpBd(p+p1)<=TwoThirdExpBd(q+p1))
(assume "p" "q" "p<=q")
(assert "p+p1<=q+p1")
(use "PosLeMonPlus")
(use "p<=q")
(use "Truth")
(use "TwoThirdExpBdMon")
;; Proof finished.
;; (cdp)
(save "IVTRealLeft")

;; The final goal, split into parts:
;; f domr-f doml<=2**p should be f domr<=2**p+f doml

;; IVTFinalRealLeft
(set-goal "all f,q,p(
     Cont f -> 
     f f doml<<=0 -> 
     0<<=f f domr -> 
     f doml+(1#2**p)<=f domr -> 
     f domr-f doml<=2**p ->
     all c,d,p(
      f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
     all cds(
      cds Zero eqd(f doml pair f domr) ->
      all n Corr f(lft(cds n))(rht(cds n))(NatToPos(p+n)) ->
      all n(lft(cds n)<=lft(cds(Succ n))) ->
      all n(rht(cds(Succ n))<=rht(cds n)) ->
      all n(
       rht(cds(Succ n))-lft(cds(Succ n))==(2#3)*(rht(cds n)-lft(cds n))) ->
      Real(RealConstr([n]lft(cds n))([p0]TwoThirdExpBd(p0+p)))))")
(assume "f" "q" "p" "Cont f" "f a<<=0" "0<<=f b" "a <_p b" "b-a<=2**p" 
	"HypSlope" "cds"
	"cdsProp1" "cdsProp2" "cdsProp3" "cdsProp4" "cdsProp5")
(use "IVTRealLeft" (pt "f doml") (pt "f domr"))

;; ?^3:0<=f domr-f doml
(use "RatLeTrans" (pt "f doml+(1#2**p)-f doml"))
(simp "RatPlusComm")
(ng #t)
(simprat "RatEqvPlusMinusRev")
(use "Truth")
(ng #t)
(use "a <_p b")
;; ?^4:f domr-f doml<=2**p
(use "b-a<=2**p")
;; ?^5:all n,m(n<=m -> lft(cds n)<=lft(cds m))
(assume "n" "m" "n<=m")
(simp (pf "m=n+(m--n)"))
(use "IVTLeftIncr" (pt "f") (pt "q") (pt "p"))
(auto)
(split)
(auto)
(split)
(auto)
(assume "n1")
(split)
(auto)
(split)
(auto)
(simp "NatPlusMinus")
(simp "<-" "NatMinusPlus")
(use "Truth")
(use "Truth")
(use "n<=m")
;; ?^6:all n,m(n<=m -> rht(cds m)<=rht(cds n))
(assume "n" "m" "n<=m")
(simp (pf "m=n+(m--n)"))
(use "IVTRightDecr")
(use "cdsProp4")
(simp "NatPlusMinus")
(simp "<-" "NatMinusPlus")
(use "Truth")
(use "Truth")
(use "n<=m")
;; ?^7:all n lft(cds n)<=rht(cds n)
(assume "n")
(use "CorrElim3Cor" (pt "f") (pt "(NatToPos(p+n))"))
(use "cdsProp2")
;; ?^8:all n rht(cds n)-lft(cds n)=(2#3)**n*(f domr-f doml)
(use "IVTDiff")
(use "cdsProp1")
(use "cdsProp5")
;; Proof finished.
;; (cdp)
(save "IVTFinalRealLeft")

;; IVTRealAppLeft probably has many unnecessary hypotheses.
;; Essentially IVTFinalRealLeft should suffice.
;; f domr-f doml<=2**p should be f domr<=2**p+f doml

;; IVTRealAppLeft
(set-goal 
 "all f,q,p(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 f doml+(1#2**p)<=f domr -> 
 f domr-f doml<=2**p -> 
 all c,d,p(f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
 all cds(
  cds Zero eqd(f doml pair f domr) -> 
  all n Corr f(lft(cds n))(rht(cds n))(NatToPos(p+n)) -> 
  all n lft(cds n)<=lft(cds(Succ n)) -> 
  all n rht(cds(Succ n))<=rht(cds n) -> 
  all n rht(cds(Succ n))-lft(cds(Succ n))==(2#3)*(rht(cds n)-lft(cds n)) -> 
  Real(f(RealConstr([n]lft(cds n))([p0](TwoThirdExpBd(p0+p)))))))")
(assume "f" "q" "p" "Cont f" "f a<<=0" "0<<=f b"
	"a <_p b" "b-a<=2**p" "HypSlope" 
        "cds" "cdsProp1" "cdsProp2" "cdsProp3" "cdsProp4" "cdsProp5")
;; (add-global-assumption
;;  "ContAppReal"
;;  "all f,x(Cont f -> Real x -> 
;;           all n f doml<=x seq n -> all n x seq n<=f domr -> Real(f x))")
(use "ContReal")
(use "Cont f")
;; ?^4:f doml<=f domr
(use "RatLeTrans" (pt "f doml+(1#2**p)"))
(use "RatLeTrans" (pt "f doml+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "a <_p b")
;; ?^5:Real(RealConstr([n]lft(cds n))([p0]TwoThirdExpBd(p0+p)))
;; (pp "IVTFinalRealLeft")
(use "IVTFinalRealLeft" (pt "f") (pt "q"))
(use "Cont f")
(use "f a<<=0")
(use "0<<=f b")
(use "a <_p b")
(use "b-a<=2**p")
(use "HypSlope")
(use "cdsProp1")
(use "cdsProp2")
(use "cdsProp3")
(use "cdsProp4")
(use "cdsProp5")
;; Proof finished.
;; (cdp)
(save "IVTRealAppLeft")

;; LeContAppZero
(set-goal "all f,x(Cont f -> Real x -> all m f(x seq m)<<=0 ->
 all n f doml<=x seq n ->
 all n x seq n<=f domr ->
 f x<<=0)")
(assume "f" "x" "Cf" "Rx" "LeZeroHyp" "LBd" "UBd")
(use "RealLeChar2RealConstrFree")
(use "ContReal")
(use "Cf")
(use "RatLeTrans" (pt "x seq Zero"))
(use "LBd")
(use "UBd")
(use "Rx")
(use "RealRat")
;; ?^5:all p exnc n all n0(n<=n0 -> (f x)seq n0<=0 seq n0+(1#2**p))
(assume "p")
(assert "exi m m=x mod(PosPred(f uModCont(PosS p)))")
 (intro 0 (pt "x mod(PosPred(f uModCont(PosS p)))"))
 (use "Truth")
(assume "mEx")
(by-assume "mEx" "m" "mDef")
(inst-with-to "LeZeroHyp" (pt "m") "LeZeroHypInst")
(inst-with-to "RealLeChar1RealConstrFree"
	      (pt "f(x seq m)")
	      (pt "RealConstr([n](0#1))([p]Zero)")
	      "Inst")
(inst-with-to "Inst" "LeZeroHypInst" "AllExProp")
(inst-with-to "AllExProp" (pt "PosS p") "ExHyp")
(drop "LeZeroHyp" "Inst" "LeZeroHypInst" "AllExProp")
(by-assume "ExHyp" "n1" "n1Prop")
(assert "exi n n=n1 max m max f uMod(PosS p)")
 (intro 0 (pt "n1 max m max f uMod(PosS p)"))
 (use "Truth")
(assume "nEx")
(by-assume "nEx" "n" "nDef")
(intro 0 (pt "n"))
(assume "n0" "n<=n0")
;;   f  x  Cf:Cont f
;;   Rx:Real x
;;   LBd:all n f doml<=x seq n
;;   UBd:all n x seq n<=f domr
;;   p  m  mDef:m=x mod(PosPred(f uModCont(PosS p)))
;;   n1  n1Prop:all n(n1<=n -> (f(x seq m))seq n<=0 seq n+(1#2**PosS p))
;;   n  nDef:n=n1 max m max f uMod(PosS p)
;;   n0  n<=n0:n<=n0
;; -----------------------------------------------------------------------------
;; ?^39:(f x)seq n0<=0 seq n0+(1#2**p)

(ng #t)
(simp "RatMaxMinEq")
;;   f  x  Cf:Cont f
;;   Rx:Real x
;;   LBd:all n f doml<=x seq n
;;   UBd:all n x seq n<=f domr
;;   p  m  mDef:m=x mod(PosPred(f uModCont(PosS p)))
;;   n1  n1Prop:all n(n1<=n -> (f(x seq m))seq n<=0 seq n+(1#2**PosS p))
;;   n  nDef:n=n1 max m max f uMod(PosS p)
;;   n0  n<=n0:n<=n0
;; -----------------------------------------------------------------------------
;; ?^41:f approx(x seq n0)n0<=(1#2**p)
(simprat (pf "f approx(x seq n0)n0==
 f approx(x seq n0)n0+ ~(f approx(x seq m)n0)+(f approx(x seq m)n0)"))
(get 45)
(simprat "RatEqvPlusMinus")
(use "Truth")
;; 44
(use "RatLeTrans" (pt "(1#2**PosS p)+(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "RatLeTrans" (pt "abs(f approx(x seq n0)n0+ ~(f approx(x seq m)n0))"))
(use "Truth")
;; ?^52:abs(f approx(x seq n0)n0+ ~(f approx(x seq m)n0))<=(1#2**PosS p)
(use "ContElim2")
(use "Cf")
(use "LBd")
(use "UBd")
(use "LBd")
(use "UBd")
(use "NatLeTrans" (pt "n"))
(simp "nDef")
(use "NatMaxUB2")
(use "n<=n0")
;; ?^59:abs(x seq n0-x seq m)<=(1#2**PosPred(f uModCont(PosS p)))
(use "CauchyElim" (pt "x mod"))
(use "RealToCauchy")
(use "Rx")
(simp "<-" "mDef")
(use "NatLeTrans" (pt "n"))
(simp "nDef")
(use "NatLeTrans" (pt "n1 max m"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "n<=n0")
(simp "<-" "mDef")
(use "Truth")
;; ?^50:f approx(x seq m)n0<=(1#2**PosS p)
(ng "n1Prop")
(assert "n1<=n0")
 (use "NatLeTrans" (pt "n"))
 (simp "nDef")
 (use "NatLeTrans" (pt "n1 max m"))
 (use "NatMaxUB1")
 (use "NatMaxUB1")
 (use "n<=n0")
;; Assertion proved.
(assume "n1<=n0")
(assert "f approx(x seq m max f doml min f domr)n0<=(1#2**PosS p)")
(use "n1Prop")
(use "n1<=n0")
(simp "RatMaxMinEq")
(assume "Hyp")
(use "Hyp")
(use "UBd")
(use "LBd")
;; ?^48:(1#2**PosS p)+(1#2**PosS p)<=(1#2**p)
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "UBd")
(use "LBd")
;; Proof finished.
;; (cdp)
(save "LeContAppZero")

;; We will also need

;; LeZeroContApp
(set-goal "all f,x(Cont f -> Real x -> all m 0<<=f(x seq m) ->
 all n f doml<=x seq n ->
 all n x seq n<=f domr ->
 0<<=f x)")
(assume "f" "x" "Cf" "Rx" "ZeroLeHyp" "LBd" "UBd")
(use "RealLeChar2RealConstrFree")
(use "RealRat")
(use "ContReal")
(use "Cf")
(use "RatLeTrans" (pt "x seq Zero"))
(use "LBd")
(use "UBd")
(use "Rx")
;; ?^5:all p exnc n all n0(n<=n0 -> 0 seq n0<=(f x)seq n0+(1#2**p))
(assume "p")
(assert "exi m m=x mod(PosPred(f uModCont(PosS p)))")
 (intro 0 (pt "x mod(PosPred(f uModCont(PosS p)))"))
 (use "Truth")
(assume "mEx")
(by-assume "mEx" "m" "mDef")
(inst-with-to "ZeroLeHyp" (pt "m") "ZeroLeHypInst")
(inst-with-to "RealLeChar1RealConstrFree"
	      (pt "RealConstr([n](0#1))([p]Zero)")
	      (pt "f(x seq m)")
	      "Inst")
(inst-with-to "Inst" "ZeroLeHypInst" "AllExProp")
(inst-with-to "AllExProp" (pt "PosS p") "ExHyp")
(drop "ZeroLeHyp" "Inst" "ZeroLeHypInst" "AllExProp")
(by-assume "ExHyp" "n1" "n1Prop")
(assert "exi n n=n1 max m max f uMod(PosS p)")
 (intro 0 (pt "n1 max m max f uMod(PosS p)"))
 (use "Truth")
(assume "nEx")
(by-assume "nEx" "n" "nDef")
(intro 0 (pt "n"))
(assume "n0" "n<=n0")
;; ?^39:0 seq n0<=(f x)seq n0+(1#2**p)
(ng #t)
;; ?^40:0<=f approx(x seq n0 max f doml min f domr)n0+(1#2**p)
(simp "RatMaxMinEq")
;; ?^41:0<=f approx(x seq n0)n0+(1#2**p)
(simprat (pf "f approx(x seq n0)n0==
 f approx(x seq n0)n0+ ~(f approx(x seq m)n0)+(f approx(x seq m)n0)"))
(get 45)
(simprat "RatEqvPlusMinus")
(use "Truth")
;; ?^44:0<=f approx(x seq n0)n0+ ~(f approx(x seq m)n0)+f approx(x seq m)n0+
;;         (1#2**p)
(simprat (pf "0== ~((1#2**PosS p)+(1#2**PosS p))+(1#2**p)"))
(simp "RatLe3RewRule")
(simp "RatUMinus2RewRule")
(use "RatLeMonPlus")
;; 51,52
;; ?^51:~(1#2**PosS p)<=f approx(x seq n0)n0+ ~(f approx(x seq m)n0)
(assert "all a,b(abs a<=b -> ~b<=a)")
 (assume "a" "b" "abs a<=b")
 (simp (pf "a= ~ ~ a"))
 (simp "RatLe7RewRule")
 (use "RatLeTrans" (pt "abs ~a"))
 (simp "RatLe8RewRule")
 (use "Truth")
 (use "abs a<=b")
 (use "Truth")
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
;; ?^63:abs(f approx(x seq n0)n0+ ~(f approx(x seq m)n0))<=(1#2**PosS p)
;; this was goal 52 above
(use "ContElim2")
(use "Cf")
(use "LBd")
(use "UBd")
(use "LBd")
(use "UBd")
(use "NatLeTrans" (pt "n"))
(simp "nDef")
(use "NatMaxUB2")
(use "n<=n0")
;; ?^70:abs(x seq n0-x seq m)<=(1#2**PosPred(f uModCont(PosS p)))
;; This was goal 59 above
(use "CauchyElim" (pt "x mod"))
(use "RealToCauchy")
(use "Rx")
(simp "<-" "mDef")
(use "NatLeTrans" (pt "n"))
(simp "nDef")
(use "NatLeTrans" (pt "n1 max m"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "n<=n0")
(simp "<-" "mDef")
(use "Truth")
;; ?^52:~(1#2**PosS p)<=f approx(x seq m)n0
;; this si similar to goal 50 above
(ng "n1Prop")
(assert "n1<=n0")
 (use "NatLeTrans" (pt "n"))
 (simp "nDef")
 (use "NatLeTrans" (pt "n1 max m"))
 (use "NatMaxUB1")
 (use "NatMaxUB1")
 (use "n<=n0")
;; Assertion proved.
(assume "n1<=n0")
(assert "0<=f approx(x seq m max f doml min f domr)n0+(1#2**PosS p)")
(use "n1Prop")
(use "n1<=n0")
(simp "RatMaxMinEq")
(assume "Hyp")
(assert "all a,b(0<=a+b -> ~b<=a)")
 (assume "a" "b" "0<=a+b")
 (use "RatLeTrans" (pt "0+ ~b"))
 (use "Truth")
 (use "RatLeTrans" (pt "a+b+ ~b"))
 (use "RatLeMonPlus")
 (use "0<=a+b")
 (use "Truth")
 (simprat "RatEqvPlusMinusRev")
 (use "Truth")
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(use "Hyp")
(use "UBd")
(use "LBd")
;; ?^48:0== ~((1#2**PosS p)+(1#2**PosS p))+(1#2**p)
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "UBd")
(use "LBd")
;; Proof finished.
;; (cdp)
(save "LeZeroContApp")

;; Similary for rht:

;; IVTRealRight
(set-goal 
 "all a,b,p1(0<=b-a ->
 b-a<=2**p1 -> 
 all cds(
  all n,m(n<=m -> lft(cds n)<=lft(cds m)) -> 
  all n,m(n<=m -> rht(cds m)<=rht(cds n)) -> 
  all n lft(cds n)<=rht(cds n) -> 
  all n rht(cds n)-lft(cds n)==(2#3)**n*(b-a) -> 
  Real(RealConstr([n]rht(cds n))([p]TwoThirdExpBd(p+p1)))))")
(assume
 "a" "b" "p1" "0<=b-a" "b-a<=2**p1" "cds" "cIncr" "dDecr" "cs<=ds" "cdDiff")
(use "RealIntro")
;; 3,4
;; Cauchyness
(use "CauchyCrit")
(ng #t)
;; ?^6:all p,n,m(
;;      TwoThirdExpBd(p+p1)<=n -> 
;;      n<=m -> abs(rht(cds n)+ ~rht(cds m))<=(1#2**p))
(assume "p" "n" "m" "MBd" "n<=m")

;; ?^7:abs(rht(cds n)+ ~rht(cds m))<=(1#2**p)
(simprat (pf "abs(rht(cds n)-rht(cds m))==rht(cds n)-rht(cds m)"))

;; ?^8:rht(cds n)+ ~rht(cds m)<=(1#2**p)
(use "RatLeTrans" (pt "rht(cds n)-lft(cds n)"))
(ng #t)
(use "RatLeTrans" (pt "lft(cds m)"))
(use "cIncr")
(use "n<=m")
(use "cs<=ds")
(simprat "cdDiff")
(simprat (pf "(1#2**p)==(1#2**(p+p1))*2**p1"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "0<=b-a")

;; ?^21:(2#3)**n<=(1#2**(p+p1))
(use "RatLeTrans" (pt "(2#3)**TwoThirdExpBd(p+p1)"))
(use "RatLeMonExpDecr")
(use "Truth")
(use "Truth")
(use "MBd")
(use "TwoThirdExpNatZeroSeqNc")
(use "b-a<=2**p1")
;; ?^18:(1#2**p)==(1#2**(p+p1))*2**p1
(simp "PosPlusComm")
(ng #t)
(simp "PosExpTwoPosPlus")
(use "Truth")
;; ?^9:abs(rht(cds n)-rht(cds m))==rht(cds n)-rht(cds m)
(ng #t)
(simp "RatAbsId")
(use "Truth")
(simprat (pf "0==rht(cds m)+ ~rht(cds m)"))
(ng #t)
(use "dDecr")
(use "n<=m")
(use "RatEqvSym")
(use "Truth")
;; ?^4:Mon((RealConstr([n]rht(cds n))([p]TwoThirdExpBd(p+p1)))mod)
(use "MonIntro")
(ng #t)
;; ?^40:all p,q(p<=q -> TwoThirdExpBd(p+p1)<=TwoThirdExpBd(q+p1))
(assume "p" "q" "p<=q")
(assert "p+p1<=q+p1")
(use "PosLeMonPlus")
(use "p<=q")
(use "Truth")
(use "TwoThirdExpBdMon")
;; Proof finished.
;; (cdp)
(save "IVTRealRight")

;; IVTFinalRealRight
(set-goal "all f,q,p(
     Cont f -> 
     f f doml<<=0 -> 
     0<<=f f domr -> 
     f doml+(1#2**p)<=f domr -> 
     f domr-f doml<=2**p ->
     all c,d,p(
      f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
     all cds(
      cds Zero eqd(f doml pair f domr) ->
      all n Corr f(lft(cds n))(rht(cds n))(NatToPos(p+n)) ->
      all n(lft(cds n)<=lft(cds(Succ n))) ->
      all n(rht(cds(Succ n))<=rht(cds n)) ->
      all n(
       rht(cds(Succ n))-lft(cds(Succ n))==(2#3)*(rht(cds n)-lft(cds n))) ->
      Real(RealConstr([n]rht(cds n))([p0]TwoThirdExpBd(p0+p)))))")
(assume "f" "q" "p" "Cont f" "f a<<=0" "0<<=f b" "a <_p b" "b-a<=2**p" 
	"HypSlope" "cds"
	"cdsProp1" "cdsProp2" "cdsProp3" "cdsProp4" "cdsProp5")
(use "IVTRealRight" (pt "f doml") (pt "f domr"))

;; ?^3:0<=f domr-f doml
(use "RatLeTrans" (pt "f doml+(1#2**p)-f doml"))
(simp "RatPlusComm")
(ng #t)
(simprat "RatEqvPlusMinusRev")
(use "Truth")
(ng #t)
(use "a <_p b")

;; ?^4:f domr-f doml<=2**p
(use "b-a<=2**p")
;; ?^5:all n,m(n<=m -> lft(cds n)<=lft(cds m))
(assume "n" "m" "n<=m")
(simp (pf "m=n+(m--n)"))
(use "IVTLeftIncr" (pt "f") (pt "q") (pt "p"))
(auto)
(split)
(auto)
(split)
(auto)
(assume "n1")
(split)
(auto)
(split)
(auto)
(simp "NatPlusMinus")
(simp "<-" "NatMinusPlus")
(use "Truth")
(use "Truth")
(use "n<=m")
;; ?^6:all n,m(n<=m -> rht(cds m)<=rht(cds n))
(assume "n" "m" "n<=m")
(simp (pf "m=n+(m--n)"))
(use "IVTRightDecr")
(use "cdsProp4")
(simp "NatPlusMinus")
(simp "<-" "NatMinusPlus")
(use "Truth")
(use "Truth")
(use "n<=m")
;; ?^7:all n lft(cds n)<=rht(cds n)
(assume "n")
(use "CorrElim3Cor" (pt "f") (pt "(NatToPos(p+n))"))
(use "cdsProp2")
;; ?^8:all n rht(cds n)-lft(cds n)=(2#3)**n*(f domr-f doml)
(use "IVTDiff")
(use "cdsProp1")
(use "cdsProp5")
;; Proof finished.
;; (cdp)
(save "IVTFinalRealRight")

;; IVTRealAppRight
(set-goal 
 "all f,q,p(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 f doml+(1#2**p)<=f domr -> 
 f domr-f doml<=2**p -> 
 all c,d,p(f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
 all cds(
  cds Zero eqd(f doml pair f domr) -> 
  all n Corr f(lft(cds n))(rht(cds n))(NatToPos(p+n)) -> 
  all n lft(cds n)<=lft(cds(Succ n)) -> 
  all n rht(cds(Succ n))<=rht(cds n) -> 
  all n rht(cds(Succ n))-lft(cds(Succ n))==(2#3)*(rht(cds n)-lft(cds n)) -> 
  Real(f(RealConstr([n]rht(cds n))([p0](TwoThirdExpBd(p0+p)))))))")
(assume "f" "q" "p" "Cont f" "f a<<=0" "0<<=f b"
	"a <_p b" "b-a<=2**p" "HypSlope" 
        "cds" "cdsProp1" "cdsProp2" "cdsProp3" "cdsProp4" "cdsProp5")
(use "ContReal")
(use "Cont f")
;; ?^4:f doml<=f domr
(use "RatLeTrans" (pt "f doml+(1#2**p)"))
(use "RatLeTrans" (pt "f doml+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "a <_p b")
;; ?^5:Real(RealConstr([n]rht(cds n))([p0]TwoThirdExpBd(p0+p)))
(use "IVTFinalRealRight" (pt "f") (pt "q"))
(use "Cont f")
(use "f a<<=0")
(use "0<<=f b")
(use "a <_p b")
(use "b-a<=2**p")
(use "HypSlope")
(use "cdsProp1")
(use "cdsProp2")
(use "cdsProp3")
(use "cdsProp4")
(use "cdsProp5")
;; Proof finished.
;; (cdp)
(save "IVTRealAppRight")

;; IVTFinal
(set-goal 
 "all f,q,p(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 f doml+(1#2**p)<=f domr -> 
 f domr-f doml<=2**p -> 
 all c,d,p(f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
 exl x(Real x andi f x===0))")
(assume "f" "q" "p" "Cont f" "f a<<=0" "0<<=f b"
	"a <_p b" "b-a<=2**p" "HypSlope")
(cut "exl cds(
 cds Zero eqd(f doml pair f domr) andi 
 all n Corr f(lft(cds n))(rht(cds n))(NatToPos(p+n)) andi 
 all n(
  lft(cds n)<=lft(cds(Succ n)) andi rht(cds(Succ n))<=rht(cds n) andi 
  rht(cds(Succ n))-lft(cds(Succ n))==(2#3)*(rht(cds n)-lft(cds n))))")
(assume "Excds")
(by-assume "Excds" "cds" "cdsProp")
(intro 0 (pt "RealConstr([n]lft(cds n))([p0]TwoThirdExpBd(p0+p))"))
(split)
(use "IVTFinalRealLeft" (pt "f") (pt "q") (pt "p"))
(use "Cont f")
(use "f a<<=0")
(use "0<<=f b")
(use "a <_p b")
(use "b-a<=2**p")
(use "HypSlope")
(use "cdsProp")
(use "cdsProp")
(assume "n")
(use "cdsProp")
(assume "n")
(use "cdsProp")
(assume "n")
(use "cdsProp")
;; ?^11:f(RealConstr([n]lft(cds n))([p0]TwoThirdExpBd(p0+p)))===0
(use "RealLeAntiSym")
(use "LeContAppZero")
(use "Cont f")
(use "IVTFinalRealLeft" (pt "f") (pt "q"))
(use "Cont f")
(use "f a<<=0")
(use "0<<=f b")
(use "a <_p b")
(use "b-a<=2**p")
(use "HypSlope")
(use "cdsProp")
(use "cdsProp")
(assume "n")
(use "cdsProp")
(assume "n")
(use "cdsProp")
(assume "n")
(use "cdsProp")
;; ?^30:all m f((RealConstr([n]lft(cds n))([p0]TwoThirdExpBd(p0+p)))seq m)<<=0
(assume "n")
(use "CorrElim4" (pt "rht(cds n)") (pt "NatToPos(p+n)"))
(use "cdsProp")
;; 31:all n f doml<=(RealConstr([n0]lft(cds n0))([p0]TwoThirdExpBd(p0+p)))seq n
(ng #t)
;; ?^49:all n f doml<=lft(cds n)
(assume "n")
(use "CorrElim1" (pt "rht(cds n)") (pt "(NatToPos(p+n))"))
(use "cdsProp")
(assume "n")
(ng #t)
(use "RatLeTrans" (pt "rht(cds n)"))
(use "CorrElim3Cor" (pt "f") (pt "(NatToPos(p+n))"))
(use "cdsProp")
(use "CorrElim2" (pt "lft(cds n)") (pt "(NatToPos(p+n))"))
(use "cdsProp")
;; ?^27:0<<=f(RealConstr([n]lft(cds n))([p0]TwoThirdExpBd(p0+p)))
(use "RealLeCompat"
     (pt "RealConstr([n](0#1))([p]Zero)")
     (pt "f(RealConstr([n]rht(cds n))([p0]TwoThirdExpBd(p0+p)))"))
(use "RealEqRefl")
(use "RealRat")
;; ?^59:f(RealConstr([n]rht(cds n))([p0]TwoThirdExpBd(p0+p)))===
;;      f(RealConstr([n]lft(cds n))([p0]TwoThirdExpBd(p0+p)))
(use "ContAppCompat")
(use "Cont f")
(use "RatLeTrans" (pt "f doml+(1#2**p)"))
(use "RatLeTrans" (pt "f doml+(0#1)"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "a <_p b")
;; ?^64:RealConstr([n]rht(cds n))([p0]TwoThirdExpBd(p0+p))===
;;      RealConstr([n]lft(cds n))([p0]TwoThirdExpBd(p0+p))
(use "RealEqChar2")
(use "IVTRealRight" (pt "f doml") (pt "f domr"))

;; ?^74:0<=f domr-f doml
(use "RatLeTrans" (pt "f doml+(1#2**p)-f doml"))
(simp "RatPlusComm")
(ng #t)
(simprat "RatEqvPlusMinusRev")
(use "Truth")
(ng #t)
(use "a <_p b")
;; ?^75:f domr-f doml<=2**p
(use "b-a<=2**p")
;; ?^76:all n,m(n<=m -> lft(cds n)<=lft(cds m))
(assume "n" "m" "n<=m")
(simp (pf "m=n+(m--n)"))
(use "IVTLeftIncr" (pt "f") (pt "q") (pt "p"))
(auto)
;; (split)
;; (auto)
;; (split)
;; (auto)
;; (assume "n1")
;; (split)
;; (auto)
;; (split)
;; (auto)
(simp "NatPlusMinus")
(simp "<-" "NatMinusPlus")
(use "Truth")
(use "Truth")
(use "n<=m")
;; ?^77:all n,m(n<=m -> rht(cds m)<=rht(cds n))
(assume "n" "m" "n<=m")

;; (pp "IVTRightDecr")
;; (pp "NatPlusMinus") ;(l<=m -> n+(m--l)=n+m--l)
;; (pp "NatMinusPlus") ;(l<=n -> n--l+m=n+m--l)

(simp (pf "m=n+(m--n)"))
(use "IVTRightDecr")
(assume "n1")
(use "cdsProp")
(simp "NatPlusMinus")
(simp "<-" "NatMinusPlus")
(use "Truth")
(use "Truth")
(use "n<=m")
;; ?^78:all n lft(cds n)<=rht(cds n)
(assume "n1")
(use "CorrElim3Cor" (pt "f") (pt "(NatToPos(p+n1))"))
(use "cdsProp")
;; ?^79:all n rht(cds n)-lft(cds n)==(2#3)**n*(f domr-f doml)
(use "IVTDiff")
(use "cdsProp")
(assume "n")
(use "cdsProp")
;; ?^72:Real(RealConstr([n]lft(cds n))([p0]TwoThirdExpBd(p0+p)))
(use "IVTFinalRealLeft" (pt "f") (pt "q"))
(use "Cont f")
(use "f a<<=0")
(use "0<<=f b")
(use "a <_p b")
(use "b-a<=2**p")
(use "HypSlope")
(use "cdsProp")
(use "cdsProp")
(assume "n")
(use "cdsProp")
(assume "n")
(use "cdsProp")
(assume "n")
(use "cdsProp")
;; ?^73:all p0 
;;       exnc n 
;;        all n0(
;;         n<=n0 -> 
;;         abs((RealConstr([n1]rht(cds n1))([p1]TwoThirdExpBd(p1+p)))seq n0+ 
;;            ~((RealConstr([n1]lft(cds n1))([p1]TwoThirdExpBd(p1+p)))seq n0))<=
;;         (1#2**p0))
(ng #t)
;; ?^127:all p exnc n all n0(n<=n0 -> abs(rht(cds n0)+ ~lft(cds n0))<=(1#2**p))
(assume "p1")
;; n needed
(inst-with-to "TwoThirdExpNatZeroSeq" (pt "p+p1") "ExHyp")
(by-assume "ExHyp" "n" "nProp")
(intro 0 (pt "n"))
(assume "n1" "n<=n1")
(simprat "IVTDiff" (pt "f"))
(simp "RatAbsId")
(use "RatLeTrans" (pt "(2#3)**n1*2**p"))
(use "RatLeMonTimesTwo")
(use "Truth")
;; ?^144:0<=f domr+ ~f doml
(use "RatLeTrans" (pt "f doml+(1#2**p)-f doml"))
(simp "RatPlusComm")
(ng #t)
(simprat "RatEqvPlusMinusRev")
(use "Truth")
(ng #t)
(use "a <_p b")
(use "Truth")
(use "b-a<=2**p")
;; ?^142:(2#3)**n1*2**p<=(1#2**p1)
(use "RatLeTrans" (pt "(1#2**(p+p1))*2**p"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "(2#3)**n"))
(use "RatLeMonExpDecr")
(use "Truth")
(use "Truth")
(use "n<=n1")
(use "nProp")
(use "Truth")
(simp "<-" "PosExpTwoPosPlus")
(use "Truth")
;; ?^140:0<=(2#3)**n1*(f domr+ ~f doml)
(use "RatLeTrans" (pt "(0#1)*0"))
(use "Truth")
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?^170:0<=f domr+ ~f doml ;see above
(use "RatLeTrans" (pt "f doml+(1#2**p)-f doml"))
(simp "RatPlusComm")
(ng #t)
(simprat "RatEqvPlusMinusRev")
(use "Truth")
(ng #t)
(use "a <_p b")
;; ?^138:all n rht(cds(Succ n))-lft(cds(Succ n))==(2#3)*(rht(cds n)-lft(cds n))
(assume "n2")
(use "cdsProp")
;; ?^137:cds Zero eqd(f doml pair f domr)
(use "cdsProp")
;; ?^60:0<<=f(RealConstr([n]rht(cds n))([p0]TwoThirdExpBd(p0+p)))
(use "LeZeroContApp")
(use "Cont f")
(use "IVTFinalRealRight" (pt "f") (pt "q"))
(use "Cont f")
(use "f a<<=0")
(use "0<<=f b")
(use "a <_p b")
(use "b-a<=2**p")
(use "HypSlope")
(use "cdsProp")
(use "cdsProp")
(assume "n")
(use "cdsProp")
(assume "n")
(use "cdsProp")
(assume "n")
(use "cdsProp")
;; ?^180:all m 0<<=f((RealConstr([n]rht(cds n))([p0]TwoThirdExpBd(p0+p)))seq m)
(assume "n")
(use "CorrElim5" (pt "lft(cds n)") (pt "NatToPos(p+n)"))
(use "cdsProp")
;; 181:all n f doml<=(RealConstr([n0]rht(cds n0))([p0]TwoThirdExpBd(p0+p)))seq n
(ng #t)
;; ?^199:all n f doml<=rht(cds n)
(assume "n")
(use "RatLeTrans" (pt "lft(cds n)"))
(use "CorrElim1" (pt "rht(cds n)") (pt "(NatToPos(p+n))"))
(use "cdsProp")
(use "CorrElim3Cor" (pt "f") (pt "(NatToPos(p+n))"))
(use "cdsProp")
(assume "n")
(ng #t)
(use "CorrElim2" (pt "lft(cds n)") (pt "(NatToPos(p+n))"))
(use "cdsProp")

;; ?^4:exl cds(
;;      cds Zero eqd(f doml pair f domr) andnc 
;;      all n Corr f(lft(cds n))(rht(cds n))(NatToPos(p+n)) andnc 
;;      all n(
;;       lft(cds n)<=lft(cds(Succ n)) andnc 
;;       rht(cds(Succ n))<=rht(cds n) andnc 
;;       rht(cds(Succ n))-lft(cds(Succ n))==(2#3)*(rht(cds n)-lft(cds n))))

(use "IVTcds" (pt "q"))
(use "Cont f")
(use "f a<<=0")
(use "0<<=f b")
(use "a <_p b")
(use "HypSlope")
;; Proof finished.
;; (cdp)
(save "IVTFinal")

(define IVTFinal-eterm (proof-to-extracted-term))
(define IVTFinal-neterm (rename-variables (nt IVTFinal-eterm)))
;; (pp IVTFinal-neterm)
;; [f,p,p0]RealConstr([n]lft(cIVTcds f p p0 n))([p1]TwoThirdExpBd(p1+p0))

(add-sound "IVTFinal")

;; ok, IVTFinalSound has been added as a new theorem:

;; allnc f,q,p(
;;  Cont f -> 
;;  f f doml<<=0 -> 
;;  0<<=f f domr -> 
;;  f doml+(1#2**p)<=f domr -> 
;;  f domr-f doml<=2**p -> 
;;  all c,d,p0(
;;   f doml<=c -> d<=f domr -> c+(1#2**p0)<=d -> RealLt(f c)(f d)(p0+q)) -> 
;;  (ExLTMR (cterm (x) Real x andnc f x===0))(cIVTFinal f q p))

;; with computation rule

;; cIVTFinal eqd
;; ([f,p,p0]RealConstr([n]lft(cIVTcds f p p0 n))([p1]TwoThirdExpBd(p1+p0)))

(deanimate "IVTFinal")

;; For to extract an approximation of sqrt 2 we prove IVTApprox
;; This needs RealApprox (in real.scm)

;; IVTApprox
(set-goal
 "all f,q,p(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 f doml+(1#2**p)<=f domr -> 
 f domr-f doml<=2**p -> 
 all c,d,p(f doml<=c -> d<=f domr -> c+(1#2**p)<=d -> RealLt(f c)(f d)(p+q)) -> 
 exr x(Real x andr f x===0 andr all r exl c abs(c+ ~x)<<=(1#2**r)))")
(assume "f" "q" "p" "Cont f" "f a<<=0" "0<<=f b"
	"a <_p b" "b-a<=2**p" "HypSlope")
(cut "exl x(Real x andnc f x===0)")
(assume "ExHyp")
(by-assume "ExHyp" "x" "xProp")

;; ?_8:exr x(Real x andr f x===0 andr all r exl c abs(c+ ~x)<<=(1#2**r))
(intro 0 (pt "x"))
(split)
(use "xProp")
(split)
(use "xProp")

;; ?_13:all r exl c abs(c+ ~x)<<=(1#2**r)
(assume "r")
(use "RealApprox")
(use "xProp")

;; ?_4:exl x(Real x andnc f x===0)
(use "IVTFinal" (pt "q") (pt "p"))
(auto)
;; Proof finished.
;; (cdp)
(save "IVTApprox")

(define IVTApprox-eterm (proof-to-extracted-term))
(define IVTApprox-neterm (rename-variables (nt IVTApprox-eterm)))
;; (pp IVTApprox-neterm)
;; [f,p,p0]cRealApprox(cIVTFinal f p p0)

(add-sound "IVTApprox")

;; ok, IVTApproxSound has been added as a new theorem:

;; allnc f,q,p(
;;  Cont f -> 
;;  f f doml<<=0 -> 
;;  0<<=f f domr -> 
;;  f doml+(1#2**p)<=f domr -> 
;;  f domr-f doml<=2**p -> 
;;  all c,d,p0(
;;   f doml<=c -> d<=f domr -> c+(1#2**p0)<=d -> RealLt(f c)(f d)(p0+q)) -> 
;;  (ExRTMR rea
;;    pos=>rat
;;    (cterm (x,(pos=>rat)^) 
;;    (AndRMR (cterm () Real x)
;;      (cterm ((pos=>rat)^0) 
;;      (AndRMR (cterm () f x===0)
;;        (cterm ((pos=>rat)^1) 
;;        allnc r (ExLTMR (cterm (c) abs(c+ ~x)<<=(1#2**r)))((pos=>rat)^1 r)))
;;      (pos=>rat)^0))
;;    (pos=>rat)^))
;;  (cIVTApprox f q p))

;; with computation rule

;; cIVTApprox eqd([f,p,p0]cRealApprox(cIVTFinal f p p0))
