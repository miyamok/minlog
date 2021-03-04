;; 2021-02-26.  cont.scm

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

(display "loading cont.scm ...") (newline)

;; Continuous functions
;; ====================

;; 2004-01-24
;; Algebraic structures (`hierarchy') versus concrete algebras.

;; To develop general group theory, take a type variable alpha (the
;; type of the group elements) and a predicate variable G of arity
;; alpha (the property to be an element of the group).  Take a binary
;; predicate variable == and formulate as its properties that it is an
;; equivalence relation on G.  Take a binary function variable o
;; (composition), a unary function variable inv (inverse) and a
;; variable e (unit), and formulate as their properties that G is
;; closed under them, compatibility with ==, and finally the ordinary
;; group axioms.  For equality reasoning we cannot use computation or
;; rewrite rules (there are no program constants), but must use simp
;; instead.  To apply general results for a concrete group, use proof
;; substitution.

;; For a concrete algebra (`record') the underlying data type is a
;; free algebra with one non-iterable constructor.  The destructors
;; are program constants and come with the obvious computation rules.
;; They should have informative names (`fields').  In a second step
;; the actual elements of the concrete algebra are singled out by
;; means of a (formally) inductively defined predicate, which in fact
;; is explicitly defined by the required properties of the field
;; components.

;; Example: continuous functions.

(add-algs
 "cont"
 (list "ContConstr"
       "rat=>rat=>(rat=>nat=>rat)=>(pos=>nat)=>(pos=>pos)=>rat=>rat=>cont"))

(add-var-name "h" (py "rat=>nat=>rat")) ;approximating map
(add-var-name "al" (py "pos=>nat")) ;uniform modulus of Cauchyness
(add-var-name "om" (py "pos=>pos")) ;uniform modulus of continuity
(add-var-name "mu" "nu" (py "rat")) ;lower and upper bound

(add-totality "cont")
(add-eqp "cont")

(add-program-constant "ContDoml" (py "cont=>rat") t-deg-zero)
(add-postfix-display-string "ContDoml" "doml")

(add-computation-rules
 "(ContConstr a b h al om mu nu)doml" "a")

(add-var-name "f" (make-alg "cont"))

;; ContDomlTotal
(set-totality-goal "ContDoml")
(assume "f^" "Tf")
(elim "Tf")
(assume
 "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom" "mu^" "Tmu" "nu^" "Tnu")
(ng #t)
(use "Ta")
;; Proof finished.
(save-totality)

(add-program-constant "ContDomr" (py "cont=>rat") t-deg-zero)
(add-postfix-display-string "ContDomr" "domr")
 
(add-computation-rules
 "(ContConstr a b h al om mu nu)domr" "b")

;; ContDomrTotal
(set-totality-goal "ContDomr")
(assume "f^" "Tf")
(elim "Tf")
(assume
 "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom" "mu^" "Tmu" "nu^" "Tnu")
(ng #t)
(use "Tb")
;; Proof finished.
(save-totality)

(add-program-constant
 "ContApprox" (py "cont=>rat=>nat=>rat") t-deg-zero 'const 1)
(add-postfix-display-string "ContApprox" "approx")

(add-computation-rules
 "(ContConstr a b h al om mu nu)approx" "h")

;; ContApproxTotal
(set-totality-goal "ContApprox")
(assume "f^" "Tf")
(elim "Tf")
(assume
 "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom" "mu^" "Tmu" "nu^" "Tnu")
(ng #t)
(use "Th")
;; Proof finished.
(save "ContApproxTotal")

(add-program-constant "ContuMod" (py "cont=>pos=>nat") t-deg-zero 'const 1)
(add-postfix-display-string "ContuMod" "uMod")

(add-computation-rules
 "(ContConstr a0 b0 h al om mu nu)uMod" "al")

;; ContuModTotal
(set-goal (rename-variables (term-to-totality-formula (pt "ContuMod"))))
(assume "f^" "Tf")
(elim "Tf")
(assume
 "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom" "mu^" "Tmu" "nu^" "Tnu")
(ng #t)
(use "TM")
;; Proof finished.
(save "ContuModTotal")

(add-program-constant "ContuModCont" (py "cont=>pos=>pos") t-deg-zero 'const 1)
(add-postfix-display-string "ContuModCont" "uModCont")

(add-computation-rules
 "(ContConstr a b h al om mu nu)uModCont" "om")

;; ContuModContTotal
(set-totality-goal "ContuModCont")
(assume "f^" "Tf")
(elim "Tf")
(assume
 "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom" "mu^" "Tmu" "nu^" "Tnu")
(ng #t)
(use "Tom")
;; Proof finished.
(save-totality)

(add-program-constant "ContLb" (py "cont=>rat") t-deg-zero)
(add-postfix-display-string "ContLb" "lb")

(add-computation-rules
 "(ContConstr a b h al om mu nu)lb" "mu")

;; ContLbTotal
(set-totality-goal "ContLb")
(assume "f^" "Tf")
(elim "Tf")
(assume
 "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom" "mu^" "Tmu" "nu^" "Tnu")
(ng #t)
(use "Tmu")
;; Proof finished.
(save-totality)

(add-program-constant "ContUb" (py "cont=>rat") t-deg-zero)
(add-postfix-display-string "ContUb" "ub")

(add-computation-rules
 "(ContConstr a b h al om mu nu)ub" "nu")

;; ContUbTotal
(set-totality-goal "ContUb")
(assume "f^" "Tf")
(elim "Tf")
(assume
 "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom" "mu^" "Tmu" "nu^" "Tnu")
(ng #t)
(use "Tnu")
;; Proof finished.
(save-totality)

;; Now the (formally inductive) definition of Cont

(add-ids
 (list (list "Cont" (make-arity (make-alg "cont"))))
 '("all a0,b0,h,al,om,mu,nu(
     all a(a0<=a -> a<=b0 -> Cauchy(h a)al) -> 
     all a,b,p,n(a0<=a -> a<=b0 -> a0<=b -> b<=b0 ->
                  al p<=n -> 
                  abs(a-b)<=(1#2**PosPred(om p)) ->
                  abs(h a n-h b n)<=(1#2**p)) ->
     all p,q(p<=q -> al p<=al q) ->
     all p,q(p<=q -> om p<=om q) ->
     all a,n(a0<=a -> a<=b0 -> mu<=h a n) -> 
     all a,n(a0<=a -> a<=b0 -> h a n<=nu) -> 
     Cont(ContConstr a0 b0 h al om mu nu))" "ContIntro"))

;; Example of a continuous function: a^2-2 on [1,2]

;; (pp (pt "(ContConstr 1 2([a,n]a*a-2)([p]Zero)([p]p+3)1 4)"))
;(pp (nt (pt "(ContConstr 1 2([a,n]a*a-2)([p]Zero)([p]p+3)1 4)approx(14#10)1")))
;; IntN 1#25

;; ContElim1
(set-goal
 "all f(Cont f ->
        all a(f doml<=a -> a<=f domr -> Cauchy(f approx a)(f uMod)))")
(ind)
(assume "a0" "b0" "h" "al" "om" "a1" "a2")
(elim)
(search)
;; Proof finished.
(save "ContElim1")

;; ContElim2
(set-goal "all f(
 Cont f -> 
 all a,b,p,n(
  f doml<=a -> 
  a<=f domr -> 
  f doml<=b -> 
  b<=f domr -> 
  f uMod p<=n -> 
  abs(a-b)<=(1#2**PosPred(f uModCont p)) ->
 abs(f approx a n-f approx b n)<=(1#2**p)))")
(ind)
(assume "a0" "b0" "h" "al" "om" "a1" "a2")
(elim)
(search)
;; Proof finished.
(save "ContElim2")

;; ContElim3
(set-goal "all f(Cont f -> all p,q(p<=q -> f uMod p<=f uMod q))")
(ind)
(assume "a0" "b0" "h" "al" "om" "a1" "a2")
(elim)
(search)
;; Proof finished.
(save "ContElim3")

;; ContElim4
(set-goal "all f(Cont f -> all p,q(p<=q -> f uModCont p<=f uModCont q))")
(ind)
(assume "a0" "b0" "h" "al" "om" "a1" "a2")
(elim)
(search)
;; Proof finished.
(save "ContElim4")

;; ContElim5
(set-goal
 "all f(Cont f -> all a,n(f doml<=a -> a<=f domr -> f lb<=f approx a n))")
(ind)
(assume "a0" "b0" "h" "al" "om" "a1" "a2")
(elim)
(search)
;; Proof finished.
;; (cdp)
(save "ContElim5")

;; ContElim6
(set-goal
 "all f(Cont f -> all a,n(f doml<=a -> a<=f domr -> f approx a n<=f ub))")
(ind)
(assume "a0" "b0" "h" "al" "om" "a1" "a2")
(elim)
(search)
;; Proof finished.
;; (cdp)
(save "ContElim6")

;; We aim at an application notation.

(add-program-constant "AppContOne" (py "cont=>rea=>rea") t-deg-zero)

;; 2018-10-30.  Change of AppContOne to ensure that a_n's stay in [c,d].
;; Use a_n max c min d instead.

;; (pp (pt "x seq n max c min d"))

;; The modulus only has p+1 instead of p+2.
;; (pp (pt "f uMod(p+1)max x mod(PosPred(f uModCont(p+1)))"))

;; To prove Real(f x) we will need properties.

;; |a'-b'|<=|a-b|

;; RatMaxMinEq
(set-goal "all a,c,d(c<=a -> a<=d -> a max c min d=a)")
(assume "a" "c" "d" "c<=a" "a<=d")
(simp "RatMaxEq1")
(simp "RatMinEq1")
(use "Truth")
(use "a<=d")
(use "c<=a")
;; Proof finished.
(save "RatMaxMinEq")

;; RatMaxMinUB
(set-goal "all a,c,d(c<=d -> c<=a max c min d)")
(assume "a" "c" "d" "c<=d")
(cases (pt "a<=c"))
;; 3,4
(assume "a<=c")
(simprat "RatMaxEq2")
(simp "RatMinEq1")
(use "Truth")
(use "c<=d")
(use "a<=c")
;; 4
(assume "a<=c -> F")
(assert "c<=a")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "a<=c -> F")
;; Assertion proved.
(assume "c<=a")
(simp "RatMaxEq1")
(use "RatMinGLB")
(use "c<=a")
(use "c<=d")
(use "c<=a")
;; Proof finished.
(save "RatMaxMinUB")

;; RatMaxMinLB
(set-goal "all a,c,d(c<=d -> a max c min d<=d)")
(assume "a" "c" "d" "c<=d")
(cases (pt "d<=a"))
(assume "d<=a")
(simp "RatMaxEq1")
(simprat "RatMinEq2")
(use "Truth")
(use "d<=a")
(use "RatLeTrans" (pt "d"))
(use "c<=d")
(use "d<=a")
;; 4
(assume "d<=a -> F")
(assert "a<=d")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "d<=a -> F")
;; Assertion proved.
(assume "a<=d")
(use "RatMinLB2")
;; Proof finished.
(save "RatMaxMinLB");; RatLeAbsMinusMaxMin
(set-goal
 "all a,b,c,d(c<=d -> abs(a max c min d+ ~(b max c min d))<=abs(a+ ~b))")
(assume "a" "b" "c" "d" "c<=d")
(cases (pt "a<=c"))
;; 3,4
(assume "a<=c")
(simprat (pf "a max c==c"))
(simp (pf "c min d=c"))
(cases (pt "b<=c"))
;; 10,11
(assume "b<=c")
(simprat (pf "b max c==c"))
(simp (pf "c min d=c"))
(simprat (pf "c+ ~c==0"))
(use "Truth")
(use "RatEqv2RewRule" (pt "a"))
(use "RatMinEq1")
(use "c<=d")
(use "RatMaxEq2")
(use "b<=c")
;; 11
(assume "b<=c -> F")
(assert "c<=b")
 (use "RatLtToLe")
 (use "RatNotLeToLt")
 (use "b<=c -> F")
(assume "c<=b")
(simp (pf "b max c=b"))
(cases (pt "b<=d"))
;; 29,30
(assume "b<=d")
(simp (pf "b min d=b"))
(simp "RatEqAbsMinusCor")
(simp "RatEqAbsMinusCor")
(ng #t)
(use "a<=c")
(use "RatLeTrans" (pt "c"))
(use "a<=c")
(use "c<=b")
(use "c<=b")
(use "RatMinEq1")
(use "b<=d")
;; 30
(assume "b<=d -> F")
(assert "d<=b")
 (use "RatLtToLe")
 (use "RatNotLeToLt")
 (use "b<=d -> F")
(assume "d<=b")
(simprat (pf "b min d==d"))
(simp "RatEqAbsMinusCor")
(simp "RatEqAbsMinusCor")
(use "RatLeMonPlus")
(use "d<=b")
(use "a<=c")
(use "RatLeTrans" (pt "c"))
(use "a<=c")
(use "c<=b")
(use "c<=d")
(use "RatMinEq2")
(use "d<=b")
;; 28
(use "RatMaxEq1")
(use "c<=b")
;; 9
(use "RatMinEq1")
(use "c<=d")
;; 7
(use "RatMaxEq2")
(use "a<=c")
;; ?^4:(a<=c -> F) -> abs(a max c min d+ ~(b max c min d))<=abs(a+ ~b)
(assume "a<=c -> F")
(assert "c<=a")
 (use "RatLtToLe")
 (use "RatNotLeToLt")
 (use "a<=c -> F")
(assume "c<=a")
(simp (pf "a max c=a"))
(cases (pt "a<=d"))
;; 70,71
(assume "a<=d")
(simp (pf "a min d=a"))
(cases (pt "b<=c"))
;; 75,76
(assume "b<=c")
(simprat (pf "b max c==c"))
(simp (pf "c min d=c"))
(simp "RatEqAbsMinus")
(simp "RatEqAbsMinus")
(ng #t)
(use "b<=c")
(use "RatLeTrans" (pt "c"))
(use "b<=c")
(use "c<=a")
(use "c<=a")
(use "RatMinEq1")
(use "c<=d")
(use "RatMaxEq2")
(use "b<=c")
;; 76
(assume "b<=c -> F")
(assert "c<=b")
 (use "RatLtToLe")
 (use "RatNotLeToLt")
 (use "b<=c -> F")
(assume "c<=b")
(simp (pf "b max c=b"))
(cases (pt "b<=d"))
;; 99,100
(assume "b<=d")
(simp (pf "b min d=b"))
(use "Truth")
(use "RatMinEq1")
(use "b<=d")
;; 100
(assume "b<=d -> F")
(assert "d<=b")
 (use "RatLtToLe")
 (use "RatNotLeToLt")
 (use "b<=d -> F")
(assume "d<=b")
(simprat (pf "b min d==d"))
(simp "RatEqAbsMinusCor")
(simp "RatEqAbsMinusCor")
(ng #t)
(use "d<=b")
(use "RatLeTrans" (pt "d"))
(use "a<=d")
(use "d<=b")
(use "a<=d")
(use "RatMinEq2")
(use "d<=b")
(use "RatMaxEq1")
(use "c<=b")
;; 74
(use "RatMinEq1")
(use "a<=d")
;; 71
(assume "a<=d -> F")
(assert "d<=a")
 (use "RatLtToLe")
 (use "RatNotLeToLt")
 (use "a<=d -> F")
(assume "d<=a")
(simprat (pf "a min d==d"))
(cases (pt "b<=c"))
;; 131,132
(assume "b<=c")
(simprat (pf "b max c==c"))
(simp (pf "c min d=c"))
(simp "RatEqAbsMinus")
(simp "RatEqAbsMinus")
(use "RatLeMonPlus")
(use "d<=a")
(use "b<=c")
(use "RatLeTrans" (pt "c"))
(use "b<=c")
(use "c<=a")
(use "c<=d")
(use "RatMinEq1")
(use "c<=d")
(use "RatMaxEq2")
(use "b<=c")
;; 132
(assume "b<=c -> F")
(assert "c<=b")
 (use "RatLtToLe")
 (use "RatNotLeToLt")
 (use "b<=c -> F")
(assume "c<=b")
(simp (pf "b max c=b"))
(cases (pt "b<=d"))
;; 156,157
(assume "b<=d")
(simp (pf "b min d=b"))
(simp "RatEqAbsMinus")
(simp "RatEqAbsMinus")
(ng #t)
(use "d<=a")
(use "RatLeTrans" (pt "d"))
(use "b<=d")
(use "d<=a")
(use "b<=d")
(use "RatMinEq1")
(use "b<=d")
;; 157
(assume "b<=d -> F")
(assert "d<=b")
 (use "RatLtToLe")
 (use "RatNotLeToLt")
 (use "b<=d -> F")
(assume "d<=b")
(simprat (pf "b min d==d"))
(simprat (pf "d+ ~d==0"))
(use "Truth")
(use "RatEqv2RewRule" (pt "d"))
(use "RatMinEq2")
(use "d<=b")
(use "RatMaxEq1")
(use "c<=b")
;; 130
(use "RatMinEq2")
(use "d<=a")
;; 69
(use "RatMaxEq1")
(use "c<=a")
;; Proof finished.
;; (cdp)
(save "RatLeAbsMinusMaxMin")

(add-computation-rule
 "AppContOne f x"
 "RealConstr([n]f approx(x seq n max f doml min f domr)n)
            ([p]f uMod(p+1)max x mod(PosPred(f uModCont(p+1))))")

;; AppContOneTotal
(set-totality-goal "AppContOne")
(assume "f^" "Tf")
(elim "Tf")
(assume
 "a^" "Ta" "b^" "Tb" "h^" "Th" "al^" "Tal" "om^" "Tom" "mu^" "Tmu" "nu^" "Tnu"
 "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(use "TotalReaRealConstr")
(ng #t)
(assume "n^" "Tn")
(use "Th")
(use "RatMinTotal")
(use "RatMaxTotal")
(use "Tas")
(use "Tn")
(use "Ta")
(use "Tb")
(use "Tn")
;; 9
(assume "p^" "Tp")
(ng #t)
(use "NatMaxTotal")
(use "Tal")
(use "PosSTotal")
(use "Tp")
(use "TM")
(use "PosPredTotal")
(use "Tom")
(use "PosSTotal")
(use "Tp")
;; Proof finished.
;; (cdp)
(save-totality)

(add-application (pt "AppContOne"))

;; (pp (pf "f x"))
;; f x

;; (pp (pt "(f x)seq"))
;; (pp (pt "(f x)mod"))

;; (pp (rename-variables (nt (pt "(f x)seq"))))
;; [n]f approx(x seq n max f doml min f domr)n

;; (pp (rename-variables (nt (pt "(f x)mod"))))
;; [p]ContuMod f(PosS p)max x mod(PosPred(f uModCont(PosS p)))

;; ContReal
(set-goal "all f(Cont f -> f doml<=f domr -> all x(Real x -> Real(f x)))")
(assume "f" "Cf")
(elim "Cf")
(ng)
(assume "c" "d" "h" "al" "om" "mu" "nu"
	"alCauchy" "omMod" "alMon" "omMon" "muLb" "nuUb" "c<=d" "x" "Rx")
(elim "Rx")
(cases)
(ng)
(assume "as" "M" "CasM" "MonM")
(intro 0)
;; 10,11
(ng)
(intro 0)
(ng)
(assume "p" "n" "m" "nBd" "mBd")
(assert "all l c<=as l max c min d")
 (assume "l")
 (use "RatMinGLB")
 (use "RatMaxUB2")
 (use "c<=d")
;; Assertion proved.
(assume "cLBd")
(assert "all l as l max c min d<=d")
 (assume "l")
 (use "RatMinLB2")
;; Assertion proved.
(assume "dUBd")
(use "RatLeTrans"
     (pt "abs(h(as n max c min d)n+ ~(h(as n max c min d)m))+
          abs(h(as n max c min d)m+ ~(h(as m max c min d)m))"))
(use "Truth")
(use "RatLeTrans" (pt "(1#2**PosS p)+(1#2**PosS p)"))
(use "RatLeMonPlus")
;; 30,31
;; ?^30:abs(h(as n max c min d)n+ ~(h(as n max c min d)m))<=(1#2**PosS p)
(use-with
 "CauchyElim"
 (pt "h(as n max c min d)") (pt "al") "?"
 (pt "PosS p") (pt "n") (pt "m") "?" "?")
(use "alCauchy")
(use "cLBd")
(use "dUBd")
(use "NatLeTrans" (pt "al(PosS p)max M(PosPred(om(PosS p)))"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "al(PosS p)max M(PosPred(om(PosS p)))"))
(use "NatMaxUB1")
(use "mBd")
;; ?^31:abs(h(as n max c min d)m+ ~(h(as m max c min d)m))<=(1#2**PosS p)
(use "omMod")
(use "cLBd")
(use "dUBd")
(use "cLBd")
(use "dUBd")
(use "NatLeTrans" (pt "al(PosS p)max M(PosPred(om(PosS p)))"))
(use "NatMaxUB1")
(use "mBd")
;; ?^46:abs(as n max c min d+ ~(as m max c min d))<=(1#2**PosPred(om(PosS p)))
(use "RatLeTrans" (pt "abs(as n+ ~(as m))"))
(use "RatLeAbsMinusMaxMin")
(use "c<=d")
;; ?^50:abs(as n+ ~(as m))<=(1#2**PosPred(om(PosS p)))
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatLeTrans" (pt "al(PosS p)max M(PosPred(om(PosS p)))"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "al(PosS p)max M(PosPred(om(PosS p)))"))
(use "NatMaxUB2")
(use "mBd")
;; ?^29:(1#2**PosS p)+(1#2**PosS p)<=(1#2**p)
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; ?^11:Mon((RealConstr([n]h(as n max c min d)n)
;;       ([p]al(PosS p)max M(PosPred(om(PosS p)))))mod)
(ng)
;; ?^60:Mon([p]al(PosS p)max M(PosPred(om(PosS p))))
(use "MonIntro")
(ng)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
(use "alMon")
(use "p<=q")
(use "MonElim")
(use "MonM")
(use "PosLeMonPred")
(use "omMon")
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "ContReal")

;; Here we need that (x seq) is above (f doml) from some n onwards,
;; since otherwise the approximating function for f is undefined.
;; ContReal is used below in InvApprox to prove Real(g u)

;; ContAppCompat
(set-goal "all f(Cont f -> f doml<=f domr -> all x,y(x===y -> f x===f y))")
(assume "f" "Cf" "c<=d" "x" "y" "x=y")
(use "RealEqChar2")
(use "ContReal")
(use "Cf")
(use "c<=d")
(realproof)
(use "ContReal")
(use "Cf")
(use "c<=d")
(realproof)
(assume "p")
(inst-with-to "RealEqChar1"
	      (pt "x") (pt "y") "x=y" (pt "PosPred(f uModCont p)") "ExHyp")
(by-assume "ExHyp" "n0" "n0Prop")
(intro 0 (pt "n0 max f uMod p"))
(assume "n" "nBd")
(ng #t)
(assert "abs(x seq n max f doml min f domr+ ~(y seq n max f doml min f domr))<=
            (1#2**PosPred(f uModCont p))")
(use "RatLeTrans" (pt "abs(x seq n+ ~(y seq n))"))
(use "RatLeAbsMinusMaxMin")
(use "c<=d")
(use "n0Prop")
(use "NatLeTrans" (pt "n0 max f uMod p"))
(use "NatMaxUB1")
(use "nBd")
;; Assertion proved.
(assume "Assertion")
(use "ContElim2")
(use "Cf")
(use "RatMaxMinUB")
(use "c<=d")
(use "RatMaxMinLB")
(use "c<=d")
(use "RatMaxMinUB")
(use "c<=d")
(use "RatMaxMinLB")
(use "c<=d")
;; 35
(use "NatLeTrans" (pt "n0 max f uMod p"))
(use "NatMaxUB2")
(use "nBd")
(use "Assertion")
;; Proof finished.
;; (cdp)
(save "ContAppCompat")

;; ContMod
(set-goal "all f(Cont f -> f doml<=f domr -> all p 1 < f uModCont p ->
 all x,y,p(Real x -> Real y -> abs(x+ ~y)<<=(1#2**f uModCont p) ->
           abs(f x+ ~(f y))<<=(1#2**p)))")
(assume "f" "Cf" "c<=d" "ompos" "x" "y" "p" "Rx" "Ry" "LeHyp")
(inst-with-to "ContReal" (pt "f") "Cf" "c<=d" (pt "x") "Rx" "Rfx")
(inst-with-to "ContReal" (pt "f") "Cf" "c<=d" (pt "y") "Ry" "Rfy")
(use "RealLeChar2RealConstrFree")
(autoreal)
(assume "p0")
(inst-with-to
 "RealLeChar1RealConstrFree"
 (pt "abs(x+ ~y)") (pt "RealConstr([n] 1#2**f uModCont p)([p] Zero)")
 "LeHyp" (pt "f uModCont p") "Ass")
(elim "Ass")
(assume "n0")
(drop "Ass")
(assume "Ass2")
(intro 0 (pt "n0 max f uMod p"))
(assume "n")
(assume "n0def")
(simp "RatLeTrans" (pt "(1#2**p)seq n + 0"))
(use "Truth")
(use "RatLeMonPlus")
(search)
(search)
(ng #t)
(use "ContElim2")
(use "Cf")
(use "RatMaxMinUB")
(use "c<=d")
(use "RatMinLB2")
(use "RatMaxMinUB")
(use "c<=d")
(use "RatMinLB2")
(use "NatLeTrans" (pt "n0 max f uMod p"))
(use "NatMaxUB2")
(use "n0def")
(use "RatLeTrans" (pt "abs(x seq n - y seq n)"))
(use "RatLeAbsMinusMaxMin")
(use "c<=d")
(use "RatLeTrans" (pt "(1#2**f uModCont p) + (1#2**f uModCont p)"))
(use "RatLeTrans" (pt "(abs(x+ ~y))seq n"))
(use "RatLeRefl")
(cases (pt "x"))
(cases (pt "y"))
(assume "as" "M" "eq1" "as0" "M0" "eq2")
(ng #t)
(use "Truth")
(use "Ass2")
(use "NatLeTrans" (pt "n0 max f uMod p"))
(use "NatMaxUB1")
(use "n0def")
(use "RatLeRefl")
(simp (pf "f uModCont p == PosS(PosPred (f uModCont p))"))
(use "RatPlusHalfExpPosS")
(use "RatEqvSym")
(use "PosSPosPredId")
(use "ompos")
;; Proof finished.
;; (cdp)
(save "ContMod")

(add-program-constant "ContComp" (py "cont=>cont=>cont") t-deg-zero)
(add-computation-rule
 "ContComp f0 f"
 "ContConstr (f doml) (f domr) ([a, n] f0 approx (f approx a n) n)
 ([p] (f0 uMod (p+1)) max (f uMod (PosPred(f0 uModCont (p+1)))))
 ([p] f uModCont (PosPred(f0 uModCont p))) (f0 lb) (f0 ub)")

(set-totality-goal "ContComp")
(fold-alltotal)
(assume "f0")
(fold-alltotal)
(assume "f")
(ng #t)
(intro 0)
;; 7-13
(use "RatTotalVar")
;; 8
(use "RatTotalVar")
;; 9
(fold-alltotal)
(assume "a")
(fold-alltotal)
(assume "n")
(ng #t)
(use "RatTotalVar")
;; 10
(fold-alltotal)
(assume "p")
(ng #t)
(use "NatTotalVar")
;; 11
(fold-alltotal)
(assume "p")
(ng #t)
(use "PosTotalVar")
;; 12
(use "RatTotalVar")
;; 13
(use "RatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; ContComposeCorr
(set-goal "all f,f0(
     Cont f0 -> 
     f0 doml<=f0 domr -> 
     Cont f -> 
     f doml<=f domr -> f0 doml<=f lb -> f ub<=f0 domr -> Cont(ContComp f0 f))")
(assume "f" "f0" "f0Cont" "f0c<=d" "fCont" "fc<=d" "dom1" "dom2")
(intro 0)
(assume "a" "bd1" "bd2")
(ng #t)
(assert "Cauchy
([n]
  f0 approx
  ((RealConstr([n0]f approx a n0)f uMod)seq n max f0 doml min f0 domr)
  n)
([p]
  f0 uMod(p+1)max
  (RealConstr([n0]f approx a n0)f uMod)mod(PosPred(f0 uModCont(p+1))))")
(use "RealConstrToCauchy")
(simp "<-" "AppContOne0CompRule")
(use "ContReal")
(use "f0Cont")
(use "f0c<=d")
(intro 0)
(ng #t)
(use "ContElim1")
(use "fCont")
(use "bd1")
(use "bd2")
(ng #t)
(intro 0)
(assume "p" "q" "pq")
(use "ContElim3")
(use "fCont")
(use "pq")
(ng #t)
(assert "all n (f approx a n max f0 doml min f0 domr = f approx a n)")
(assume "n")
(use "RatMaxMinEq")
(use "RatLeTrans" (pt "f lb"))
(use "dom1")
(use "ContElim5")
(use "fCont")
(use "bd1")
(use "bd2")
(use "RatLeTrans" (pt "f ub"))
(use "ContElim6")
(use "fCont")
(use "bd1")
(use "bd2")
(use "dom2")
(assume "eq" "cauchy")
(intro 0)
(assume "p" "n" "m" "nB" "mB")
(ng #t)
(simp-with "<-" "eq" (pt "n"))
(simp-with "<-" "eq" (pt "m"))
(use-with
 "CauchyElim"
 (pt "([n] f0 approx(f approx a n max f0 doml min f0 domr) n)")
 (pt "([p] f0 uMod(PosS p)max f uMod(PosPred(f0 uModCont(PosS p))))")
 "?" (pt "p") (pt "n") (pt "m") "?" "?")
(use "cauchy")
(use "nB")
(use "mB")
(assume "a" "b" "p" "n" "bd1" "bd2" "bd3" "bd4")
(ng #t)
(assume "nDef" "abs")
(use "ContElim2")
(use "f0Cont")
(use "RatLeTrans" (pt "f lb"))
(use "dom1")
(use "ContElim5")
(use "fCont")
(use "bd1")
(use "bd2")
(use "RatLeTrans" (pt "f ub"))
(use "ContElim6")
(use "fCont")
(use "bd1")
(use "bd2")
(use "dom2")
(use "RatLeTrans" (pt "f lb"))
(use "dom1")
(use "ContElim5")
(use "fCont")
(use "bd3")
(use "bd4")
(use "RatLeTrans" (pt "f ub"))
(use "ContElim6")
(use "fCont")
(use "bd3")
(use "bd4")
(use "dom2")
(use "NatLeTrans"
 (pt "f0 uMod(PosS p)max f uMod(PosPred(f0 uModCont(PosS p)))"))
(use "NatLeTrans" (pt "f0 uMod(PosS p)"))
(use "ContElim3")
(use "f0Cont")
(search)
(use "NatMaxUB1")
(use "nDef")
(use "ContElim2")
(use "fCont")
(use "bd1")
(use "bd2")
(use "bd3")
(use "bd4")
(use "NatLeTrans" (pt "f uMod(PosPred(f0 uModCont(PosS p)))"))
(use "ContElim3")
(use "fCont")
(use "PosLeMonPred")
(use "ContElim4")
(use "f0Cont")
(search)
(use "NatLeTrans"
     (pt "f0 uMod(PosS p)max f uMod(PosPred(f0 uModCont(PosS p)))"))
(use "NatMaxUB2")
(use "nDef")
(use "abs")
(assume "p" "q")
(assume "pq")
(ng #t)
(use "NatLeMonMax")
(use "ContElim3")
(use "f0Cont")
(ng #t)
(use "pq")
(use "ContElim3")
(use "fCont")
(use "PosLeMonPred")
(use "ContElim4")
(use "f0Cont")
(ng #t)
(use "pq")
(assume "p" "q" "pq")
(ng #t)
(use "ContElim4")
(use "fCont")
(use "PosLeMonPred")
(use "ContElim4")
(use "f0Cont")
(use "pq")
(assume "a" "n" "bd1" "bd2")
(ng #t)
(use "ContElim5")
(use "f0Cont")
(use "RatLeTrans" (pt "f lb"))
(use "dom1")
(use "ContElim5")
(use "fCont")
(use "bd1")
(use "bd2")
(use "RatLeTrans" (pt "f ub"))
(use "ContElim6")
(use "fCont")
(use "bd1")
(use "bd2")
(use "dom2")
(assume "a" "n" "bd1" "bd2")
(ng #t)
(use "ContElim6")
(use "f0Cont")
(use "RatLeTrans" (pt "f lb"))
(use "dom1")
(use "ContElim5")
(use "fCont")
(use "bd1")
(use "bd2")
(use "RatLeTrans" (pt "f ub"))
(use "ContElim6")
(use "fCont")
(use "bd1")
(use "bd2")
(use "dom2")
;; Proof finished.
;; (cdp)
(save "ContComposeCorr")

;; ContComposeCorr2
(set-goal "all f,f0(
     Cont f0 -> 
     f0 doml<=f0 domr -> 
     Cont f -> 
     f doml<=f domr -> 
     f0 doml<=f lb -> 
     f ub<=f0 domr -> all x(Real x -> ContComp f0 f x===f0(f x)))")
(assume "f" "f0" "f0Cont" "f0c<=d" "fCont" "fc<=d" "dom1" "dom2" "x" "x_r")
(use "RealEqChar2")
(use "ContReal")
(use "ContComposeCorr")
(use "f0Cont")
(use "f0c<=d")
(use "fCont")
(use "fc<=d")
(use "dom1")
(use "dom2")
(ng #t)
(use "fc<=d")
(use "x_r")
(use "ContReal")
(use "f0Cont")
(use "f0c<=d")
(use "ContReal")
(use "fCont")
(use "fc<=d")
(use "x_r")
(assume "p")
(intro 0 (pt "Zero"))
(assume "n" "stupid")
(ng #t)
(simp (pf "f approx(x seq n max f doml min f domr)n max f0 doml min f0 domr =
 f approx(x seq n max f doml min f domr)n"))
(assert "all a(a + ~a == 0)")
(assume "a")
(ng #t)
(use "Truth")
(assume "RatPlusMinusZero")
(simprat "RatPlusMinusZero")
(ng #t)
(use "Truth")
(use "RatMaxMinEq")
(use "RatLeTrans" (pt "f lb"))
(use "dom1")
(use "ContElim5")
(use "fCont")
(use "RatMaxMinUB")
(use "fc<=d")
(use "RatMaxMinLB")
(use "fc<=d")
(use "RatLeTrans" (pt "f ub"))
(use "ContElim6")
(use "fCont")
(use "RatMaxMinUB")
(use "fc<=d")
(use "RatMaxMinLB")
(use "fc<=d")
(use "dom2")
;; Proof finished.
;; (cdp)
(save "ContComposeCorr2")

;; ContLim
(set-goal "all xs,x,M,f(
     Cont f -> 
     f doml<=f domr -> 
     all p 1<f uModCont p -> 
     RealConv xs x M -> RealConv([n]f(xs n))(f x)([p]M(f uModCont p)))")
(assume "xs" "x" "M" "f" "fCont" "c<=d" "ompos" "conv")
(intro 0)
(assume "n")
(use "ContReal")
(use "fCont")
(use "c<=d")
(use "RealConvElim1" (pt "x") (pt "M"))
(use "conv")
(use "ContReal")
(use "fCont")
(use "c<=d")
(use "RealConvElim2" (pt "xs") (pt "M"))
(use "conv")
(intro 0)
(assume "p" "q")
(assume "pq")
(ng #t)
(use "MonElim")
(use "RealConvElim3" (pt "xs") (pt "x"))
(use "conv")
(use "ContElim4")
(use "fCont")
(use "pq")
(assume "p" "n")
(assume "Mp")
(use "ContMod")
(use "fCont")
(use "c<=d")
(use "ompos")
(use "RealConvElim1" (pt "x") (pt "M"))
(use "conv")
(use "RealConvElim2" (pt "xs") (pt "M"))
(use "conv")
(use "RealConvElim4" (pt "M"))
(use "conv")
(use "Mp")
;;(cdp)
(save "ContLim")

;; ContRat
(set-goal "all f,f0(
     Cont f -> 
     f doml<=f domr -> 
     all p 1<f uModCont p -> 
     Cont f0 -> 
     f0 doml<=f0 domr -> 
     all p 1<f0 uModCont p -> 
     all a f a===f0 a -> all x(Real x -> f x===f0 x))")
(assume
 "f" "f0" "fCont" "fc<=d" "fompos" "f0Cont" "f0c<=d" "f0ompos" "eqQ" "x" "x_r")
(assert "all x, p, n (Real x -> x mod p<=n -> abs(x seq n + ~x)<<=1#2**p)")
(cases)
(use "RatCauchyConvMod")
(assume "RealCauchyConv1")
(use "RealConvEq" (pt "([n] f (x seq n))") (pt "([n] f0 (x seq n))")
 (pt "([p] x mod (f uModCont p))") (pt "([p] x mod (f0 uModCont p))"))
(assume "n")
(use "eqQ")
(inst-with-to
 "ContLim" (pt "([n]RealConstr([n0]x seq n)([p] Zero))") (pt "x") (pt "x mod")
 (pt "f") "fCont" "fc<=d" "fompos" "Ass") ;here ContLim is used
(use "Ass")
(intro 0)
(assume "n")
(ng #t)
(autoreal)
(use "RealToMon")
(use "x_r")
(assume "p" "n" "nB")
(ng #t)
(use "RealCauchyConv1")
(use "x_r")
(use "nB")
(inst-with-to "ContLim"
 (pt "([n]RealConstr([n0]x seq n)([p] Zero))")
 (pt "x") (pt "x mod") (pt "f0") "f0Cont" "f0c<=d" "f0ompos" "Ass")
(use "Ass")
(intro 0)
(assume "n")
(ng #t)
(autoreal)
(use "RealToMon")
(use "x_r")
(assume "p" "n" "nB")
(ng #t)
(use "RealCauchyConv1")
(use "x_r")
(use "nB")
;; Proof finished.
;; (cdp)
(save "ContRat")

