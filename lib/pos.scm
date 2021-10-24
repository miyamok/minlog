;; 2021-10-20.  pos.scm

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(display "loading pos.scm ...") (newline)

;; (remove-nat-tokens) removes all tokens added in nat.scm and from
;; DISPLAY-FUNCTIONS all items (nat proc).  The reason is that they
;; will be reintroduced here, with a different assigned procedure.

(remove-nat-tokens)
(add-display (py "nat") (make-display-creator1 "ListLength" "Lh" 'prefix-op))

;; The functions make-numeric-term (used by the parser) and
;; is-numeric-term?, numeric-term-to-number (used by term-to-expr and
;; token-tree-to-string) take pos as default.

(set! NAT-NUMBERS #f)

;; 1.  Positive numbers
;; ====================

;; We want to overload operators like +,*,/,<=,<, and automatically
;; raise the type of arguments when reading.  For instance, + should
;; take its arguments, compute the lub rho of their types, raise the
;; type of both arguments to type rho, apply RhoPlus to the results.
;; Moreover, a number should be displayed at the lowest possible level.
;; ppn (pretty print with names) displays the actually used functions.

(add-algs "pos" '("One" "pos") '("SZero" "pos=>pos") '("SOne" "pos=>pos"))
(add-var-name "p" "q" "r" (py "pos"))

(add-totality "pos")
(add-totalnc "pos")
(add-co "TotalPos")
(add-co "TotalPosNc")

(add-eqp "pos")
(add-co "EqPPos")
(add-eqpnc "pos")
(add-co "EqPPosNc")

;; PosTotalVar
(set-goal "all p TotalPos p")
(use "AllTotalIntro")
(assume "p^" "Tp")
(use "Tp")
;; Proof finished.
;; (cdp)
(save "PosTotalVar")

;; Alternative proof:
;; (set-goal "all p TotalPos p")
;; (ind)
;; (use "TotalPosOne")
;; (assume "p" "Tp")
;; (use "TotalPosSZero")
;; (use "Tp")
;; (assume "p" "Tp")
;; (use "TotalPosSOne")
;; (use "Tp")

;; PosEqToEqD
(set-goal "all p,q(p=q -> p eqd q)")
(ind) ;2-4
(cases) ;5-7
(assume "Useless")
(use "InitEqD")
;; 6
(assume "p" "1=SZero p")
(use "EfEqD")
(use "1=SZero p")
;; 7
(assume "p" "1=SOne p")
(use "EfEqD")
(use "1=SOne p")
;; 3
(assume "p" "IH1")
(cases) ;14-16
(assume "SZero p=1")
(use "EfEqD")
(use "SZero p=1")
;; 15
(assume "q" "SZero p=SZero q")
(assert "p eqd q")
 (use "IH1")
 (use "SZero p=SZero q")
(assume "p eqd q")
(elim "p eqd q")
(strip)
(use "InitEqD")
;; 18
(assume "q" "SZero p=SOne q")
(use "EfEqD")
(use "SZero p=SOne q")
;; 4
(assume "p" "IH1")
(cases) ;29-31
(assume "SOne p=1")
(use "EfEqD")
(use "SOne p=1")
;; 30
(assume "q" "SOne p=SZero q")
(use "EfEqD")
(use "SOne p=SZero q")
;; 31
(assume "q" "SOne p=SOne q")
(assert "p eqd q")
 (use "IH1")
 (use "SOne p=SOne q")
(assume "p eqd q")
(elim "p eqd q")
(strip)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "PosEqToEqD")

;; PosIfTotal
(set-goal "allnc p^(TotalPos p^ ->
 allnc alpha^,(pos=>alpha)^1,(pos=>alpha)^2(
 Total alpha^ ->
 allnc p^1(TotalPos p^1 -> Total((pos=>alpha)^1 p^1)) ->
 allnc p^1(TotalPos p^1 -> Total((pos=>alpha)^2 p^1)) ->
 Total[if p^ alpha^ (pos=>alpha)^1 (pos=>alpha)^2]))")
(assume "p^" "Tp" "alpha^" "(pos=>alpha)^1" "(pos=>alpha)^2"
	"Talpha" "Tf1" "Tf2")
(elim "Tp")
(use "Talpha")
(assume "p^1" "Tp1" "Useless")
(ng #t)
(use "Tf1")
(use "Tp1")
(assume "p^1" "Tp1" "Useless")
(ng #t)
(use "Tf2")
(use "Tp1")
;; Proof finished.
;; (cdp)
(save "PosIfTotal")

;; To prove extensionality of pconsts of level >=2 we will need
;; properties of EqPPos.  There are collected here.

;; EqPPosRefl
(set-goal "allnc p^(TotalPos p^ -> EqPPos p^ p^)")
(assume "p^" "Tp")
(elim "Tp")
(use "EqPPosOne")
(assume "p^1" "Tp1")
(use "EqPPosSZero")
(assume "p^1" "Tp1")
(use "EqPPosSOne")
;; Proof finished.
;; (cdp)
(save "EqPPosRefl")

;; EqPPosToTotalLeft
(set-goal "allnc p^,q^(EqPPos p^ q^ -> TotalPos p^)")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
;; 3-5
(use "TotalPosOne")
;; 4
(assume "p^1" "q^1" "EqPp1q1" "IH")
(use "TotalPosSZero")
(use "IH")
;; 5
(assume "p^1" "q^1" "EqPp1q1" "IH")
(use "TotalPosSOne")
(use "IH")
;; Proof finished.
;; (cdp)
(save "EqPPosToTotalLeft")

;; EqPPosToTotalRight
(set-goal "allnc p^,q^(EqPPos p^ q^ -> TotalPos q^)")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
;; 3-5
(use "TotalPosOne")
;; 4
(assume "p^1" "q^1" "EqPp1q1" "IH")
(use "TotalPosSZero")
(use "IH")
;; 5
(assume "p^1" "q^1" "EqPp1q1" "IH")
(use "TotalPosSOne")
(use "IH")
;; Proof finished.
;; (cdp)
(save "EqPPosToTotalRight")

;; EqPPosToEqD
(set-goal "allnc p^,q^(EqPPos p^ q^ -> p^ eqd q^)")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
;; 3-5
(use "InitEqD")
;; 4
(assume "p^1" "q^1" "Useless" "IH")
(simp "IH")
(use "InitEqD")
;; 5
(assume "p^1" "q^1" "Useless" "IH")
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "EqPPosToEqD")

;; EqPPosSym
(set-goal "allnc p^,q^(EqPPos p^ q^ -> EqPPos q^ p^)")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
(use "EqPPosOne")
(assume "p^1" "q^1" "EqPp1q1" "EqPq1p1")
(use "EqPPosSZero")
(use "EqPq1p1")
(assume "p^1" "q^1" "EqPp1q1" "EqPq1p1")
(use "EqPPosSOne")
(use "EqPq1p1")
;; Proof finished.
;; (cdp)
(save "EqPPosSym")

(add-var-name "f" (py "pos=>alpha=>alpha"))

;; PosRecTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(Rec pos=>alpha)"))))
(assume "p^" "Tp" "alpha^" "Talpha" "f^1" "Tf1" "f^2" "Tf2")
(elim "Tp") 
;;3-5
(ng #t)
(use "Talpha")
;; 4
(assume "p^1" "Tp1" "IH")
(ng #t)
(use "Tf1")
(use "Tp1")
(use "IH")
;; 5
(assume "p^1" "Tp1" "IH")
(ng #t)
(use "Tf2")
(use "Tp1")
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosRecTotal")

(remove-var-name "f")

;; make-numeric-term-wrt-pos produces a pos object for a positive
;; integer.

(define (make-numeric-term-wrt-pos n)
  (cond ((= n 1) (pt "One"))
	((even? n) (make-term-in-app-form
		    (make-term-in-const-form (constr-name-to-constr "SZero"))
		    (make-numeric-term-wrt-pos (/ n 2))))
	((odd? n) (make-term-in-app-form
		   (make-term-in-const-form (constr-name-to-constr "SOne"))
		   (make-numeric-term-wrt-pos (/ (- n 1) 2))))
	(else
	 (myerror "make-numeric-term-wrt-pos" "positive integer expected" n))))

(define (make-numeric-term n)
  (if NAT-NUMBERS
      (make-numeric-term-wrt-nat n)
      (make-numeric-term-wrt-pos n)))

;; (define (make-numeric-term n)
;;   (if (not (and (integer? n) (positive? n)))
;;       (myerror "make-numeric-term" "positive integer expected" n)
;;       (make-numeric-term-wrt-pos n)))
(define is-numeric-term? is-numeric-term-wrt-pos?)
(define numeric-term-to-number numeric-term-wrt-pos-to-number)

;; To use external code in a pconst, we provide tests for numeral
;; values and conversion operations from numerals values to numbers,
;; for pos and nat.

(define (pos-numeral-value? value)
  (and (nbe-constr-value? value)
       (let* ((name (nbe-constr-value-to-name value))
	      (args (nbe-constr-value-to-args value))
	      (vals (map nbe-object-to-value args)))
	 (or (string=? "One" name)
	     (and (or (string=? "SZero" name) (string=? "SOne" name))
		  (pair? vals)
		  (pos-numeral-value? (car vals)))))))

(define (pos-numeral-value-to-number value)
  (let* ((name (nbe-constr-value-to-name value))
	 (args (nbe-constr-value-to-args value))
	 (vals (map nbe-object-to-value args)))
    (if (string=? "One" name)
	1
	(let ((prev (pos-numeral-value-to-number (car vals))))
	  (if (string=? "SZero" name) (* 2 prev) (+ (* 2 prev) 1))))))

(define (nat-numeral-value? value)
  (and (nbe-constr-value? value)
       (let* ((name (nbe-constr-value-to-name value))
	      (args (nbe-constr-value-to-args value))
	      (vals (map nbe-object-to-value args)))
	 (or (string=? "Zero" name)
	     (and (string=? "Succ" name)
		  (pair? vals)
		  (nat-numeral-value? (car vals)))))))

(define (nat-numeral-value-to-number value)
  (let* ((name (nbe-constr-value-to-name value))
	 (args (nbe-constr-value-to-args value))
	 (vals (map nbe-object-to-value args)))
    (if (string=? "Zero" name)
	1
	(+ 1 (nat-numeral-value-to-number (car vals))))))

;; Instead of the converse use pt.

;; 2. Parsing and display for arithmetical operations
;; ==================================================

;; We have the subtype relation pos < nat.

(add-program-constant "PosToNat" (py "pos=>nat"))

(add-item-to-algebra-edge-to-embed-term-alist
 "pos" "nat"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (pconst-name-to-pconst "PosToNat"))
         (make-term-in-var-form var)))))

;; (alg-le? (make-alg "pos") (make-alg "nat"))
;; (alg-le? (make-alg "nat") (make-alg "pos"))

(add-program-constant "PosS" (py "pos=>pos"))
(add-program-constant "PosPred" (py "pos=>pos"))
(add-program-constant "PosHalf" (py "pos=>pos"))

;; We define an overloaded addition.

(add-program-constant "PosPlus" (py "pos=>pos=>pos"))

;; We define a cut-off subtraction for pos (as we have it for nat).

(add-program-constant "PosMinus" (py "pos=>pos=>pos"))

;; We define an overloaded multiplication.

(add-program-constant "PosTimes" (py "pos=>pos=>pos"))

;; We define the exponential with values in pos and nat

(add-program-constant "PosExp" (py "pos=>nat=>pos"))
(add-program-constant "NatExp" (py "nat=>nat=>nat"))

;; We define the overloaded maximum function, written infix:

(add-program-constant "PosMax" (py "pos=>pos=>pos"))

;; We define the overloaded minimum function, written infix:

(add-program-constant "PosMin" (py "pos=>pos=>pos"))

;; We define an overloaded less-than relation.

(add-program-constant "PosLt" (py "pos=>pos=>boole"))

;; We define an overloaded less-than-or-equal relation.

(add-program-constant "PosLe" (py "pos=>pos=>boole"))

;; We define the logarithm os a positive number

(add-program-constant "PosLog" (py "pos=>nat"))

;; Program constants used for extraction of program constants to
;; Haskell, where computation rules
;;
;;    f (SZero x) = ... x ...
;
;; must be transformed into
;;    f n | even n = ... TranslationPosHalfEven n ...
;;
;; etc.  Notice that we always know that n is an even number, so that
;; the remainder is zero, and similarly for minus and predecessor. Not
;; meant to be used directly by the user.

(add-program-constant "TranslationPosHalfEven" (py "pos=>pos"))
(add-program-constant "TranslationPosNegForInt" (py "pos=>pos"))
(add-program-constant "TranslationPosPredNonOne" (py "pos=>pos"))

;; We define the tokens that are used by the parser

(add-token "+" 'add-op (make-term-creator "+" "pos"))
(add-token-and-type-to-name "+" (py "pos") "PosPlus")
(add-token-and-type-to-name "+" (py "nat") "NatPlus")

(add-token "--" 'add-op (make-term-creator "--" "pos"))
(add-token-and-type-to-name "--" (py "pos") "PosMinus")
(add-token-and-type-to-name "--" (py "nat") "NatMinus")

(add-token "*" 'mul-op (make-term-creator "*" "pos"))
(add-token-and-type-to-name "*" (py "pos") "PosTimes")
(add-token-and-type-to-name "*" (py "nat") "NatTimes")

(add-token "**" 'exp-op (make-term-creator-exp "**"))

(add-token-and-types-to-name "**" (list (py "pos") (py "pos")) "PosExp")
(add-token-and-types-to-name "**" (list (py "pos") (py "nat")) "PosExp")

(add-token-and-types-to-name "**" (list (py "nat") (py "pos")) "NatExp")
(add-token-and-types-to-name "**" (list (py "nat") (py "nat")) "NatExp")

(add-token "max" 'mul-op (make-term-creator "max" "pos"))
(add-token-and-type-to-name "max" (py "pos") "PosMax")
(add-token-and-type-to-name "max" (py "nat") "NatMax")

(add-token "min" 'mul-op (make-term-creator "min" "pos"))
(add-token-and-type-to-name "min" (py "pos") "PosMin")
(add-token-and-type-to-name "min" (py "nat") "NatMin")

(add-token "<" 'rel-op (make-term-creator "<" "pos"))
(add-token-and-type-to-name "<" (py "pos") "PosLt")
(add-token-and-type-to-name "<" (py "nat") "NatLt")

(add-token "<=" 'rel-op (make-term-creator "<=" "pos"))
(add-token-and-type-to-name "<=" (py "pos") "PosLe")
(add-token-and-type-to-name "<=" (py "nat") "NatLe")

(add-display (py "pos") (make-display-creator "PosPlus" "+" 'add-op))
(add-display (py "nat") (make-display-creator "NatPlus" "+" 'add-op))

(add-display (py "pos") (make-display-creator "PosMinus" "--" 'add-op))
(add-display (py "nat") (make-display-creator "NatMinus" "--" 'add-op))

(add-display (py "pos") (make-display-creator "PosTimes" "*" 'mul-op))
(add-display (py "nat") (make-display-creator "NatTimes" "*" 'mul-op))

(add-display (py "pos") (make-display-creator "PosExp" "**" 'exp-op))
(add-display (py "nat") (make-display-creator "NatExp" "**" 'exp-op))

(add-display (py "pos") (make-display-creator "PosMax" "max" 'mul-op))
(add-display (py "nat") (make-display-creator "NatMax" "max" 'mul-op))

(add-display (py "pos") (make-display-creator "PosMin" "min" 'mul-op))
(add-display (py "nat") (make-display-creator "NatMin" "min" 'mul-op))

(add-display (py "boole") (make-display-creator "PosLt" "<" 'rel-op))
(add-display (py "boole") (make-display-creator "NatLt" "<" 'rel-op))

(add-display (py "boole") (make-display-creator "PosLe" "<=" 'rel-op))
(add-display (py "boole") (make-display-creator "NatLe" "<=" 'rel-op))

;; 3. Arithmetic for positive numbers
;; ==================================

;; BooleEqTotal is proved in ets.scm.  NatEqTotal is proved in nat.scm

;; PosEqTotal
(set-goal "allnc p^(
 TotalPos p^ -> allnc q^(TotalPos q^ -> TotalBoole(p^ =q^)))")
(assume "p^" "Tp")
(elim "Tp")
(assume "q^" "Tq")
(elim "Tq")
(use "TotalBooleTrue")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(use "TotalBooleFalse")
(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "IHp1")
(use "Tq1")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(use "TotalBooleFalse")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")
(assume "q^1" "Tq1" "Useless")
(use "IHp1")
(use "Tq1")
;; Proof finished.
;; (cdp)
(save "PosEqTotal")

;; Rules for PosS

(add-computation-rules
 "PosS One" "SZero One"
 "PosS(SZero p)" "SOne p"
 "PosS(SOne p)" "SZero(PosS p)")

;; PosSTotal
(set-totality-goal "PosS")
(assume "p^" "Tp")
(elim "Tp")
;; ?_3:TotalPos(PosS 1)
(ng #t)
(use "TotalPosSZero")
(use "TotalPosOne")
;; ?_4:allnc p^(
;;      TotalPos p^ -> TotalPos(PosS p^) -> TotalPos(PosS(SZero p^)))
(assume "q^" "Tq" "TSq")
(ng #t)
(use "TotalPosSOne")
(use "Tq")
;; ?_5:allnc p^(
;;      TotalPos p^ -> TotalPos(PosS p^) -> TotalPos(PosS(SOne p^)))
(assume "q^" "Tq" "TSq")
(ng #t)
(use "TotalPosSZero")
(use "TSq")
;; Proof finished.
;; (cdp)
(save-totality)

;; PosSEqP
(set-goal "allnc p^,q^(EqPPos p^ q^ -> EqPPos(PosS p^)(PosS q^))")
(assume "p^" "q^" "EqPpq")
(simp "<-" (pf "p^ eqd q^"))
(use "EqPPosRefl")
(use "PosSTotal")
(use "EqPPosToTotalLeft" (pt "q^"))
(use "EqPpq")
;; 4
(use "EqPPosToEqD")
(use "EqPpq")
;; Proof finished.
;; (cdp)
(save "PosSEqP")

;; Rules for PosPred

(add-computation-rules
 "PosPred One" "One"
 "PosPred(SZero One)" "One"
 "PosPred(SZero(SZero p))" "SOne(PosPred(SZero p))"
 "PosPred(SZero(SOne p))" "SOne(SZero p)"
 "PosPred(SOne p)" "SZero p")

;; PosPredTotal
(set-totality-goal "PosPred")
(assume "p^" "Tp")
(elim "Tp")
;; ?_3:TotalPos(PosPred 1)
(ng #t)
(use "TotalPosOne")
;; allnc p^(TotalPos p^ -> TotalPos(PosPred p^) -> TotalPos(PosPred(SZero p^)))
(assume "q^" "Tq" "TPq")
(ng #t)
(elim "Tq")
;; ?_9:TotalPos(PosPred 2)
(ng #t)
(use "TotalPosOne")
;; ?_10:allnc p^(
;;       TotalPos p^ -> 
;;       TotalPos(PosPred(SZero p^)) -> TotalPos(PosPred(SZero(SZero p^))))
(assume "q^0" "Tq0" "TPSZq0")
(ng #t)
(use "TotalPosSOne")
(use "TPSZq0")
;; ?_11:allnc p^(
;;       TotalPos p^ -> 
;;       TotalPos(PosPred(SZero p^)) -> TotalPos(PosPred(SZero(SOne p^))))
(assume "q^1" "Tq1" "TPSZq1")
(ng #t)
(use "TotalPosSOne")
(use "TotalPosSZero")
(use "Tq1")
;; allnc p^(TotalPos p^ -> TotalPos(PosPred p^) -> TotalPos(PosPred(SOne p^)))
(assume "q^" "Tq" "TPq")
(ng #t)
(use "TotalPosSZero")
(use "Tq")
;; Proof finished.
;; (cdp)
(save-totality)

;; PosPredEqP
(set-goal "allnc p^,q^(EqPPos p^ q^ -> EqPPos(PosPred p^)(PosPred q^))")
(assume "p^" "q^" "EqPpq")
(simp "<-" (pf "p^ eqd q^"))
(use "EqPPosRefl")
(use "PosPredTotal")
(use "EqPPosToTotalLeft" (pt "q^"))
(use "EqPpq")
;; 4
(use "EqPPosToEqD")
(use "EqPpq")
;; Proof finished.
;; (cdp)
(save "PosPredEqP")

;; Rules for PosHalf

(add-computation-rules
 "PosHalf One" "One"
 "PosHalf(SZero p)" "p"
 "PosHalf(SOne p)" "p")

;; PosHalfTotal
(set-totality-goal "PosHalf")
(assume "p^" "Tp")
(elim "Tp")
;; ?_3:TotalPos(PosHalf 1)
(ng #t)
(use "TotalPosOne")
;; ?_4:allnc p^(
;;      TotalPos p^ ->
;;      TotalPos(PosHalf p^) -> TotalPos(PosHalf(SZero p^)))
(assume "q^" "Tq" "THq")
(ng #t)
(use "Tq")
;; ?_5:allnc p^(
;;      TotalPos p^ ->
;;      TotalPos(PosHalf p^) -> TotalPos(PosHalf(SOne p^)))
(assume "q^" "Tq" "THq")
(ng #t)
(use "Tq")
;; Proof finished.
;; (cdp)
(save-totality)

;; Rules for PosToNat

(add-computation-rules
 "PosToNat One" "Succ Zero"
 "PosToNat(SZero p)" "NatDouble(PosToNat p)"
 "PosToNat(SOne p)" "Succ(PosToNat(SZero p))")

;; PosToNatTotal
(set-totality-goal "PosToNat")
(assume "p^" "Tp")
(elim "Tp") ;3-5
(use "TotalNatSucc")
(use "TotalNatZero")
;; 4
(assume "p^1" "Tp1" "IH")
(ng #t)
(use "NatDoubleTotal")
(use "IH")
;; 5
(assume "p^1" "Tp1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "NatDoubleTotal")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

(replace-item-in-algebra-edge-to-embed-term-alist
 "pos" "nat"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
	 (make-term-in-const-form
	  (pconst-name-to-pconst "PosToNat"))
	 (make-term-in-var-form var)))))

;; We define the inverse NatToPos of PosToNat , using GRec

;; (add-program-constant "NatToPosStep" (py "nat=>(nat=>pos)=>pos"))

;; ;; Rules for NatToPosStep

;; (add-computation-rules
;;  "NatToPosStep n(nat=>pos)"
;;  "[if (n<=Succ Zero) One
;;       [if (NatEven n)
;;  	  (SZero((nat=>pos)(NatHalf n)))
;; 	  (SOne((nat=>pos)(NatHalf n)))]]")

;; (add-computation-rules
;;  "NatToPosStep n(nat=>pos)"
;;  "[if (NatEven n)
;;       (SZero((nat=>pos)(NatHalf n)))
;;       [if (n=Succ Zero) One (SOne((nat=>pos)(NatHalf n)))]]")

;; ;; NatToPosStepTotal
;; (set-totality-goal "NatToPosStep")
;; (fold-alltotal)
;; (assume "n")
;; (fold-alltotal)
;; (assume "nat=>pos")
;; (ng #t)
;; (use "BooleIfTotal")
;; (use "TotalVar")
;; (use "TotalVar")
;; (use "BooleIfTotal")
;; (use "TotalVar")
;; (use "TotalVar")
;; (use "TotalVar")
;; ;; Proof finished.
;; ;; (cdp)
;; (save-totality)

;; ;; NatToPosStepTotal
;; (set-totality-goal "NatToPosStep")
;; (assume "nat^" "Tnat" "(nat=>pos)^" "Th")
;; (ng #t)
;; (use "BooleIfTotal")
;; (use "NatEvenTotal")
;; (use "Tnat")
;; (use "TotalPosSZero")
;; (use "Th")
;; (use "NatHalfTotal")
;; (use "Tnat")
;; (use "BooleIfTotal")
;; (use "NatEqTotal")
;; (use "Tnat")
;; (use "TotalNatSucc")
;; (use "TotalNatZero")
;; (use "TotalPosOne")
;; (use "TotalPosSOne")
;; (use "Th")
;; (use "NatHalfTotal")
;; (use "Tnat")
;; ;; Proof finished.
;; ;; (cdp)
;; (save-totality)

(add-program-constant "NatToPos" (py "nat=>pos"))

;; Rules for NatToPos

(add-computation-rules
 "NatToPos n"
 "(GRec nat pos)([n]n)n ([n,nat=>pos][if (n<=Succ Zero) One
    [if (NatEven n)
	(SZero((nat=>pos)(NatHalf n)))
	(SOne((nat=>pos)(NatHalf n)))]])")

;; (add-computation-rules
;;  "NatToPos n" "(GRec nat pos)([n]n)n NatToPosStep")

;; NatToPosTotal
(set-totality-goal "NatToPos")
(fold-alltotal)
(assume "n")
(ng #t)
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "TotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; Use cNatPos instead of the pconst NatToPos to block unwanted unfoldings

;; NatPos
(set-goal "all n exl p p=NatToPos n")
(assume "n")
(intro 0 (pt "NatToPos n"))
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatPos")

(animate "NatPos")

;; NatPosExFree
(set-goal "all n cNatPos n=NatToPos n")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatPosExFree")

(deanimate "NatPos")

(set-totality-goal "cNatPos")
(fold-alltotal)
(assume "n")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save "cNatPosTotal")

;; Rules for PosPlus

(add-computation-rules
 "p+One" "PosS p"
 "One+SZero p" "SOne p"
 "SZero p+SZero q" "SZero(p+q)"
 "SOne p+SZero q" "SOne(p+q)"
 "One+SOne p" "SZero(PosS p)"
 "SZero p+SOne q" "SOne(p+q)"
 "SOne p+SOne q" "SZero(PosS(p+q))")

;; PosPlusTotal
(set-totality-goal "PosPlus")
(assume "p^" "Tp")
(elim "Tp")

;; ?_3:allnc p^(TotalPos p^ -> TotalPos(1+p^))
(assume "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosSZero")
(use "TotalPosOne")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSOne")
(use "Tq1")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "PosSTotal")
(use "Tq1")
;; ?_4:allnc p^(
;;      TotalPos p^ -> 
;;      allnc p^0(TotalPos p^0 -> TotalPos(p^ +p^0)) -> 
;;      allnc p^0(TotalPos p^0 -> TotalPos(SZero p^ +p^0)))
(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "TotalPosSOne")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSOne")
(use "IHq")
(use "Tq2")
;; ?_5:allnc p^(
;;      TotalPos p^ -> 
;;      allnc p^0(TotalPos p^0 -> TotalPos(p^ +p^0)) -> 
;;      allnc p^0(TotalPos p^0 -> TotalPos(SOne p^ +p^0)))
(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "TotalPosSZero")
(use "PosSTotal")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSOne")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "PosSTotal")
(use "IHq")
(use "Tq2")
;; Proof finished.
;; (cdp)
(save-totality)

;; PosPlusEqP
(set-goal "allnc p^1,q^1(EqPPos p^1 q^1 -> allnc p^2,q^2(EqPPos p^2 q^2 ->
 EqPPos(p^1+p^2)(q^1+q^2)))")
(assume "p^1" "q^1" "EqPp1q1" "p^2" "q^2" "EqPp2q2")
(simp "<-" (pf "p^1 eqd q^1"))
(simp "<-" (pf "p^2 eqd q^2"))
(use "EqPPosRefl")
(use "PosPlusTotal")
(use "EqPPosToTotalLeft" (pt "q^1"))
(use "EqPp1q1")
(use "EqPPosToTotalLeft" (pt "q^2"))
(use "EqPp2q2")
;; 6
(use "EqPPosToEqD")
(use "EqPp2q2")
;; 4
(use "EqPPosToEqD")
(use "EqPp1q1")
;; Proof finished.
;; (cdp)
(save "PosPlusEqP")

;; NatLtZeroPos
(set-goal "all p Zero<p")
(ind)
(use "Truth")
(ng #t)
(assume "p" "0<p")
(use "NatLt0Double")
(use "0<p")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLtZeroPos")
(save "NatLt0Pos")

;; SZeroPosPlus
(set-goal "all p SZero p=p+p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(simp "<-" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "SZeroPosPlus")

;; We derive some rewrite rules.  To ensure termination, we (1) decrease
;; the sum of the lengths of summands, where the rhs counts more than
;; the lhs.

(set-goal "all p PosPred(PosS p)=p")
(ind) ;2-4
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH")
(ng #t)
(use "Truth")
;; 4
(cases) ;8-10
(ng #t)
(strip)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
(ng #t)
(assume "p" "Hyp")
(use "Hyp")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosPred(PosS p)" "p")

(set-goal "all p PosPred(SZero(PosS p))=SOne p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosPred(SZero(PosS p))" "SOne p")

(set-goal "all p PosS(PosPred(SZero p))=SZero p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosS(PosPred(SZero p))" "SZero p")

(set-goal "all p One+p=PosS p")
(cases)
(auto)
;; Proof finished
;; (cdp)
(add-rewrite-rule "One+p" "PosS p")

(set-goal "all p,q PosS p+q=PosS(p+q)")
(ind)
  (ind)
  (auto)
(assume "pos" "IHzero")
(ind)
  (auto)
(assume "pos" "IHone")
(ind)
(auto)
;; Proof finished
;; (cdp)
(add-rewrite-rule "PosS p+q" "PosS(p+q)")

(set-goal "all p,q p+PosS q=PosS(p+q)")
(ind)
  (cases)
(auto)
(assume "p" "IH1")
(cases)
  (auto)
(assume "p" "IH2")
(cases)
(auto)
;; Proof finished
;; (cdp)
(add-rewrite-rule "p+PosS q" "PosS(p+q)")

;; To prove "all p,q,r p+(q+r)=p+q+r" by
;; pos-induction seems to be difficult.  Solutions: (1) Using the rules
;; just proved one can mimic the proof in nat.  This requires
;; successor-induction for pos, which has to be proven before (see
;; wwwpublic/seminars/prosemss04/sucind.scm).  (2) Another more general
;; way out is to transfer the problem to nat via appropriate functions
;; and then use associativity in nat.  (For an alternative see
;; examples/ordinals/reflection_numbers_thms.scm)

;; GRecDef
(set-goal "all (nat=>nat),nat,(nat=>(nat=>pos)=>pos)
            (GRec nat pos)(nat=>nat)nat(nat=>(nat=>pos)=>pos)=
            (GRecGuard nat pos)(nat=>nat)nat(nat=>(nat=>pos)=>pos)True")
(assume "(nat=>nat)" "nat" "(nat=>(nat=>pos)=>pos)")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "GRecDef")

;; NatToPosEqSZeroNatToPosHalf
(set-goal "all n(Succ Zero<n -> NatEven n ->
                   NatToPos n=SZero(NatToPos(NatHalf n)))")
(assume "n" "1<n" "En")
(ng #t)
(assert "n<=Succ Zero -> F")
(assume "n<=1")
(assert "Succ Zero<Succ Zero")
(use "NatLtLeTrans" (pt "n"))
(use "1<n")
(use "n<=1")
(assume "Absurd")
(use "Absurd")
(assume "Not1<n")
(simp "Not1<n")
(ng #t)
(simp "En")
(ng #t)
(assert "NatHalf n<n")
 (use "NatHalfLt")
 (use "NatLtTrans" (pt "Succ Zero"))
 (use "Truth")
 (use "1<n")
(assume "NatHalf n<n")
(simp "NatHalf n<n")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatToPosEqSZeroNatToPosHalf")

;; NatToPosEqSOneNatToPosHalf
(set-goal "all n(Succ Zero<n -> (NatEven n -> F) -> 
                 NatToPos n=SOne(NatToPos(NatHalf n)))")
(assume "n" "1<n" "NotEn")
(ng #t)
(assert "n<=Succ Zero -> F")
(assume "n<=1")
(assert "Succ Zero<Succ Zero")
(use "NatLtLeTrans" (pt "n"))
(use "1<n")
(use "n<=1")
(assume "Absurd")
(use "Absurd")
(assume "NotLen1")
(simp "NotLen1")
(ng #t)
(simp "NotEn")
(ng #t)
(assert "NatHalf n<n")
(use "NatHalfLt")
(use "NatLtTrans" (pt "Succ Zero"))
(use "Truth")
(use "1<n")
(assume "NatHalf n<n")
(simp "NatHalf n<n")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatToPosEqSOneNatToPosHalf")

;; ;; NatToPosEqSOneNatToPosHalf
;; (set-goal "all n(Succ Zero<n -> (NatEven n -> F) -> 
;;                  NatToPos n=SOne(NatToPos(NatHalf n)))")
;; (assume "n" "1<n" "NotEn")
;; (ng #t)
;; (assert "n<=Succ Zero -> F")
;; (assume "n<=1")
;; (use "Not1<n")
;; (assert "n<=Succ Zero -> F")
;; (assume "n<=1")
;; (assert "Succ Zero<Succ Zero")
;; (use "NatLtLeTrans" (pt "n"))
;; (use "1<n")
;; (use "n<=1")
;; (assume "Absurd" "Not1<n")
;; (use "Absurd")
;; (search)
;; (assume "NotLen1")
;; (simp "NotLen1")
;; (ng #t)
;; (simp "NotEn")
;; (ng #t)
;; (assert "NatHalf n<n")
;; (use "NatHalfLt")
;; (use "NatLtTrans" (pt "Succ Zero"))
;; (use "Truth")
;; (use "1<n")
;; (assume "NatHalf n<n")
;; (simp "NatHalf n<n")
;; (ng #t)
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "NatToPosEqSOneNatToPosHalf")

;; NatHalfSuccEven
(set-goal "all n(NatEven n -> NatHalf(Succ n)=NatHalf n)")
(use "CVIndPvar")
(assume "Absurd")
(strip)
(use "EfAtom")
(use "Absurd")
(assume "n" "Prog" "En")
(cases (pt "n"))
(ng #t)
(strip)
(use "Truth")
(assume "n1" "n=Sn1")
(cases (pt "n1"))
(ng #t)
(assume "n1=0")
(simphyp-with-to "n=Sn1" "n1=0" "n=1")
(simphyp-with-to "En" "n=1" "Absurd")
(use "Absurd")
(assume "n2" "n1=Sn2")
(ng #t)
(use "Prog")
(simp "n=Sn1")
(simp "n1=Sn2")
(use "NatLtTrans" (pt "Succ n2"))
(use "Truth")
(use "Truth")
(simphyp-with-to "En" "n=Sn1" "EnSimp")
(simphyp-with-to "EnSimp" "n1=Sn2" "EnSimpSimp")
(use "EnSimpSimp")
;; Proof finished.
;; (cdp)
(save "NatHalfSuccEven")

;; PosToNatToPosId
(set-goal "all n(Zero<n -> PosToNat(NatToPos n)=n)")
(use "CVIndPvar")
(assume "Absurd" "n^" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n" "Prog" "0<n")
(use "NatLeLtCases" (pt "n") (pt "Succ Zero"))
;; 7,8
(assume "n<=1")
(simp "n<=1")
(ng #t)
(use "NatLeAntiSym")
(use "NatLtToSuccLe")
(use "0<n")
(use "n<=1")
;; 8
(assume "1<n")
(cases (pt "NatEven n"))
;; 16,17
(assume "En")
(assert "NatToPos n=SZero(NatToPos(NatHalf n))")
 (use "NatToPosEqSZeroNatToPosHalf")
 (use "1<n")
 (use "En")
(assume "NatToPos n=SZero(NatToPos(NatHalf n))")
(simp "NatToPos n=SZero(NatToPos(NatHalf n))")
(simp "PosToNat1CompRule")
(simp "Prog")
(use "NatDoubleHalfEven")
(use "En")
(use "NatLtZeroHalfEven")
(use "0<n")
(use "En")
(use "NatHalfLt")
(use "0<n")
;; 17
(assume "NotEn")
(assert "NatToPos n=SOne(NatToPos(NatHalf n))")
 (use "NatToPosEqSOneNatToPosHalf")
 (use "1<n")
 (use "NotEn")
(assume "NatToPos n=SOne(NatToPos(NatHalf n))")
(simp "NatToPos n=SOne(NatToPos(NatHalf n))")
(simp "PosToNat2CompRule")
(cases (pt "n"))
(assume "n=0")
(use "EfAtom")
(simphyp-with-to "NotEn" "n=0" "Absurd")
(use "Absurd")
(use "Truth")
(assume "n1" "n=Succ n1")
(simp "PosToNat1CompRule")
(assert "NatEven n1")
(use "NatOddSuccToEven")
(simp "<-" "n=Succ n1")
(use "NotEn")
(assume "En1")
(simp "NatHalfSuccEven")
(assert "PosToNat(SZero(NatToPos(NatHalf n1)))=n1")
 (simp "PosToNat1CompRule")
 (simp "Prog")
 (use "NatDoubleHalfEven")
 (use "En1")
 (simphyp-with-to "1<n" "n=Succ n1" "0<n1")

 (use "NatLtZeroHalfEven")
 (use "0<n1")
 (use "En1")
 ;; ?^61:NatHalf n1<n
 (simp "n=Succ n1")
 (use "NatHalfLtSucc")
 ;; Assertion proved.
 (assume "PosToNat(SZero(NatToPos(NatHalf n1)))=n1")
(simp "Prog")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "En1")
(use "NatLtZeroHalfEven")
;; ?^75:Zero<n1
(assert "Succ Zero<Succ n1")
(simp "<-" "n=Succ n1")
(use "1<n")
;; Assertion proved.
(assume "S0<Sn1")
(use "S0<Sn1")
;; 76
(use "En1")
(simp "n=Succ n1")
(use "NatHalfLtSucc")
(use "En1")
;; Proof finished.
;; (cdp)
(save "PosToNatToPosId")

;; PosEqTrans
(set-goal "all p,q,r(p=q -> q=r -> p=r)")
(assume "p" "q" "r" "=Hyp")
(simp "<-" "=Hyp")
(assume "p=r")
(use "p=r")
;; Proof finished.
;; (cdp)
(save "PosEqTrans")

;; NatToPosToNatId
(set-goal "all p NatToPos(PosToNat p)=p")
(ind) 
;; 2-4
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH")
(simp "NatToPos0CompRule")
(assert "NatDouble(PosToNat p)<=Succ Zero -> F")
(use "NatLeDoubleOne")
(use "NatLtZeroPos")
;; Assertion proved.
(assume "Assertion")
(simp "Assertion")
(ng #t)
(simp "NatEvenDouble")
(ng #t)
(simp "NatHalfDouble")
(use "PosEqTrans" (pt "NatToPos(PosToNat p)"))
(simp "NatLtDouble")
;; ?^19:(GRecGuard nat pos)([n]n)(PosToNat p)
;;      ([n,(nat=>pos)]
;;        [if (n<=Succ Zero)
;;          1
;;          [if (NatEven n)
;;           (SZero((nat=>pos)(NatHalf n)))
;;           (SOne((nat=>pos)(NatHalf n)))]])
;;      True=
;;      NatToPos(PosToNat p)
(use "Truth")
(use "NatLtZeroPos")
(use "IH")
;; 4
(assume "p" "IH")
(simp "NatToPos0CompRule")
(ng #t)
(assert "NatDouble(PosToNat p)=Zero -> F")
(assume "EqH")
(assert "Zero<NatDouble(PosToNat p)")
(use "NatLt0Double")
(use "NatLtZeroPos")
(simp "EqH")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "Assertion")
(simp "Assertion")
(ng #t)
(simp "NatEvenSucc")
(ng #t)
(simp "NatHalfSuccDouble")
(assert "p<Succ(NatDouble(PosToNat p))")
(use "NatLeToLtSucc")
(use "NatLeDouble")
;; Asserton proved.
(assume "LtSucc")
(simp "LtSucc")
(use "PosEqTrans" (pt "NatToPos(PosToNat p)"))
;; ?^44:(GRecGuard nat pos)([n]n)(PosToNat p)
;;      ([n,(nat=>pos)]
;;        [if (n<=Succ Zero)
;;          1
;;          [if (NatEven n)
;;           (SZero((nat=>pos)(NatHalf n)))
;;           (SOne((nat=>pos)(NatHalf n)))]])
;;      True=
;;      NatToPos(PosToNat p)
(use "Truth")
(use "IH")
;; ?^36:NatEven(NatDouble(PosToNat p))
(use "NatEvenDouble")
;; Proof finished.
;; (cdp)
(save "NatToPosToNatId")

;; PosToNatInj
(set-goal "all p,q(PosToNat p=PosToNat q -> p=q)")
(assume "p" "q" "EqHyp")
(assert "NatToPos(PosToNat p)=NatToPos(PosToNat q)")
 (simp "EqHyp")
 (use "Truth")
 (simp "NatToPosToNatId")
 (simp "NatToPosToNatId")
(assume "p=q")
(use "p=q")
;; Proof finished.
;; (cdp)
(save "PosToNatInj")

;; NatLtSuccZeroEven
(set-goal "all n(Zero<n -> NatEven n -> Succ Zero<n)")
(cases)
;; 2,3
(assume "Absurd" "Useless")
(use "Absurd")
;; 3
(cases)
;; 5,6
(assume "Useless" "Absurd")
(use "Absurd")
;; 6
(assume "n" "Useless1" "Useless2")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLtSuccZeroEven")

;; NatLtSuccZeroOdd
(set-goal "all n((NatEven n -> F) -> (n=Succ Zero -> F) -> Succ Zero<n)")
(cases)
;; 2,3
(assume "Absurd" "Useless")
(use "Absurd")
(use "Truth")
;; 3
(cases)
;; 6,7
(assume "Useless" "Absurd")
(use "Absurd")
(use "Truth")
;; 7
(assume "n" "Useless1" "Useless2")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLtSuccZeroOdd")

;; SuccPosS
(set-goal "all n(Zero<n -> NatToPos(Succ n)=PosS(NatToPos n))")
(assert "all n(Zero<n -> Succ n=PosToNat(PosS(NatToPos n)))")
(use "CVIndPvar")
(assume "Absurd")
(strip)
(use "EfAtom")
(use "Absurd")
(assume "n" "Prog" "0<n")
(cases (pt "NatEven n"))
;;10,11
(assume "En")
(simp "NatToPosEqSZeroNatToPosHalf")
(simp "PosS1CompRule")
(simp "PosToNat2CompRule")
(simp "PosToNat1CompRule")
(simp "PosToNatToPosId")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "En")
(use "NatLtZeroHalfEven")
(use "0<n")
(use "En")
(use "En")
(use "NatLtSuccZeroEven")
(use "0<n")
(use "En")
;; 11
(assume "On")
(cases (pt "n=Succ Zero"))
;; 28,29
(assume "n=1")
(simp "n=1")
;; simp normalizes the goal, which we do not want.  Why?  Ok if order
;; in simp-with-intern is changed: consider normalized items last.
(ng #t)
(use "Truth")
;; 29
(assume "n=/=1")
(simp "NatToPosEqSOneNatToPosHalf")
(simp "PosS2CompRule")
(simp "PosToNat1CompRule")
(simp "<-" "Prog")
(simp "NatDouble1CompRule")
(ng #t)
(simp "NatDoubleHalfOdd")
(use "Truth")
(use "On")
(use "NatLtZeroHalfFinally")
(use "0<n")
(use "n=/=1")
(use "NatHalfLt")
(use "0<n")
(use "On")
;; ?^35:Succ Zero<n
(use "NatLtSuccZeroOdd")
(use "On")
(use "n=/=1")
;; Assertion proved
(assume "SuccPosSAux" "n" "0<n")
(simp "SuccPosSAux")
(simp "NatToPosToNatId")
(use "Truth")
(use "0<n")
;; Proof finished.
;; (cdp)
(save "SuccPosS")

;; PosSSucc
(set-goal "all p PosToNat(PosS p)=Succ(PosToNat p)")
(assume "p")
(assert "PosToNat(PosS p)=PosToNat(PosS(NatToPos(PosToNat p)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "SuccPosS")
(simp "PosToNatToPosId")
(use "Truth")
(use "Truth")
(use "NatLtZeroPos")
;; Proof finished.
;; (cdp)
(save "PosSSucc")

;; We prove that PosToNat is an isomorphism w.r.t. +

;; PosToNatPlus
(set-goal "all p,q PosToNat(p+q)=PosToNat p+PosToNat q")
(ind) 
;; 2-4
(assume "q")
(ng #t)
(use "PosSSucc")
;; 3
(assume "p" "IH")
(cases) ;8-10
(ng #t)
(use "Truth")
;; 9
(assume "q")
(ng #t)
(simp "NatPlusDouble")
(simp "IH")
(use "Truth")
;; 10
(assume "q")
(ng #t)
(simp "NatPlusDouble")
(simp "IH")
(use "Truth")
;; 4
(assume "p" "IH")
(cases) ;21-23
(ng #t)
(simp "PosSSucc")
(ng #t)
(use "Truth")
;; 22
(assume "q")
(ng #t)
(simp "NatPlusDouble")
(simp "IH")
(use "Truth")
;; 23
(assume "q")
(ng #t)
(simp "PosSSucc")
(ng #t)
(simp "NatPlusDouble")
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosToNatPlus")

;; NatToPosPlus
(set-goal "all n,m(Zero<n -> Zero<m -> NatToPos(n+m)=NatToPos n+NatToPos m)")
(assume "n" "m" "0<n" "0<m")
(assert "n+m=PosToNat(NatToPos n)+PosToNat(NatToPos m)")
 (simp "PosToNatToPosId")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "0<m")
 (use "0<n")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "PosToNatPlus")
(simp "NatToPosToNatId")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatToPosPlus")

;; Commutativity of + for pos
;; PosPlusComm
(set-goal "all p,q p+q=q+p")
(assume "p" "q")
(assert "p+q=NatToPos(PosToNat(p+q))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "q+p=NatToPos(PosToNat(q+p))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(p+q)=PosToNat p+PosToNat q")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(simp "NatPlusComm")
(assert "PosToNat(q+p)=PosToNat q+PosToNat p")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosPlusComm")

;; Associativity of + for pos
(set-goal "all p,q,r p+(q+r)=p+q+r")
(assume "p" "q" "r")
(assert "p+(q+r)=NatToPos(PosToNat(p+(q+r)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "PosToNat(p+(q+r))=PosToNat(p)+PosToNat(q+r)")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(q+r)=PosToNat q+PosToNat r")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(assert "PosToNat p+(NatPlus(PosToNat q)(PosToNat r))=
         NatPlus(PosToNat p+PosToNat q)(PosToNat r)")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(simp "<-" "PosToNatPlus")
(simp "<-" "PosToNatPlus")
(use "NatToPosToNatId")
;; Proof finished.
;; (cdp)
(save "PosPlusAssoc")
(add-rewrite-rule "p+(q+r)" "p+q+r")

;; To prove PosPlusCancelL we again transfer the problem to nat via
;; PosToNatInj and PosToNatPlus.

;; PosPlusCancelL
(set-goal "all p,q,r(p+q=p+r -> q=r)")
(assume "p" "q" "r" "EqHyp")
(use "PosToNatInj")
(use "NatPlusCancelL" (pt "PosToNat p"))
(simp "<-" "PosToNatPlus")
(simp "<-" "PosToNatPlus")
(simp "EqHyp")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosPlusCancelL")

;; PosPlusCancelR
(set-goal "all p,q,r(p+q=r+q -> p=r)")
(assume "p" "q" "r" "EqHyp")
(use "PosToNatInj")
(use "NatPlusCancelR" (pt "PosToNat q"))
(simp "<-" "PosToNatPlus")
(simp "<-" "PosToNatPlus")
(simp "EqHyp")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosPlusCancelR")

;; We postpone the treatment (as rewrite rules) of PosLePlusCancelL
;; PosLePlusCancelR PosLtPlusCancelL PosLtPlusCancelR
;; PosLeTimesCancelL PosLeTimesCancelR PosLtTimesCancelL
;; PosLtTimesCancelR until after PosLe and PosLt.

;; The following (former) rules are not used any more, because they
;; increase the number of +'s.

;; (add-rewrite-rule "p+SZero q" "p+q+q")
;; (add-rewrite-rule "p+SOne q" "p+q+q+1")
;; (add-rewrite-rule "SZero p+q" "p+p+q") ;no term. for 2+m
;; (add-rewrite-rule "SOne p+q" "p+p+1+q"

;; (display-pconst "PosPlus")

;; The rules for PosMinus will give correct results for p--q (only) if
;; q<p.  To be able to formulate appropriate assumptions we postpone
;; the treatment of PosMinus until after PosLe and PosLt.

;; Rules for PosTimes:

(add-computation-rules
 "p*One" "p"
 "p*SZero q" "SZero(p*q)"
 "p*SOne q" "SZero(p*q)+p")

;; PosTimesTotal
(set-totality-goal "PosTimes")
(assume "p^" "Tp" "q^" "Tq")
(elim "Tq")

(ng #t)
(use "Tp")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "IHq1")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "PosPlusTotal")
(use "TotalPosSZero")
(use "IHq1")
(use "Tp")
;; Proof finished.
;; (cdp)
(save-totality)

;; PosTimesEqP
(set-goal "allnc p^1,q^1(EqPPos p^1 q^1 -> allnc p^2,q^2(EqPPos p^2 q^2 ->
 EqPPos(p^1*p^2)(q^1*q^2)))")
(assume "p^1" "q^1" "EqPp1q1" "p^2" "q^2" "EqPp2q2")
(simp "<-" (pf "p^1 eqd q^1"))
(simp "<-" (pf "p^2 eqd q^2"))
(use "EqPPosRefl")
(use "PosTimesTotal")
(use "EqPPosToTotalLeft" (pt "q^1"))
(use "EqPp1q1")
(use "EqPPosToTotalLeft" (pt "q^2"))
(use "EqPp2q2")
;; 6
(use "EqPPosToEqD")
(use "EqPp2q2")
;; 4
(use "EqPPosToEqD")
(use "EqPp1q1")
;; Proof finished.
;; (cdp)
(save "PosTimesEqP")

(set-goal "all p One*p=p")
(ind)
(auto)
;; Proof finished.
;; (cdp)
(add-rewrite-rule "One*p" "p")

(set-goal "all p,q SZero p*q=SZero(p*q)")
(assume "p")
(ind)
(auto)
(assume "q" "IHone")
(ng)
(simp "IHone")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "SZero p*q" "SZero(p*q)")

;; We prove that NatToPos is an isomorphism w.r.t. *

;; PosToNatTimes
(set-goal "all p,q PosToNat(p*q)=PosToNat p*PosToNat q")
(assume "p")
(ind) ;3-5
(ng #t)
(use "Truth")
;; 4
(assume "q" "IH")
(ng #t)
(simp "IH")
(simp "NatDoubleTimes2")
(use "Truth")
;; 5
(assume "q" "IH")
(ng #t)
(simp "PosToNatPlus")
(ng #t)
(simp "IH")
(simp "NatDoubleTimes2")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosToNatTimes")

;; NatToPosTimes
(set-goal "all n,m(Zero<n -> Zero<m -> NatToPos(n*m)=NatToPos n*NatToPos m)")
(assume "n" "m" "0<n" "0<m")
(assert "n*m=PosToNat(NatToPos n)*PosToNat(NatToPos m)")
 (simp "PosToNatToPosId")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "0<m")
 (use "0<n")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "PosToNatTimes")
(simp "NatToPosToNatId")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatToPosTimes")

;; PosTimesPlusDistr
(set-goal "all p,q,r p*(q+r)=p*q+p*r")
(assume "p" "q" "r")
(assert "p*(q+r)=NatToPos(PosToNat(p*(q+r)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "p*q+p*r=NatToPos(PosToNat(p*q+p*r))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(simp "PosToNatTimes")
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(simp "NatTimesPlusDistr")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosTimesPlusDistr")
(add-rewrite-rule "p*(q+r)" "p*q+p*r")

;; Commutativity of * for pos
;; PosTimesComm
(set-goal "all p,q p*q=q*p")
(assume "p" "q")
(assert "p*q=NatToPos(PosToNat(p*q))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "q*p=NatToPos(PosToNat(q*p))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(p*q)=PosToNat p*PosToNat q")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(simp "NatTimesComm")
(assert "PosToNat(q*p)=PosToNat q*PosToNat p")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosTimesComm")

;; PosTimesPlusDistrLeft
(set-goal "all p,q,r (p+q)*r=(p*r)+(q*r)")
(assume "p" "q" "r")
(simp-with "PosTimesComm" (pt "p+q") (pt "r"))
(ng)
(simp-with "PosTimesComm" (pt "p") (pt "r"))
(simp-with "PosTimesComm" (pt "q") (pt "r"))
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosTimesPlusDistrLeft")
(add-rewrite-rule "(p+q)*r" "p*r+q*r")

;; Associativity of * for pos
(set-goal "all p,q,r p*(q*r)=p*q*r")
(assume "p" "q" "r")
(assert "p*(q*r)=NatToPos(PosToNat(p*(q*r)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "PosToNat(p*(q*r))=PosToNat(p)*PosToNat(q*r)")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(q*r)=PosToNat q*PosToNat r")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(assert "PosToNat p*(NatTimes(PosToNat q)(PosToNat r))=
         NatTimes(PosToNat p*PosToNat q)(PosToNat r)")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(simp "<-" "PosToNatTimes")
(simp "<-" "PosToNatTimes")
(use "NatToPosToNatId")
;; Proof finished.
;; (cdp)
(save "PosTimesAssoc")
(add-rewrite-rule "p*(q*r)" "p*q*r")

(set-goal "all p,q SOne p*q=SZero(p*q)+q")
(assume "p")
(ind)
(ng #t)
(use "Truth")
;; 4
(assume "q" "IH")
(ng #t)
(use "IH")
;; 5
(assume "q" "IH")
(ng #t)
(simp "IH")
(assert "SZero(p*q)+q+p=SZero(p*q)+(q+p)")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "SZero(p*q)+p+q=SZero(p*q)+(p+q)")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "p+q=q+p")
 (use "PosPlusComm")
(assume "p+q=q+p")
(simp "p+q=q+p")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosTimesSOne")
(add-rewrite-rule "SOne p*q" "SZero(p*q)+q")

;; Rules for PosExp : pos=>nat=>pos

(add-computation-rules
 "p**Zero" "One"
 "p**Succ m" "p**m*p")

;; PosExpTotal
(set-totality-goal "PosExp")
(assume "p^" "Tp" "n^" "Tn")
(elim "Tn")

(ng #t)
(use "TotalPosOne")

(assume "n^1" "Tn1" "IHn1")
(ng #t)
(use "PosTimesTotal")
(use "IHn1")
(use "Tp")
;; Proof finished.
;; (cdp)
(save-totality)

;; PosExpOne
(set-goal "all n 1**n=1")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosExpOne")
(add-rewrite-rules "1**n" "1")

;; Rules for PosLt, PosLe

(add-computation-rules
 "p<One" "False"
 "One<SZero p" "True"
 "One<SOne p" "True"
 "SZero p<SZero q" "p<q"
 "SZero p<SOne q" "p<=q"
 "SOne p<SZero q" "p<q"
 "SOne p<SOne q" "p<q")

(add-computation-rules
 "One<=p" "True"
 "SZero p<=One" "False"
 "SOne p<=One" "False"
 "SZero p<=SZero q" "p<=q"
 "SZero p<=SOne q" "p<=q"
 "SOne p<=SZero q" "p<q"
 "SOne p<=SOne q" "p<=q")

;; PosLtPosLeTotalLemma
(set-goal "allnc p^(TotalPos p^ -> allnc q^(TotalPos q^ ->
 TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)))")
(assume "p^" "Tp")
(elim "Tp")

(assume "q^" "Tq")
(split)
(elim "Tq")
(use "TotalBooleFalse")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalBooleTrue")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalBooleTrue")

(ng #t)
(use "TotalBooleTrue")
;; ?_4:allnc p^(
;;      TotalPos p^ -> 
;;      allnc q^(TotalPos q^ -> TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)) -> 
;;      allnc q^(
;;      TotalPos q^ -> TotalBoole(SZero p^ <q^) andd TotalBoole(SZero p^ <=q^)))
(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")

(split)
(ng #t)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleFalse")

(assume "q^1" "Tq1" "Useless")
(inst-with-to "IHp1" (pt "q^1") "Tq1" "AndHyp")
(drop "IHp1")
(split)
(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")

(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(inst-with-to "IHp1" (pt "q^1") "Tq1" "AndHyp")
(drop "IHp1")
(split)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")
;; ?_5:allnc p^(
;;      TotalPos p^ -> 
;;      allnc q^(TotalPos q^ -> TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)) -> 
;;      allnc q^(
;;       TotalPos q^ -> TotalBoole(SOne p^ <q^) andd TotalBoole(SOne p^ <=q^)))
(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")

(split)
(ng #t)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleFalse")

(assume "q^1" "Tq1" "Useless")
(inst-with-to "IHp1" (pt "q^1") "Tq1" "AndHyp")
(drop "IHp1")
(split)
(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")

(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "IHp1")
(use "Tq1")
;; Proof finished.
;; (cdp)
(save "PosLtPosLeTotalLemma")

;; PosLtTotal
(set-totality-goal "PosLt")
(assume "p^" "Tp" "q^" "Tq")
(assert "TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)")
(use "PosLtPosLeTotalLemma")
(use "Tp")
(use "Tq")
(assume "AndHyp")
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")
;; Proof finished.
;; (cdp)
(save-totality)

;; PosLeTotal
(set-totality-goal "PosLe")
(assume "p^" "Tp" "q^" "Tq")
(assert "TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)")
(use "PosLtPosLeTotalLemma")
(use "Tp")
(use "Tq")
(assume "AndHyp")
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")
;; Proof finished.
;; (cdp)
(save "PosLeTotal")

;; PosLtToLe
(set-goal "all p,q(p<q -> p<=q)")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "p" "IH")
(cases)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "q")
(ng #t)
(use "IH")
(assume "q")
(ng #t)
(assume "p<=p")
(use "p<=p")
;; 4
(assume "p" "IH")
(cases)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "q")
(ng #t)
(assume "p<p")
(use "p<p")
(assume "q")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosLtToLe")

;; PosLTrans
(set-goal "all p,q,r((p<q -> q<=r -> p<r)
                     andnc (p<=q -> q<r -> p<r)
                     andnc (p<=q -> q<=r -> p<=r))")
(ind) ;2-4
(cases) ;5-7
(assume "r")
(ng #t)
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(split)
(assume "Useless" "1<r")
(use "1<r")
(strip)
(use "Truth")
;; 6
(assume "q")
(ng #t)
(cases)
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(strip)
(use "Truth")
(assume "r")
(ng #t)
(split)
(strip)
(use "Truth")
(split)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r")
(split)
(ng #t)
(strip)
(use "Truth")
(split)
(ng #t)
(strip)
(use "Truth")
(strip)
(use "Truth")
;; 7
(assume "q")
(cases)
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(strip)
(use "Truth")
(assume "r")
(ng #t)
(split)
(strip)
(use "Truth")
(split)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r")
(ng #t)
(split)
(strip)
(use "Truth")
(split)
(strip)
(use "Truth")
(strip)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases) ;79-81
(assume "q")
(ng #t)
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 80
(assume "q")
(cases) ;97-99
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 98
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(use "IH1")
;; 99
(assume "r")
(ng #t)
(split)
(assume "p1<p2" "p2<=p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "p2<=p3")
(split)
(use "IH1")
(use "IH1")
;; 83
(assume "q")
(cases) ;123-25
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 124
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(assume "p1<=p2" "p2<p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'right 'left "p1<=p2" "p2<p3")
;; 125
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(assume "p1<=p2" "p2<p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'right 'left "p1<=p2" "p2<p3")
(use "IH1")
;; 4
(assume "p" "IH1")
(cases) ;151-153
(assume "q")
(ng #t)
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 152
(assume "q")
(cases) ;167-169
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 168
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(assume "p1<p2" "p2<p3")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "?")
(use "PosLtToLe")
(use "p2<p3")
(use "IH1")
;; 169
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(assume "p1<p2" "p2<=p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "p2<=p3")
;; 153
(assume "q")
(cases) ;196-98
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 197
(assume "r")
(ng #t)
(split)
(assume "p1<p2" "p2<p3")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "?")
(use "PosLtToLe")
(use "p2<p3")
(split)
(use "IH1")
(use "IH1")
;; 198
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(use "IH1")
;; Proof finished.
;; (cdp)
(save "PosLTrans")

;; Using this and PosLtToLe we can easily derive PosLeLtTrans
;; PosLtLeTrans PosLeTrans PosLtTrans.

;; PosLtLeTrans
(set-goal "all p,q,r(p<q -> q<=r -> p<r)")
(assume "p" "q" "r")
(use "PosLTrans")
;; Proof finished.
;; (cdp)
(save "PosLtLeTrans")

;; PosLeLtTrans
(set-goal "all p,q,r(p<=q -> q<r -> p<r)")
(assume "p" "q" "r")
(use "PosLTrans")
;; Proof finished.
;; (cdp)
(save "PosLeLtTrans")

;; PosLeTrans
(set-goal "all p,q,r(p<=q -> q<=r -> p<=r)")
(assume "p" "q" "r")
(use "PosLTrans")
;; Proof finished.
;; (cdp)
(save "PosLeTrans")

;; PosLtTrans
(set-goal "all p,q,r(p<q -> q<r -> p<r)")
(assume "p" "q" "r" "p1<p2")
(use "PosLeLtTrans")
(use "PosLtToLe")
(use "p1<p2")
;; Proof finished.
;; (cdp)
(save "PosLtTrans")

;; We add some useful rewrite rules.

;; PosLeToEq
(set-goal "all p (p<=1)=(p=1)")
(cases)
(use "Truth")
(assume "p")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosLeToEq")
(add-rewrite-rule "p<=1" "p=1")

(set-goal "all p (p<p)=False")
(ind)
(use "Truth")
(assume "p" "IH")
(use "IH")
(assume "p" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<p" "False")

(set-goal "all p p<=p")
(ind)
(use "Truth")
(assume "p" "IH")
(use "IH")
(assume "p" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<=p" "True")

(set-goal "all p p<PosS p")
(ind)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; 4
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<PosS p" "True")

(set-goal "all p p<=PosS p")
(cases)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; 4
(assume "p")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<=PosS p" "True")

(set-goal "all p (PosS p<=p)=False")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosS p<=p" "False")

(set-goal "all p (PosS p<p)=False")
(cases)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosS p<p" "False")

(set-goal "all p,q p<=p+q")
(ind)
(cases)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "IH1")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "PosLeLtTrans" (pt "p+q"))
(use "IH1")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<=p+q" "True")

(set-goal "all p,q p<p+q")
(ind)
(cases)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "Truth")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "PosLtTrans" (pt "p+q"))
(use "IH1")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<p+q" "True")

(set-goal "all p,q p<=q+p")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<=q+p" "True")

(set-goal "all p,q p<q+p")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<q+p" "True")

(set-goal "all p (PosS p<=1)=False")
(cases)
(use "Truth")
(strip)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosS p<=1" "False")

(set-goal "all p,q (p+q<=p)=False")
(assert "all p,q(p+q<=p -> F)")
 (ind) ;4-6
 (ng)
 (cases)
 (assume "Absurd")
 (use "Absurd")
 (assume "p" "Absurd")
 (use "Absurd")
 (assume "p" "Absurd")
 (use "Absurd")
;; 5
 (assume "p" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "q" "IH2")
 (ng #t)
 (use "IH1")
 (assume "q" "IH2")
 (ng #t)
 (assume "p+q<p")
 (use "IH1" (pt "q"))
 (use "PosLtToLe")
 (use "p+q<p")
;; 6
 (assume "p" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "q" "IH2")
 (ng #t)
 (use "IH1")
 (assume "q" "IH2")
 (ng #t)
 (assume "S(p+q)<=p")
 (use "IH1" (pt "q"))
 (use "PosLeTrans" (pt "PosS(p+q)"))
 (use "Truth")
 (use "S(p+q)<=p")
;; Assertion proved.
(assume "Assertion" "p" "q")
(use "AtomFalse")
(use "Assertion")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p+q<=p" "False")

(set-goal "all p,q (p+q<=q)=False")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p+q<=q" "False")

(set-goal "all p,q (p+q<p)=False")
(assert "all p,q(p+q<p -> F)")
 (ind) ;4-6
 (ng #t)
 (assume "p" "Absurd")
 (use "Absurd")
;; 5
 (assume "p" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "q" "IH2")
 (ng #t)
 (use "IH1")
 (assume "q" "IH2")
 (ng #t)
 (assume "p+q<p")
 (use "IH1" (pt "q"))
 (use "p+q<p")
;; 6
 (assume "p" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "q" "IH2")
 (ng #t)
 (use "IH1")
 (assume "q" "IH2")
 (ng #t)
 (assume "S(p+q)<=p")
 (use "IH1" (pt "q"))
 (use "PosLtLeTrans" (pt "PosS(p+q)"))
 (use "Truth")
 (use "S(p+q)<=p")
;; Assertion proved.
(assume "Assertion" "p" "q")
(use "AtomFalse")
(use "Assertion")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p+q<p" "False")

(set-goal "all p,q (p+q<q)=False")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p+q<q" "False")

(set-goal "all p One<PosS p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "One<PosS p" "True")

;; PosLtPosS
(set-goal "all p,q (p<PosS q)=(p<=q)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
;; Proof finished
;; (cdp)
(save "PosLtPosS")

;; PosLePosS
(set-goal "all p,q (PosS p<=q)=(p<q)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "IH1")
;; Proof finished.
;; (cdp)
(save "PosLePosS")

(set-goal "all p,q (PosS p<PosS q)=(p<q)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "PosLtPosS")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "PosLePosS")
(assume "q")
(ng #t)
(use "IH1")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosS p<PosS q" "p<q")

(set-goal "all p,q (PosS p<=PosS q)=(p<=q)")
(ind)
(ng)
(cases)
(use "Truth")
(assume "q")
(use "Truth")
(assume "q")
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng)
(use "Truth")
(assume "q")
(use "Truth")
(assume "q")
(use "PosLtPosS")
;; 4
(assume "p" "IH1")
(cases)
(ng)
(cases (pt "p"))
(strip)
(use "Truth")
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "q")
(ng #t)
(use "PosLePosS")
(assume "q")
(ng #t)
(use "IH1")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosS p<=PosS q" "p<=q")

;; PosSPosPredId
(set-goal "all p(One<p -> PosS(PosPred p)=p)")
(cases)
;; 2-4
(assume "Absurd")
(use "Absurd")
;; 3
(assume "p" "Useless")
(ng)
(use "Truth")
;; 4
(assume "p" "Useless")
(ng)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosSPosPredId")

;; PosLtMonPred
(set-goal "all p,q(One<p -> p<q -> PosPred p<PosPred q)")
(assume "p" "q" "1<p" "p<q")
(assert "One<q")
 (use "PosLtTrans" (pt "p"))
 (use "1<p")
 (use "p<q")
(assume "1<q")
(simp "<-" "PosLt8RewRule")
(simp "PosSPosPredId")
(simp "PosSPosPredId")
(use "p<q")
(use "1<q")
(use "1<p")
;; Proof finished.
;; (cdp)
(save "PosLtMonPred")

;; PosNotLeToLt and PosNotLtToLe are proved using the isomorphic
;; embedding PosToNat of pos into nat.

;; We prove that NatToPos is an isomorphism w.r.t. <= and <.  Main
;; idea: Translate the computation rules for PosLe, PosLt into
;; equational lemmas for NatLe, NatLt with NatDouble nat for SZero pos
;; and Succ(NatDouble nat) for SOne pos.

;; PosToNatLeLt
(set-goal "all p,q((PosToNat p<=PosToNat q)=(p<=q) andnc
                   (PosToNat p<PosToNat q)=(p<q))")
(ind) ;2-4
(cases) ;5-7
(ng #t)
(split)
(use "Truth")
(use "Truth")
;; 6
(assume "p")
(ng #t)
(split)
(assert "Succ Zero<=NatDouble(PosToNat p)")
 (use "NatLtToLe")
 (use "NatLtOneDouble")
 (use "NatLtZeroPos")
(assume "Succ Zero<=NatDouble(PosToNat p)")
(simp "Succ Zero<=NatDouble(PosToNat p)")
(use "Truth")
(assert "Succ Zero<NatDouble(PosToNat p)")
 (use "NatLtOneDouble")
 (use "NatLtZeroPos")
(assume "Succ Zero<NatDouble(PosToNat p)")
(simp "Succ Zero<NatDouble(PosToNat p)")
(use "Truth")
;; 7
(assume "p")
(ng #t)
(split)
(use "Truth")
(assert "Zero<NatDouble(PosToNat p)")
 (use "NatLtOneSuccDouble")
 (use "NatLtZeroPos")
(assume "Zero<NatDouble(PosToNat p)")
(simp "Zero<NatDouble(PosToNat p)")
(use "Truth")
;; 3
(assume "p" "IH1")
(cases) ;36-38
(ng #t)
(split)
(assert "NatDouble(PosToNat p)<=Succ Zero -> F")
 (use "NatLeDoubleOne")
 (use "NatLtZeroPos")
(assume "NatDouble(PosToNat p)<=Succ Zero -> F")
(simp "NatDouble(PosToNat p)<=Succ Zero -> F")
(use "Truth")
(assert "NatDouble(PosToNat p)<Succ Zero -> F")
 (use "NatLtDoubleOne")
 (use "NatLtZeroPos")
(assume "NatDouble(PosToNat p)<Succ Zero -> F")
(simp "NatDouble(PosToNat p)<Succ Zero -> F")
(use "Truth")
;; 37
(assume "q")
(ng #t)
(split)
(simp "NatDoubleLe")
(use "IH1")
(simp "NatDoubleLt")
(use "IH1")
;; 38
(assume "q")
(ng #t)
(split)
(simp "NatLeDoubleSuccDouble")
(use "IH1")
(simp "NatLtDoubleSuccDouble")
(use "IH1")
;; 4
(assume "p" "IH1")
(cases) ;65-67
(ng #t)
(split)
(assert "NatDouble(PosToNat p)=Zero -> F")
 (assume "NatDouble(PosToNat p)=Zero")
 (assert "Zero<PosToNat p")
  (use "NatLtZeroPos")
 (assume "0<p")
 (inst-with-to "NatLt0Double" (pt "PosToNat p") "0<p" "NatLt0DoubleInst")
 (simphyp-with-to "NatLt0DoubleInst" "NatDouble(PosToNat p)=Zero" "Absurd")
 (use "Absurd")
(assume "NatDouble(PosToNat p)=Zero -> F")
(simp "NatDouble(PosToNat p)=Zero -> F")
(use "Truth")
(use "Truth")
;; 66
(assume "q")
(ng #t)
(split)
(simp "NatLeSuccDoubleDouble")
(use "IH1")
(simp "NatLtSuccDoubleDouble")
(use "IH1")
;; 67
(assume "q")
(ng #t)
(split)
(simp "NatLeSuccDoubleSuccDouble")
(use "IH1")
(simp "NatLtSuccDoubleSuccDouble")
(use "IH1")
;; Proof finished.
;; (cdp)
(save "PosToNatLeLt")

;; Easy consequences

;; PosToNatLe
(set-goal "all p,q (PosToNat p<=PosToNat q)=(p<=q)")
(assume "p" "q")
(use "PosToNatLeLt")
;; Proof finished.
(save "PosToNatLe")

;; NatToPosLe
(set-goal "all n,m(Zero<n -> Zero<m -> (NatToPos n<=NatToPos m)=(n<=m))")
(assume "n" "m" "0<n" "0<m")
(simp "<-" "PosToNatLe")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "Truth")
(use "0<m")
(use "0<n")
;; Proof finished.
;; (cdp)
(save "NatToPosLe")

;; PosToNatLt
(set-goal "all p,q (PosToNat p<PosToNat q)=(p<q)")
(assume "p" "q")
(use "PosToNatLeLt")
;; Proof finished.
;; (cdp)
(save "PosToNatLt")

;; NatToPosLt
(set-goal "all n,m(Zero<n -> Zero<m -> (NatToPos n<NatToPos m)=(n<m))")
(assume "n" "m" "0<n" "0<m")
(simp "<-" "PosToNatLt")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "Truth")
(use "0<m")
(use "0<n")
;; Proof finished.
;; (cdp)
(save "NatToPosLt")

;; PosNotLeToLt
(set-goal "all p,q((p<=q -> F) -> q<p)")
(assume "p" "q")
(simp "<-" "NatToPosToNatId")
(assert "NatToPos(PosToNat q)=q")
 (use "NatToPosToNatId")
(assume "NatToPos(PosToNat q)=q")
(simp "<-" "NatToPos(PosToNat q)=q")
(simp "NatToPosLe")
(simp "NatToPosLt")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "NatNotLeToLt")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cdp)
(save "PosNotLeToLt")

;; PosNotLtToLe
(set-goal "all p,q((p<q -> F) -> q<=p)")
(assume "p" "q")
(simp "<-" "NatToPosToNatId")
(assert "NatToPos(PosToNat q)=q")
 (use "NatToPosToNatId")
(assume "NatToPos(PosToNat q)=q")
(simp "<-" "NatToPos(PosToNat q)=q")
(simp "NatToPosLe")
(simp "NatToPosLt")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "NatNotLtToLe")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cdp)
(save "PosNotLtToLe")

;; PosLeAntiSym
(set-goal "all p,q(p<=q -> q<=p -> p=q)")
(assume "p" "q")
(simp "<-" "PosToNatLe")
(simp "<-" "PosToNatLe")
(assume "NatLeHyp1" "NatLeHyp2")
(assert "PosToNat p=PosToNat q")
(use "NatLeAntiSym")
(use "NatLeHyp1")
(use "NatLeHyp2")
(use "PosToNatInj")
;; Proof finished.
;; (cdp)
(save "PosLeAntiSym")

;; PosLeMonPlus
(set-goal "all p,q,r,r0(p<=q -> r<=r0 -> p+r<=q+r0)")
(assume "p" "q" "r" "r0" "p<=q" "r<=r0")
(assert "p=NatToPos(PosToNat p)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "p=NatToPos(PosToNat p)")
(simp "p=NatToPos(PosToNat p)")
(drop "p=NatToPos(PosToNat p)")
(assert "q=NatToPos(PosToNat q)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "q=NatToPos(PosToNat q)")
(simp "q=NatToPos(PosToNat q)")
(drop "q=NatToPos(PosToNat q)")
(assert "r=NatToPos(PosToNat r)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "r=NatToPos(PosToNat r)")
(simp "r=NatToPos(PosToNat r)")
(drop "r=NatToPos(PosToNat r)")
(assert "r0=NatToPos(PosToNat r0)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "r0=NatToPos(PosToNat r0)")
(simp "r0=NatToPos(PosToNat r0)")
(drop "r0=NatToPos(PosToNat r0)")
(simp "<-" "NatToPosPlus")
(simp "<-" "NatToPosPlus")
(simp "NatToPosLe")
(use "NatLeMonPlus")
(simp "PosToNatLe")
(use "p<=q")
(simp "PosToNatLe")
(use "r<=r0")
;; ?_35:Zero<NatPlus(PosToNat q)(PosToNat r0)
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cdp)
(save "PosLeMonPlus")

;; PosLeMonTimes
(set-goal
 "all p,q,r,r0(p<=q -> r<=r0 -> p*r<=q*r0)")
(assume "p" "q" "r" "r0" "p<=q" "r<=r0")
(assert "p=NatToPos(PosToNat p)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "p=NatToPos(PosToNat p)")
(simp "p=NatToPos(PosToNat p)")
(drop "p=NatToPos(PosToNat p)")
(assert "q=NatToPos(PosToNat q)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "q=NatToPos(PosToNat q)")
(simp "q=NatToPos(PosToNat q)")
(drop "q=NatToPos(PosToNat q)")
(assert "r=NatToPos(PosToNat r)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "r=NatToPos(PosToNat r)")
(simp "r=NatToPos(PosToNat r)")
(drop "r=NatToPos(PosToNat r)")
(assert "r0=NatToPos(PosToNat r0)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "r0=NatToPos(PosToNat r0)")
(simp "r0=NatToPos(PosToNat r0)")
(drop "r0=NatToPos(PosToNat r0)")
(simp "<-" "NatToPosTimes")
(simp "<-" "NatToPosTimes")
(simp "NatToPosLe")
(use "NatLeMonTimes")
(simp "PosToNatLe")
(use "p<=q")
(simp "PosToNatLe")
(use "r<=r0")
;; ?_35:Zero<NatTimes(PosToNat q)(PosToNat r0)
(simp "<-" "PosToNatTimes")
(use "NatLtZeroPos")
(simp "<-" "PosToNatTimes")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cdp)
(save "PosLeMonTimes")

;; Since many properties involving PosMinus depend on <-hypotheses
;; we provide PosLtLeMonTimes and PosLeLtMonTimes

;; PosLtLeMonTimes
(set-goal "all p,q,r,r0(
 p<q -> r<=r0 -> p*r<q*r0)")
(assume "p" "q" "r" "r0")
(simp "<-" "PosLePosS")
(simp "<-" "PosPlus0CompRule")
(assume "Sp<=q" "r<=r0")
(assert "(p+1)*r<=q*r0")
 (use "PosLeMonTimes")
 (use "Sp<=q")
 (use "r<=r0")
(assume "(p+1)r<=qr")
(use "PosLtLeTrans" (pt "(p+1)*r"))
(simp "PosTimesPlusDistrLeft")
(ng)
(use "Truth")
(use "(p+1)r<=qr")
;; Proof finished.
;; (cdp)
(save "PosLtLeMonTimes")

;; PosLeLtMonTimes
(set-goal "all p,q,r,r0(
 p<=q -> r<r0 -> p*r<q*r0)")
(assume "p" "q" "r" "r0" "p<=q")
(simp "<-" "PosLePosS")
(simp "<-" "PosPlus0CompRule")
(assume "Sr<=r0")
(assert "p*(r+1)<=q*r0")
 (use "PosLeMonTimes")
 (use "p<=q")
 (use "Sr<=r0")
(assume "p*(r+1)<=qr0")
(use "PosLtLeTrans" (pt "p*(r+1)"))
(simp "PosTimesPlusDistr")
(ng)
(use "Truth")
(use "p*(r+1)<=qr0")
;; Proof finished.
;; (cdp)
(save "PosLeLtMonTimes")

;; PosLePlusCancelL
(set-goal "all p,q,r(p+q<=p+r)=(q<=r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "<-" (pf "NatToPos(PosToNat(p+q))=p+q"))
(simp "<-" (pf "NatToPos(PosToNat(p+r))=p+r"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(simp "NatToPosLe")
(ng) ;uses NatPlusCancelL
(simp "<-" "NatToPosLe")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(use "Truth")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(use "NatToPosToNatId")
(use "NatToPosToNatId")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p+q<=p+r" "q<=r")

;; PosLePlusCancelR
(set-goal "all p,q,r(p+q<=r+q)=(p<=r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "PosPlusComm")
(simp (pf "r+q=q+r"))
(ng)
(use "Truth")
(use "PosPlusComm")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p+q<=r+q" "p<=r")

;; PosLtPlusCancelL
(set-goal "all p,q,r(p+q<p+r)=(q<r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "<-" (pf "NatToPos(PosToNat(p+q))=p+q"))
(simp "<-" (pf "NatToPos(PosToNat(p+r))=p+r"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(simp "NatToPosLt")
(ng) ;uses NatPlusCancelL
(simp "<-" "NatToPosLt")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(use "Truth")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(use "NatToPosToNatId")
(use "NatToPosToNatId")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p+q<p+r" "q<r")

;; PosLtPlusCancelR
(set-goal "all p,q,r(p+q<r+q)=(p<r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "PosPlusComm")
(simp (pf "r+q=q+r"))
(ng)
(use "Truth")
(use "PosPlusComm")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p+q<r+q" "p<r")

;; PosTimesCancelL
(set-goal "all p,q,r(p*q=p*r -> q=r)")
(assume "p" "q" "r" "pq=pr")
(use "PosLeAntiSym")
;; 3,4
(use "PosNotLtToLe")
(assume "r<q")
(assert "p*r<p*q")
 (use "PosLeLtMonTimes")
 (use "Truth")
 (use "r<q")
(simp "pq=pr")
(assume "Absurd")
(use "Absurd")
;; 4 
(use "PosNotLtToLe")
(assume "q<r")
(assert "p*q<p*r")
 (use "PosLeLtMonTimes")
 (use "Truth")
 (use "q<r")
(simp "pq=pr")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "PosTimesCancelL")

;; PosTimesCancelR
(set-goal "all p,q,r(p*r=q*r -> p=q)")
(assume "p" "q" "r" "pr=qr")
(use "PosTimesCancelL" (pt "r"))
(simp "PosTimesComm")
(simp "pr=qr")
(use "PosTimesComm")
;; Proof finished.
;; (cdp)
(save "PosTimesCancelR")

;; PosLeTimesCancelR 
(set-goal "all p,q,r (p*r<=q*r)=(p<=q)") ;as rewrite rule
(assume "p" "q" "r")
(use "BooleAeqToEq")
;; 3,4
(assume "pr<=qr")
(use "PosNotLtToLe")
(assume "q<p")
(assert "q*r<p*r")
 (use "PosLtLeMonTimes")
 (use "q<p")
 (use "Truth")
(assume "qr<pr")
(assert "p*r<p*r")
 (use "PosLeLtTrans" (pt "q*r"))
 (use "pr<=qr")
 (use "qr<pr")
(assume "Absurd")
(use "Absurd")
;; 4
(assume "p<=q")
(use "PosLeMonTimes")
(use "p<=q")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p*r<=q*r" "p<=q")

;; PosLeTimesCancelL
(set-goal  "all p,q,r(p*q<=p*r)=(q<=r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "PosTimesComm")
(simp (pf "p*r=r*p"))
(use "Truth")
(use "PosTimesComm")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p*q<=p*r" "q<=r")

;; PosLeTimesCancelL
(set-goal  "all p,q,r(p*q<=p*r)=(q<=r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "PosTimesComm")
(simp (pf "p*r=r*p"))
(use "Truth")
(use "PosTimesComm")
;; Proof finished.
(add-rewrite-rule "p*q<=p*r" "q<=r")

;; PosLtTimesCancelL
(set-goal  "all p,q,r(p*q<p*r)=(q<r)") ;as rewrite rule
(assume "p" "q" "r")
(use "BooleAeqToEq")
;; 3,4
(assume "pq<pr")
(use "PosNotLeToLt")
(assume "r<=q")
(assert "p*r<=p*q")
 (use "PosLeMonTimes")
 (use "Truth")
 (use "r<=q")
(assume "pr<=pq")
(assert "p*q<p*q")
 (use "PosLtLeTrans" (pt "p*r"))
 (use "pq<pr")
 (use "pr<=pq")
(assume "Absurd")
(use "Absurd")
;; 4
(use "PosLeLtMonTimes")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p*q<p*r" "q<r")

;; PosLtTimesCancelR
(set-goal  "all p,q,r(p*q<r*q)=(p<r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "PosTimesComm")
(simp (pf "r*q=q*r"))
(use "Truth")
(use "PosTimesComm")
;; Proof finished.
(add-rewrite-rule "p*q<r*q" "p<r")

(set-goal "all p p<SZero p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng)
(use "IH")
(assume "p" "IH")
(ng)
(use "PosLtTrans" (pt "SZero p"))
(use "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<SZero p" "True")

;; PosLeLtCases
(set-goal "all p,q((p<=q -> Pvar) -> (q<p -> Pvar) -> Pvar)")
(assume "p" "q" "LeHyp" "LtHyp")
(use "NatLeLtCases" (pt "PosToNat p") (pt "PosToNat q") "?" "?")
;; 3,4
(assume "NatLeHyp")
(use "LeHyp")
(simp "<-" "PosToNatLe")
(use "NatLeHyp")
;; 4
(assume "NatLtHyp")
(use "LtHyp")
(simp "<-" "PosToNatLt")
(use "NatLtHyp")
;; Proof finished.
;; (cdp)
(save "PosLeLtCases")

;; PosLeCases
(set-goal "all p,q(p<=q -> (p<q -> Pvar) -> (p=q -> Pvar) -> Pvar)")
(assume "p" "q" "p<=q" "LtHyp" "EqHyp")
(use "NatLeCases" (pt "PosToNat p") (pt "PosToNat q") "?" "?" "?")
;; 3-5
(simp "PosToNatLe")
(use "p<=q")
;; 4
(simp "PosToNatLt")
(use "LtHyp")
;; 5
(assume "EqPosToNatHyp")
(use "EqHyp")
(simp "<-" "NatToPosToNatId")
(simp "EqPosToNatHyp")
(use "NatToPosToNatId")
;; Proof finished.
;; (cdp)
(save "PosLeCases")

;; PosLeMonPred
(set-goal "all p,q(p<=q -> PosPred p<=PosPred q)")
(assume "p" "q")
(use "PosLeCases" (pt "1") (pt "p"))
(use "Truth")
;; 3-5
(assume "1<p")
(use "PosLeCases" (pt "1") (pt "q"))
;; 7-9
(use "Truth")
(assume "1<q" "p<=q")
(assert "PosS(PosPred p)<=PosS(PosPred q)")
 (simp "PosSPosPredId")
 (simp "PosSPosPredId")
 (use "p<=q")
 (use "1<q")
 (use "1<p")
(ng)
(assume "Hyp")
(use "Hyp")
;; 9
(assume "1=q")
(simp "<-" "1=q")
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
;; 5
(assume "1=p" "Useless")
(simp "<-" "1=p")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosLeMonPred")

;; Rules for PosMinus:  They give correct results for p--q (only) if q<p.

(add-computation-rules
 "One--p" "One"
 "SZero p--One" "PosPred(SZero p)"
 "SZero p--SZero q" "SZero(p--q)"
 "SZero p--SOne q" "PosPred(SZero(p--q))"
 "SOne p--One" "SZero p"
 "SOne p--SZero q" "[if (p=q) One (SOne(p--q))]"
 "SOne p--SOne q" "SZero(p--q)")

;; (display-pconst "PosMinus")

;; (pp (nt (pt "7--4")))
;; (pp (nt (pt "6--4")))
;; (pp (nt (pt "66--44")))

;; PosMinusTotal
(set-totality-goal "PosMinus")
(assume "p^" "Tp")
(elim "Tp")

;; ?_3:allnc p^(TotalPos p^ -> TotalPos(1--p^))
(assume "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosOne")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalPosOne")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalPosOne")
;; ?_4:allnc p^(
;;      TotalPos p^ -> 
;;      allnc p^0(TotalPos p^0 -> TotalPos(p^ --p^0)) -> 
;;      allnc p^0(TotalPos p^0 -> TotalPos(SZero p^ --p^0)))
(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "PosPredTotal")
(use "TotalPosSZero")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "PosPredTotal")
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")
;; ?_5:allnc p^(
;;      TotalPos p^ -> 
;;      allnc p^0(TotalPos p^0 -> TotalPos(p^ --p^0)) -> 
;;      allnc p^0(TotalPos p^0 -> TotalPos(SOne p^ --p^0)))
(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "TotalPosSZero")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "BooleIfTotal")
(use "PosEqTotal")
(use "Tq")
(use "Tq2")
(use "TotalPosOne")
(use "TotalPosSOne")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")
;; Proof finished.
;; (cdp)
(save-totality)

(set-goal "all p PosS p--1=p")
(cases)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
(assume "p")
;; PosS(SOne p)--1=SOne p
(ng)
;; ?_8:PosPred(SZero(PosS p))=SOne p
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosS p--1" "p")

;; We consider the rules for NatMinus.  Do they hold for PosMinus?

;; PosMinusOneEqPosPred
(set-goal "all p p--1=PosPred p")
(cases)
;; 2-4
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosMinusOneEqPosPred")

;; The remaining rewrite rules for NatMinus are

;; (set-goal "all n,m Pred(Succ n--m)=n--m")
;; (set-goal "all nat nat--nat=0")
;; (set-goal "all nat Succ nat--nat=1")
;; (set-goal "all nat 0--nat=0")
;; (set-goal "all n,m n--m<=n")
;; (set-goal "all n,m n+m--m=n")
;; (set-goal "all n,m m+n--m=n")

;; The second computation rule p--PosS q=PosPred(p--q) is
;; wrong for p=2 and q=1.

;; (pp (nt (pt "2--PosS 1"))) ;2
;; (pp (nt (pt "PosPred(2--1)"))) ;1

;; We need a premise PosS q<p.  Since the proof is easiest with
;; an ordinary successor induction, we postpone the proof until we
;; have seen that NatToPos and PosToNat are isomorphisms w.r.t. -

;; We prove that PosToNat is an isomorphism w.r.t. -

;; Need that PosToNat is an isomorphism w.r.t. NatDouble and Pred.

;; SuccPosPred
(set-goal "all p(1<p -> PosToNat p=Succ(PosToNat(PosPred p)))")
(ind)
(assume "Absurd")
(use "Absurd")
;; 3
(cases)
;; 6-8
(ng)
(strip)
(use "Truth")
;; 7
(assume "p" "IH" "Useless")
(ng)
(simp "IH")
(ng)
(use "Truth")
(use "Truth")
; 8
(assume "p" "IH" "Useless")
(ng)
(use "Truth")
;; 4
(ng)
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "SuccPosPred")

;; PredPosPred
(set-goal "all p(1<p -> Pred(PosToNat p)=PosToNat(PosPred p))")
(assume "p" "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cdp)
(save "PredPosPred")

(set-goal "all p PosPred p<=p")
(assume "p")
(use "PosLeCases" (pt "1") (pt "p"))
(use "Truth")
(assume "1<p")
(simp "<-" "PosToNatLe")
(simp "<-" "PredPosPred")
(ng)
(use "Truth")
(use "1<p")
(assume "1=p")
(simp "<-" "1=p")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "PosPred p<=p" "True")

;; NatDoubleSZero
(set-goal "NatDouble(PosToNat p)=PosToNat(SZero p)")
(ind)
(ng)
(use "Truth")
(assume "p" "IH")
(ng)
(use "Truth")
(assume "p" "IH")
(ng)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatDoubleSZero")

;; Now we can prove that PosToNat is an isomorphism w.r.t. -

;; PosToNatMinus
(set-goal "all p,q(q<p -> PosToNat(p--q)=PosToNat p--PosToNat q)")
(ind)
;; 2-4
(assume "q" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "p" "IH1")
(ind)
;; 8-10
(ng)
;; ?^11:T -> PosToNat(PosPred(SZero p))=Pred(NatDouble(PosToNat p))
(simp "NatDoubleSZero")
(simp "PredPosPred")
(assume "Useless")
(use "Truth")
(ng)
(use "Truth")
;; 9
(assume "q" "IH2" "q<p")
(ng)
(simp "IH1")
(simp "NatDoubleMinus")
(use "Truth")
(use "q<p")
;; 10
(ng)
(assume "q" "IH2")
(assume "q<p")
(simp "<-" "NatDoubleMinus")
(simp "<-" "PredPosPred")
(simp "<-" "NatDoubleSZero")
(simp "IH1")
(use "Truth")
(use "q<p")
(ng)
(use "Truth")
;; 4
(assume "p" "IH1")
(ind)
;; 33-35
(ng)
(strip)
(use "Truth")
;; 34
(assume "q" "IH2")
(ng)
(assume "q<=p")
(use "PosLeCases" (pt "q") (pt "p"))
(use "q<=p")
(assume "q<p")
(assert "p=q -> q<q")
 (assume "p=q")
 (simphyp-with-to "q<p" "p=q" "Absurd")
 (use "Absurd")
(assume "p=q -> F")
(simp "p=q -> F")
(ng #t)
(simp "<-" "SuccNatMinus")
(simp "<-" "NatDoubleMinus")
(ng)
(simp "IH1")
(ng)
(use "Truth")
(use "q<p")
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "q<=p")
;; 43
(assume "q=p")
(simp "q=p")
(ng)
(use "Truth")
;; 35
(assume "q" "IH2" "q<p")
(ng #t)
(simp "IH1")
(simp "NatDoubleMinus")
(use "Truth")
(use "q<p")
;; Proof finished.
;; (cdp)
(save "PosToNatMinus")

;; Code discarded 2021-02-15
;; ;; PosToNatMinus
;; (set-goal "all p,q(q<p -> PosToNat(p--q)=PosToNat p--PosToNat q)")
;; (ind)
;; ;; 2-4
;; (assume "q" "Absurd")
;; (use "EfAtom")
;; (use "Absurd")
;; ;; 3
;; (assume "p" "IH1")
;; (ind)
;; ;; 8-10
;; (ng)
;; ;; ?^11:T -> PosToNat(PosPred(SZero p))=Pred(NatDouble(PosToNat p))
;; (simp "NatDoubleSZero")
;; (simp "PredPosPred")
;; (assume "Useless")
;; (use "Truth")
;; (ng)
;; (use "Truth")
;; ;; 9
;; (assume "q" "IH2" "q<p")
;; (ng)
;; (simp "IH1")
;; (simp "NatDoubleMinus")
;; (use "Truth")
;; (use "q<p")
;; ;; 10
;; (ng)
;; (assume "q" "IH2")
;; (assume "q<p")
;; (simp "<-" "NatDoubleMinus")
;; (simp "<-" "PredPosPred")
;; (simp "<-" "NatDoubleSZero")
;; (simp "IH1")
;; (use "Truth")
;; (use "q<p")
;; (ng)
;; (use "Truth")
;; ;; 4
;; (assume "p" "IH1")
;; (ind)
;; ;; 33-35
;; (ng)
;; (strip)
;; (use "Truth")
;; ;; 34
;; (assume "q" "IH2")
;; (ng)
;; (assume "q<=p")
;; (use "PosLeCases" (pt "q") (pt "p"))
;; (use "q<=p")
;; (assume "q<p")
;; (assert "p=q -> q<q")
;;  (assume "p=q")
;;  (simphyp-with-to "q<p" "p=q" "Absurd")
;;  (use "Absurd")
;; (assume "p=q -> F")
;; (simp "p=q -> F")
;; (ng #t)
;; (simp "<-" "SuccNatMinus")
;; (simp "<-" "NatDoubleMinus")
;; (ng)
;; (simp "IH1")
;; (ng)
;; (use "Truth")
;; (use "q<p")
;; (simp "NatDoubleLt")
;; (simp "PosToNatLt")
;; (use "q<p")
;; ;; 43
;; (assume "q=p")
;; (simp "q=p")
;; (ng)
;; (use "Truth")
;; ;; 35
;; (assume "q" "IH2" "q<p")
;; (ng #t)
;; (simp "IH1")
;; (simp "NatDoubleMinus")
;; (use "Truth")
;; (use "q<p")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "PosToNatMinus")

;; NatToPosMinus
(set-goal "all n,m(Zero<m -> m<n -> NatToPos(n--m)=NatToPos n--NatToPos m)")
(assume "n" "m" "0<m" "m<n")
(assert "Zero<n")
 (use "NatLtTrans" (pt "m"))
 (use "0<m")
 (use "m<n")
(assume "0<n") 
(assert "n--m=PosToNat(NatToPos n)--PosToNat(NatToPos m)")
 (simp "PosToNatToPosId")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "0<m")
 (use "0<n")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "PosToNatMinus")
(simp "NatToPosToNatId")
(use "Truth")
(simp "NatToPosLt")
(use "m<n")
(use "0<n")
(use "0<m")
;; Proof finished.
;; (cdp)
(save "NatToPosMinus")

;; Now we can continue proving the nat rewrite rules for pos

(set-goal "all p,q p+q--q=p")
(assume "p" "q")
(assert "p=NatToPos(PosToNat p)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "p=NatToPos(PosToNat p)")
(simp "p=NatToPos(PosToNat p)")
(drop "p=NatToPos(PosToNat p)")
(assert "q=NatToPos(PosToNat q)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "q=NatToPos(PosToNat q)")
(simp "q=NatToPos(PosToNat q)")
(drop "q=NatToPos(PosToNat q)")
(simp "<-" "NatToPosPlus")
(simp "<-" "NatToPosMinus")
(ng #t)
(use "Truth")
(simp "<-" "PosToNatPlus")
(simp "PosToNatLt")
(ng #t)
(use "Truth")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p+q--q" "p")

(set-goal "all p,q q+p--q=p")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "q+p--q" "p")

;; PosLtMonMinusLeft
(set-goal "all p,q,r(q<r -> p<q -> q--p<r--p)")
(assume "p" "q" "r" "q<r" "p<q")
(inst-with-to "NatToPosToNatId" (pt "q--p") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "r--p") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "NatToPosLt")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(use "NatLtMonMinusLeft")
(simp "PosToNatLt")
(use "q<r")
(use "NatLtToLe")
(simp "PosToNatLt")
(use "p<q")
(use "PosLtTrans" (pt "q"))
(use "p<q")
(use "q<r")
(use "p<q")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cdp)
(save "PosLtMonMinusLeft")

;; From NatPlusMinus we obtain PosPlusMinus using the isomorphisms
;; PosToNat and NatToPos.

;; PosPlusMinus
(set-goal "all p,q,r(r<q -> p+(q--r)=p+q--r)")
(assume "p" "q" "r" "r<q")
(assert
 "NatToPos(PosToNat(p+(q--r)))=NatToPos(PosToNat(p+q--r))")
 (simp "PosToNatPlus")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (simp "PosToNatPlus")
 (simp "NatPlusMinus")
 (use "Truth")
 (use "NatLtToLe")
 (simp "PosToNatLt")
 (use "r<q")
 (use "PosLtTrans" (pt "q"))
 (use "r<q")
 (use "Truth")
 (use "r<q")
 (simp "NatToPosToNatId")
 (simp "NatToPosToNatId")
(assume "Assertion")
(use "Assertion")
;; Proof finished.
;; (cdp)
(save "PosPlusMinus")

;; Code discarded 2021-02-15
;; ;; PosPlusMinus
;; (set-goal "all p,q,r(r<q -> p+(q--r)=p+q--r)")
;; (assume "p" "q" "r" "r<q")
;; (assert
;;  "NatToPos(PosToNat(p+(q--r)))=NatToPos(PosToNat(p+q--r))")
;;  (simp "PosToNatPlus")
;;  (simp "PosToNatMinus")
;;  (simp "PosToNatMinus")
;;  (simp "PosToNatPlus")
;;  (simp "NatPlusMinus")
;;  (use "Truth")
;;  (use "NatLtToLe")
;;  (simp "PosToNatLt")
;;  (use "r<q")
;;  (use "PosLtTrans" (pt "q"))
;;  (use "r<q")
;;  (use "Truth")
;;  (use "r<q")
;;  (simp "NatToPosToNatId")
;;  (simp "NatToPosToNatId")
;; (assume "Assertion")
;; (use "Assertion")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "PosPlusMinus")

;; PosMinusPlus
(set-goal "all p,q,r(r<p -> p--r+q=p+q--r)")
(assume "p" "q" "r" "r<p")
(inst-with-to "PosPlusMinus" (pt "q") (pt "p") (pt "r") "r<p"
	      "PosPlusMinusInst")
(simp "PosPlusComm")
(simp "PosPlusMinusInst")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosMinusPlus")

;; PosMinusPlusEq
(set-goal "all p,q(q<p -> p--q+q=p)")
(assume "p" "q" "q<p")
(simp "PosMinusPlus")
(use "Truth")
(use "q<p")
;; Proof finished.
;; (cdp)
(save "PosMinusPlusEq")

;; From NatMinusMinus we obtain PosMinusMinus using the isomorphisms
;; PosToNat and NatToPos.

;; PosMinusMinus
(set-goal "all p,q,r(r<q -> q<p+r -> p--(q--r)=p+r--q)")
(assume "p" "q" "r" "r<q" "q<p+r")
(assert "q--r<p")
 (assert "p=p+r--r")
  (use "Truth")
 (assume "p=p+r-r")
 (simp "p=p+r-r")
 (drop "p=p+r-r")
 (use "PosLtMonMinusLeft")
 (use "q<p+r")
 (use "r<q")
(assume "q-r<p")
(assert "NatToPos(PosToNat(p--(q--r)))=NatToPos(PosToNat(p+r--q))")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (simp "PosToNatPlus")
 (simp "NatMinusMinus")
 (use "Truth")
 (use "NatLtToLe")
 (simp "<-" "PosToNatPlus")
 (simp "PosToNatLt")
 (use "q<p+r")
 (use "NatLtToLe")
 (simp "PosToNatLt")
 (use "r<q")
 (use "q<p+r")
 (use "r<q")
 (use "q-r<p")
 (simp "NatToPosToNatId")
 (simp "NatToPosToNatId")
(assume "Hyp")
(use "Hyp")
;; Proof finished.
;; (cdp)
(save "PosMinusMinus")

;; Similarly to NatMinus5RewRule we have
;; q+r<p -> p--q--r=p--(q+r)
;; The assumption q+r<p is necessary since PosMinus does not
;; behave well for equal arguments.

;; Idea of the proof: Apply PosToNat o NatToPos outside.  Move
;; PosToNat inside (this needs q+r<p), use NatMinus5RewRule.  Notice
;; that the display by pp is not helpful for this level of detail.
;; Use ppn instead.

;; PosMinusMinusLeft
(set-goal "all p,q,r(q+r<p -> p--q--r=p--(q+r))")
(assume "p" "q" "r" "q+r<p")
(assert "q<p")
 (use "PosLtTrans" (pt "q+r"))
 (use "Truth")
 (use "q+r<p")
(assume "q<p")
(inst-with-to "NatToPosToNatId" (pt "p--q--r") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "p--(q+r)") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatPlus")
(simp "<-" "NatMinus5RewRule")
(use "Truth")
(use "q+r<p")
(use "q<p")
;; ?_17:r<p--q
(assert "r=q+r--q")
 (use "Truth")
(assume "r=q+r--q")
(simp "r=q+r--q")
(drop "r=q+r--q")
(use "PosLtMonMinusLeft")
(use "q+r<p")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosMinusMinusLeft")

;; PosTimesMinusDistr
(set-goal "all p,q,r(r<q ->  p*(q--r)=p*q--p*r)")
(assume "p" "q" "r" "r<q")
(inst-with-to "NatToPosToNatId" (pt "p*(q--r)") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "p*q--p*r") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "PosToNatTimes")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(ng)
(use "Truth")
(use "PosLeLtMonTimes")
(use "Truth")
(use "r<q")
(use "r<q")
;; Proof finished.
;; (cdp)
(save "PosTimesMinusDistr")

;; PosTimesMinusDistrLeft
(set-goal "all p,q,r(q<p ->  (p--q)*r=p*r--q*r)")
(assume "p" "q" "r" "q<p")
(inst-with-to "NatToPosToNatId" (pt "(p--q)*r") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "p*r--q*r") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "PosToNatTimes")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(ng)
(use "Truth")
(use "PosLtLeMonTimes")
(use "q<p")
(use "Truth")
(use "q<p")
;; Proof finished.
;; (cdp)
(save "PosTimesMinusDistrLeft")

;; Rules for PosMax

(add-computation-rules
 "One max p" "p"
 "SZero p max One" "SZero p"
 "SZero p max SZero q" "SZero(p max q)"
 "SZero p max SOne q" "[if (p<=q) (SOne q) (SZero p)]"
 "SOne p max One" "SOne p"
 "SOne p max SZero q" "[if (q<=p) (SOne p) (SZero q)]"
 "SOne p max SOne q" "SOne(p max q)")

;; PosMaxTotal
(set-totality-goal "PosMax")
(assume "p^" "Tp")
(elim "Tp")
(ng #t)
(assume "q^" "Tq")
(use "Tq")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosSZero")
(use "Tp1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "IHp1")
(use "Tq1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSOne")
(use "Tq1")
(use "TotalPosSZero")
(use "Tp1")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosSOne")
(use "Tp1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tq1")
(use "Tp1")
(use "TotalPosSOne")
(use "Tp1")
(use "TotalPosSZero")
(use "Tq1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSOne")
(use "IHp1")
(use "Tq1")
;; Proof finished.
;; (cdp)
(save-totality)

(set-goal "all p p max One=p")
(cases)
(use "Truth")
(assume "p")
(ng #t)
(use "Truth")
(assume "p")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p max One" "p")

(set-goal "all p p max p=p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p max p" "p")

(set-goal "all p p max Succ Zero=p")
(assume "p")
(use "PosLeLtCases" (pt "p") (pt "1"))
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
(assume "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cdp)
(save "NatMaxPosOne")

(set-goal "all p Succ Zero max p=p")
(assume "p")
(use "PosLeLtCases" (pt "p") (pt "1"))
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
(assume "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cdp)
(save "NatMaxOnePos")

;; PosMaxComm
(set-goal "all p,q p max q = q max p")
(ind)
;; 2-4
(strip)
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 7-9
(use "Truth")
;; 8
(use "IH")
;; 9
(ng)
(strip)
(use "Truth")
;; 4
(assume "p" "IH")
(cases)
;; 13-15
(use "Truth")
;; 14
(ng)
(strip)
(use "Truth")
;; 15
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosMaxComm")

;; PosMaxEq1
(set-goal "all p,q(q<=p -> p max q=p)")
(ind)
(ng)
(assume "q" "q=1")
(use "q=1")
;; 3
(assume "p" "IH")
(cases)
;; 8-10
(strip)
(use "Truth")
;; 9
(ng)
(use "IH")
;; 10
(ng)
(assume "q" "q<p")
(assert "p<=q -> F")
 (assume "p<=q")
 (assert "p<p")
  (use "PosLeLtTrans" (pt "q"))
  (use "p<=q")
  (use "q<p")
 (assume "p<p")
 (use "p<p")
(assume "p<=q -> F")
(simp "p<=q -> F")
(use "Truth")
;; 4
(assume "p" "IH")
(cases)
;; 26-28
(ng)
(strip)
(use "Truth")
;; 27
(ng)
(assume "q" "q<=p")
(simp "q<=p")
(use "Truth")
;; 28
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosMaxEq1")

;; PosMaxEq2
(set-goal "all p,q(p<=q -> p max q=q)")
(assume "p" "q")
(simp "PosMaxComm")
(use "PosMaxEq1")
;; Proof finished.
;; (cdp)
(save "PosMaxEq2")

;; We prove that PosToNat is an isomorphism w.r.t. max

;; PosToNatMax
(set-goal "all p,q PosToNat(p max q)=PosToNat p max PosToNat q")
(ind)
;; 2-4
(assume "q")
(ng)
(simp "NatMaxOnePos")
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 9-11
(ng)
(simp "NatDoubleSZero")
(simp "NatMaxPosOne")
(use "Truth")
;; 10
(assume "q")
(ng)
(simp "IH")
(simp "NatMaxDouble")
(use "Truth")
;; 11
(assume "q")
(ng)
(cases (pt "p<=q"))
(assume "p<=q")
(ng)
(simp "NatMaxEq2")
(use "Truth")
(use "NatLeTrans" (pt "NatDouble(PosToNat q)"))
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "p<=q")
(use "Truth")
;; 22
(assume "p<=q -> F")
(ng)
(simp "NatMaxEq1")
(use "Truth")
(simp "NatLeSuccDoubleDouble")
(assert "q<p")
 (use "PosNotLeToLt")
 (use "p<=q -> F")
(assume "q<p")
(simp "PosToNatLt")
(use "q<p")
;; 4
(assume "p" "IH")
(cases)
;; 42-44
(ng)
(use "Truth")
;; 43
(assume "q")
(ng)
(cases (pt "q<=p"))
(assume "q<=p")
(ng)
(simp "NatMaxEq1")
(use "Truth")
(use "NatLeTrans" (pt "NatDouble(PosToNat p)"))
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "q<=p")
(use "Truth")
;; 49
(assume "q<=p -> F")
(ng)
(simp "NatMaxEq2")
(use "Truth")
(simp "NatLeSuccDoubleDouble")
(assert "p<q")
 (use "PosNotLeToLt")
 (use "q<=p -> F")
(assume "p<q")
(simp "PosToNatLt")
(use "p<q")
;; 44
(ng)
(assume "q")
(simp "NatMaxDouble")
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosToNatMax")

;; PosMaxUB1
(set-goal "all p,q p<=p max q")
(assume "p" "q")
(assert "NatToPos(PosToNat p)<=NatToPos(PosToNat(p max q))")
 (simp "NatToPosLe")
 (simp "PosToNatMax")
 (use "NatMaxUB1")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "p<=p max q")
(use "p<=p max q")
;; Proof finished.
;; (cdp)
(save "PosMaxUB1")

;; PosMaxUB2
(set-goal "all p,q q<=p max q")
(assume "p" "q")
(simp "PosMaxComm")
(use "PosMaxUB1")
;; Proof finished.
;; (cdp)
(save "PosMaxUB2")

;; PosMaxLUB
(set-goal "all p,q,r(p<=r -> q<=r -> p max q<=r)")
(assume "p" "q" "r")
(assert "NatToPos(PosToNat p)<=NatToPos(PosToNat r) ->
         NatToPos(PosToNat q)<=NatToPos(PosToNat r) ->
         NatToPos(PosToNat(p max q))<=NatToPos(PosToNat r)")
 (simp "NatToPosLe")
 (simp "NatToPosLe")
 (simp "NatToPosLe")
 (simp "PosToNatMax")
 (use "NatMaxLUB")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "p<=r -> q<=r -> p max q<=r")
(use "p<=r -> q<=r -> p max q<=r")
;; Proof finished.
;; (cdp)
(save "PosMaxLUB")

;; PosTimesMaxDistr
(set-goal "all p,q,r p*(q max r)=p*q max(p*r)")
(ind)
;; 2-4
(assume "q" "r")
(use "Truth")
;; 3
(assume "p" "IH" "q" "r")
(ng)
(use "IH")
;; 4
(assume "p" "IH" "q" "r")
(use "PosLeLtCases" (pt "q") (pt "r"))
;; 9,10
(assume "q<=r")
(simp (pf "q max r=r"))
(simp (pf "SOne p*q max(SOne p*r)=SOne p*r"))
(use "Truth")
(use "PosMaxEq2")
(use "PosLeMonTimes")
(use "Truth")
(use "q<=r")
(use "PosMaxEq2")
(use "q<=r")
;; 10
(assume "r<q")
(inst-with-to "PosLtToLe" (pt "r") (pt "q") "r<q" "r<=q")
(simp (pf "q max r=q"))
(simp (pf "SOne p*q max(SOne p*r)=SOne p*q"))
(use "Truth")
(use "PosMaxEq1")
(use "PosLeMonTimes")
(use "Truth")
(use "r<=q")
(use "PosMaxEq1")
(use "r<=q")
;; Proof finished.
;; (cdp)
(save "PosTimesMaxDistr")

;; Rules for PosMin

(add-computation-rules
 "One min p" "One"
 "SZero p min One" "One"
 "SZero p min SZero q" "SZero(p min q)"
 "SZero p min SOne q" "[if (p<=q) (SZero p) (SOne q)]"
 "SOne p min One" "One"
 "SOne p min SZero q" "[if (q<=p) (SZero q) (SOne p)]"
 "SOne p min SOne q" "SOne(p min q)")

;; PosMinTotal
(set-totality-goal "PosMin")
(assume "p^" "Tp")
(elim "Tp")
(ng #t)
(assume "q^" "Tq")
(use "TotalPosOne")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosOne")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "IHp1")
(use "Tq1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSZero")
(use "Tp1")
(use "TotalPosSOne")
(use "Tq1")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosOne")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tq1")
(use "Tp1")
(use "TotalPosSZero")
(use "Tq1")
(use "TotalPosSOne")
(use "Tp1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSOne")
(use "IHp1")
(use "Tq1")
;; Proof finished.
;; (cdp)
(save-totality)

(set-goal "all p p min One=One")
(cases)
(use "Truth")
(assume "p")
(ng #t)
(use "Truth")
(assume "p")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p min One" "One")

(set-goal "all p p min p=p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p min p" "p")

;; NatMinOnePos
(set-goal "all p Succ Zero min p=One")
(assume "p")
(use "PosLeLtCases" (pt "p") (pt "1"))
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
(assume "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cdp)
(save "NatMinOnePos")

;; NatMinPosOne
(set-goal "all p p min Succ Zero=One")
(assume "p")
(use "PosLeLtCases" (pt "p") (pt "1"))
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
(assume "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cdp)
(save "NatMinPosOne")

;; PosMinComm
(set-goal "all p,q p min q = q min p")
(ind)
;; 2-4
(strip)
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 7-9
(use "Truth")
;; 8
(use "IH")
;; 9
(ng)
(strip)
(use "Truth")
;; 4
(assume "p" "IH")
(cases)
;; 13-15
(use "Truth")
;; 14
(ng)
(strip)
(use "Truth")
;; 15
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosMinComm")

;; PosMinEq1
(set-goal "all p,q(q<=p -> p min q=q)")
(ind)
(ng)
(assume "q" "q=1")
(simp "q=1")
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 9--11
(strip)
(use "Truth")
;; 10
(ng)
(use "IH")
;; 11
(ng)
(assume "q" "q<p")
(assert "p<=q -> F")
 (assume "p<=q")
 (assert "p<p")
  (use "PosLeLtTrans" (pt "q"))
  (use "p<=q")
  (use "q<p")
 (assume "p<p")
 (use "p<p")
(assume "p<=q -> F")
(simp "p<=q -> F")
(use "Truth")
;; 4
(assume "p" "IH")
(cases)
;; 27-29
(ng)
(strip)
(use "Truth")
;; 28
(ng)
(assume "q" "q<=p")
(simp "q<=p")
(use "Truth")
;; 29
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosMinEq1")

;; PosMinEq2
(set-goal "all p,q(p<=q -> p min q=p)")
(assume "p" "q")
(simp "PosMinComm")
(use "PosMinEq1")
;; Proof finished.
;; (cdp)
(save "PosMinEq2")

;; We prove that PosToNat is an isomorphism w.r.t. min

;; PosToNatMin
(set-goal "all p,q PosToNat(p min q)=PosToNat p min PosToNat q")
(ind)
;; 2-4
(assume "q")
(ng)
(simp "NatMinOnePos")
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 9-11
(ng)
(simp "NatDoubleSZero")
(simp "NatMinPosOne")
(use "Truth")
;; 10
(assume "q")
(ng)
(simp "IH")
(simp "NatMinDouble")
(use "Truth")
;; 11
(assume "q")
(ng)
(cases (pt "p<=q"))
(assume "p<=q")
(ng)
(simp "NatMinEq1")
(use "Truth")
(use "NatLeTrans" (pt "NatDouble(PosToNat q)"))
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "p<=q")
(use "Truth")
;; 22
(assume "p<=q -> F")
(ng)
(simp "NatMinEq2")
(use "Truth")
(simp "NatLeSuccDoubleDouble")
(assert "q<p")
 (use "PosNotLeToLt")
 (use "p<=q -> F")
(assume "q<p")
(simp "PosToNatLt")
(use "q<p")
;; 4
(assume "p" "IH")
(cases)
;; 42-44
(ng)
(use "Truth")
;; 43
(assume "q")
(ng)
(cases (pt "q<=p"))
(assume "q<=p")
(ng)
(simp "NatMinEq2")
(use "Truth")
(use "NatLeTrans" (pt "NatDouble(PosToNat p)"))
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "q<=p")
(use "Truth")
;; 49
(assume "q<=p -> F")
(ng)
(simp "NatMinEq1")
(use "Truth")
(simp "NatLeSuccDoubleDouble")
(assert "p<q")
 (use "PosNotLeToLt")
 (use "q<=p -> F")
(assume "p<q")
(simp "PosToNatLt")
(use "p<q")
;; 44
(ng)
(assume "q")
(simp "NatMinDouble")
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosToNatMin")

;; PosMinLB1
(set-goal "all p,q p min q<=p")
(assume "p" "q")
(assert "NatToPos(PosToNat(p min q))<=NatToPos(PosToNat p)")
 (simp "NatToPosLe")
 (simp "PosToNatMin")
 (use "NatMinLB1")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "p min q<=p")
(use "p min q<=p")
;; Proof finished.
;; (cdp)
(save "PosMinLB1")

;; PosMinLB2
(set-goal "all p,q p min q<=q")
(assume "p" "q")
(simp "PosMinComm")
(use "PosMinLB1")
;; Proof finished.
;; (cdp)
(save "PosMinLB2")

;; PosMinGLB
(set-goal "all p,q,r(r<=p -> r<=q -> r<=p min q)")
(assume "p" "q" "r")
(assert "NatToPos(PosToNat r)<=NatToPos(PosToNat p) ->
         NatToPos(PosToNat r)<=NatToPos(PosToNat q) ->
         NatToPos(PosToNat r)<=NatToPos(PosToNat(p min q))")
 (simp "NatToPosLe")
 (simp "NatToPosLe")
 (simp "NatToPosLe")
 (simp "PosToNatMin")
 (use "NatMinGLB")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "r<=p -> r<=q -> r<=p min q")
(use "r<=p -> r<=q -> r<=p min q")
;; Proof finished.
;; (cdp)
(save "PosMinGLB")

;; Rules for NatExp : nat=>nat=>nat

(add-computation-rules
 "n**Zero" "Succ Zero"
 "n**Succ m" "n**m*n")

;; NatExpTotal
(set-totality-goal "NatExp")
(assume "n^" "Tn" "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatZero")

(assume "m^1" "Tm1" "IHm1")
(ng #t)
(use "NatTimesTotal")
(use "IHm1")
(use "Tn")
;; Proof finished.
;; (cdp)
(save-totality)

;; NatLeOneTwoExp
(set-goal "all n Succ Zero<=(Succ(Succ Zero))**n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "NatLeTrans" (pt "Succ(Succ Zero)**n+Succ Zero"))
(use "Truth")
(use "NatLeMonPlus")
(use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeOneTwoExp")

;; NatLeMonTwoExp
(set-goal "all n,m(n<=m -> 2**n<=2**m)")
(ind)
;; 2,3
(ng)
(assume "m" "Useless")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "n<=m")
(ng)
(use "IH")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "NatLeMonTwoExp")

(set-goal "all pos,nat (PosToNat pos**nat)=PosToNat(pos**nat)")
(assume "pos")
(ind)
(ng #t)
(use "Truth")
(assume "nat" "IH")
(ng #t)
(simp "IH")
(simp "PosToNatTimes")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rules
 "(PosToNat pos)**nat" "PosToNat(pos**nat)")

;; Rules for PosLog

(add-computation-rules
 "PosLog 1" "Zero"
 "PosLog(SZero p)" "Succ(PosLog p)"
 "PosLog(SOne p)" "Succ(PosLog p)")

(set-totality-goal "PosLog")
(use "AllTotalElim")
(ind)
(use "TotalNatZero")
(assume "p" "IH")
(ng)
(use "TotalNatSucc")
(use "IH")
(assume "p" "IH")
(ng)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; (pp (nt (pt "PosLog 8")))
;; Succ(Succ(Succ Zero))

;; PosLogEqP
(set-goal "allnc p^,q^(EqPPos p^ q^ -> EqPNat(PosLog p^)(PosLog q^))")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
;; 3-5
(ng #t)
(use "EqPNatZero")
;; 4
(assume "p^1" "q^1" "EqPp1q1" "IH")
(ng #t)
(use "EqPNatSucc")
(use "IH")
;; 5
(assume "p^1" "q^1" "EqPp1q1" "IH")
(ng #t)
(use "EqPNatSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosLogEqP")

;; PosLogZero
(set-goal "all p (PosLog p=Zero)=(p=1)")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosLogZero")

;; PosLogZeroLt
(set-goal "all p (Zero<PosLog p)=(1<p)")
(cases)
;; 2-4
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosLogZeroLt")

;; PosLtZeroLog
(set-goal "all p(1<p -> Zero<PosLog p)")
(cases)
;; 2-4
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "p" "Useless")
(use "Truth")
;; 4
(assume "p" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosLtZeroLog")

;; PosLeExpTwoLog
(set-goal "all p 2**PosLog p<=p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosLeExpTwoLog")

;; PosLtExpTwoSuccLog
(set-goal "all p p<2**Succ(PosLog p)")
(ind)
(use "Truth")
(assume "p")
(ng #t)
(assume "IH")
(use "IH")
(assume "p")
(ng #t)
(assume "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosLtExpTwoSuccLog")

;; PosLeMonLog
(set-goal "all p,q(p<=q -> PosLog p<=PosLog q)")
(ind)
;; 2-4
(assume "q" "Useless")
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 7-9
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 8
(use "IH")
;; 9
(use "IH")
;; 4
(assume "p" "IH")
(cases)
;; 13-15
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 14
(assume "q" "p<q")
(ng)
(inst-with-to "PosLtToLe" (pt "p") (pt "q") "p<q" "p<=q")
(use "IH")
(use "p<=q")
;; 15
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosLeMonLog")

;; PosExpTwoNatPlus
(set-goal "2**n*2**m=2**(n+m)")
(assume "n")
(ind)
(ng)
(use "Truth")
;; Step
(assume "m" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosExpTwoNatPlus")

;; PosExpTwoPosPlus
(set-goal "all p,q 2**p*2**q=2**(p+q)")
(assume "p" "q")
(simp "PosToNatPlus")
(use "PosExpTwoNatPlus")
;; Proof finished.
;; (cdp)
(save "PosExpTwoPosPlus")

(set-goal "all p,q p--q<=p")
(assert "all p,q(p<=q -> p--q<=p)")
(ind)
;; 4-6
(strip)
(use "Truth")
;; 5
(assume "p" "IH")
(cases)
;; 9-11
(strip)
(use "Truth")
;; 10
(use "IH")
;; 11
(assume "q" "p<=q")
(ng)
(use "PosLeTrans" (pt "SZero(p--q)"))
(use "Truth")
(use "IH")
(use "p<=q")
;; 6
(assume "p" "IH")
(cases)
;; 19-21
(strip)
(use "Truth")
;; 20
(assume "q" "p<q")
(ng)
(cases (pt "p=q"))
(strip)
(use "Truth")
(assume "p=q -> F")
(use "IH")
(use "PosLtToLe")
(use "p<q")
;; 21
(use "IH")
;; Assertion proved
(assume "Assertion" "p" "q")
(use "PosLeLtCases" (pt "p") (pt "q"))
(use "Assertion")
(drop "Assertion")
;; ?_34:q<p -> p--q<=p
(assume "q<p")
(simp "<-" "PosToNatLe")
(simp "PosToNatMinus")
(ng)
(use "Truth")
(use "q<p")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p--q<=p" "True")

(set-goal "all p p<=SZero p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng)
(use "IH")
(assume "p" "IH")
(ng)
(use "PosLeLtTrans" (pt "SZero p"))
(use "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<=SZero p" "True")

;; PosLeMonPosExp
(set-goal "all p,n,m(n<=m -> p**n<=p**m)")
(assume "p")
(ind)
;; 3,4
(strip)
(use "Truth")
;; 4
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
(save "PosLeMonPosExp")

(set-goal "all p 2<=2**p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng)
(simp "<-" "NatDoublePlusEq")
(simp "<-" "PosExpTwoNatPlus")
(use "PosLeTrans" (pt "2*2"))
(use "Truth")
(use "PosLeMonTimes")
(use "IH")
(use "IH")
;; 4
(assume "p" "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "2<=2**p" "True")

(set-goal "all p p<2**p")
(ind)
;; 2-4
(use "Truth")
;; 3
(assume "p" "IH")
(ng)
(simp "<-" "NatDoublePlusEq")
(simp "<-" "PosExpTwoNatPlus")
(simp (pf "SZero p=2*p"))
(use "PosLeLtTrans" (pt "2**p*p"))
(use "PosLeMonTimes")
(use "Truth")
(use "Truth")
(use "PosLeLtMonTimes")
(use "Truth")
(use "IH")
(use "Truth")
;; 4
(assume "p" "IH")
(ng)
(simp "<-" "NatDoublePlusEq")
(simp "<-" "PosExpTwoNatPlus")
;; ?^20:p<2**p*2**p
(use "PosLeLtTrans" (pt "p*1"))
(use "Truth")
(use "PosLtLeMonTimes")
(use "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "p<2**p" "True")

(set-goal "all p 1<2**p")
(assume "p")
(use "PosLeLtTrans" (pt "p"))
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "1<2**p" "True")

;; TwoExpNatLe
(set-goal "all n,m (2**n<=2**m)=(n<=m)")
(ind)
;; 2,3
(cases)
;; 4,5
(use "Truth")
;; 5
(ng)
(assume "n")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 9.10
(ng)
(use "Truth")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "TwoExpNatLe")

;; TwoExpNatLt
(set-goal "all n,m (2**n<2**m)=(n<m)")
(ind)
;; 2,3
(cases)
;; 4,5
(use "Truth")
;; 5
(ng)
(assume "n")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 9,10
(ng)
(use "Truth")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "TwoExpNatLt")

;; TwoExpPosLe
(set-goal "all p,q (2**p<=2**q)=(p<=q)")
(assume "p" "q")
(inst-with-to "TwoExpNatLe" (pt "PosToNat p") (pt "PosToNat q") "Inst")
(simp "Inst")
(use "PosToNatLe")
;; Proof finished.
;; (cdp)
(save "TwoExpPosLe")

;; NatToPosNatPlusSucc
(set-goal "all p,n NatToPos(p+Succ n)=PosS(NatToPos(p+n))")
(assume "p" "n")
(simp "NatPlus1CompRule")
(simp "SuccPosS")
(use "Truth")
(use "NatLeLtTrans" (pt "Zero+n"))
(use "Truth")
(simp "NatLt3RewRule")
(use "NatLtZeroPos")
;; Proof finished.
;; (cdp)
(save "NatToPosNatPlusSucc")

;; NatLePlusTimes
(set-goal "all n,m(2<=n -> 2<=m -> n+m<=n*m)")
(assert "all n,m (n+2)+(m+2)<=(n+2)*(m+2)")
(assume "n" "m")
(simp "NatTimesPlusDistr")
(simp "NatTimesPlusDistrLeft")
(simp "NatTimesPlusDistrLeft")
(ng)
(simp "<-" "NatPlus2RewRule")
(simp "<-" "NatPlus2RewRule")
(use "NatLeTrans" (pt "m+(n+n)"))
(simp "NatPlusComm")
(ng)
(use "Truth")
(ng)
(use "Truth")
;; Assertion proved.
(assume "NatLePlusTimesAux")
(assert "all n(2<=n -> n=Pred(Pred n)+2)")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "Useless")
(use "Truth")
;; Assertion proved.
(assume "Assertion" "n" "m" "2<=n" "2<=m")
(simp (pf "n=Pred(Pred n)+2"))
(simp (pf "m=Pred(Pred m)+2"))
(use "NatLePlusTimesAux")
(use "Assertion")
(use "2<=m")
(use "Assertion")
(use "2<=n")
;; Proof finished.
;; (cdp)
(save "NatLePlusTimes")

;; PosLePlusTimes
(set-goal "all p,q(2<=p -> 2<=q -> p+q<=p*q)")
(assume "p" "q" "2<=p" "2<=q")
(simp "<-" "PosToNatLe")
(simp "PosToNatPlus")
(simp "PosToNatTimes")
(use "NatLePlusTimes")
(simp "PosToNatLe")
(use "2<=p")
(simp "PosToNatLe")
(use "2<=q")
;; Proof finished.
;; (cdp)
(save "PosLePlusTimes")

;; PosLeMonPosExpPos
(set-goal "all r,p,q(p<=q -> r**p<=r**q)")
(assume "r" "p" "q" "p<=q")
(assert "NatLe p q")
(simp "PosToNatLe")
(use "p<=q")
(use "PosLeMonPosExp")
;; Proof finished.
;; (cdp)
(save "PosLeMonPosExpPos")

;; PosLeTimesTwoExp
(set-goal "all p 2*p<=2**p")
(ind)
;; 2-4
(use "Truth")
;; 3
(assume "p" "IH")
;; ?^5:2*SZero p<=2**SZero p
(simp "PosTimes1CompRule")
(simp "SZeroPosPlus")
(simp (pf "SZero p=p+p"))
(simp "<-" "PosExpTwoPosPlus")
(use "PosLeTrans" (pt "2**p+2**p"))
(use "PosLeMonPlus")
(use "IH")
(use "IH")
(use "PosLePlusTimes")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
(use "SZeroPosPlus")
;; 4
(assume "p" "IH")
(simp "PosTimes2CompRule")
(simp "PosToNat2CompRule")
(simp "PosExp1CompRule")
(assert "all q q*2=q+q")
(assume "q")
(ng #t)
(use "SZeroPosPlus")
;; Assertion proved.
(assume "Assertion")
(simp "Assertion")
(use "PosLeMonPlus")
;; ?^33:SZero(2*p)<=2**SZero p
(simp (pf "SZero(2*p)=2*p+2*p"))
;; 35,36
(simp (pf "SZero p=p+p"))
(simp "<-" "PosExpTwoPosPlus")
(use "PosLeTrans" (pt "2**p+2**p"))
(use "PosLeMonPlus")
(use "IH")
(use "IH")
(use "PosLePlusTimes")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
(use "SZeroPosPlus")
;; 36
(use "SZeroPosPlus")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosLeTimesTwoExp")

(set-goal "all p (2**p<=1)=False")
(assume "p")
(use "AtomFalse")
(assume "LeH")
(assert "2*p<=1")
(use "PosLeTrans" (pt "2**p"))
(use "PosLeTimesTwoExp")
(use "LeH")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "2**p<=1" "False")

;; PosTwoExpEqOneFalse
(set-goal "all p (2**p=1)=False")
(assume "p")
(use "AtomFalse")
(assume "2**p=1")
(assert "2**p<=1")
(simp "2**p=1")
(use "Truth")
(simp "PosLe19RewRule")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "PosTwoExpEqOneFalse")

;; SZeroPosTimes
(set-goal "all p SZero p=2*p")
(ind)
(use "Truth")
(assume "p" "IH")
(use "Truth")
(assume "p" "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "SZeroPosTimes")

;; PosMinusOnePred
(set-goal "all p(1<p -> p--1=PosPred p)")
(cases)
;; 2-4
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "p" "Useless")
(use "Truth")
;; 4
(assume "p" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosMinusOnePred")

;; PosLtMonPosExpTwo
(set-goal "all n,m(n<m -> 2**n<2**m)")
(ind)
;; 3,4
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "Useless")
(use "Truth")
;; 4
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosLtMonPosExpTwo")

;; PosLtMonPosExpTwoPos
(set-goal "all p,q(p<q -> 2**p<2**q)")
(assume "p" "q" "p<q")
(assert "NatLt p q")
(simp "PosToNatLt")
(use "p<q")
(use "PosLtMonPosExpTwo")
;; Proof finished.
;; (cdp)
(save "PosLtMonPosExpTwoPos")

;; Added 2021-08-22

;; PosLeMonNatToPos
(set-goal "all n,m(n<=m -> NatToPos n<=NatToPos m)")
(cases)
;; 2,3
(assume "m" "Useless")
(use "Truth")
;; 3
(assume "n")
(cases)
;; 6,7
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; ?^7:all n0(Succ n<=Succ n0 -> NatToPos(Succ n)<=NatToPos(Succ n0))
(assume "m" "n<=m")
(simp "NatToPosLe")
(use "n<=m")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosLeMonNatToPos")

;; PosLeMoncNatPos
(set-goal "all n,m(n<=m -> cNatPos n<=cNatPos m)")
(assume "n" "m" "n<=m")
(simp "NatPosExFree")
(simp "NatPosExFree")
(use "PosLeMonNatToPos")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "PosLeMoncNatPos")

;; NatEvenTwoExp
(set-goal "all n(Zero<n -> NatEven(PosToNat(2**n)))")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "Useless")
(ng #t)
(use "NatEvenDouble")
;; Proof finished.
;; (cdp)
(save "NatEvenTwoExp")

;; Added 2021-10-15

;; NatLePosExpTwo
(set-goal "all n Succ Zero<=2**n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
;; ?^5:Succ Zero<=NatDouble(PosToNat(2**n))
(use "NatLeTrans" (pt "PosToNat(2**n)"))
(use "IH")
(use "NatLeDouble")
;; Proof finished.
;; (cdp)
(save "NatLePosExpTwo")

;; ZeroLtTwoExp
(set-goal "all n Zero<2**n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "NatLt0Double")
(use "IH")
;; Proof finished.
;; (cdp)
(save "ZeroLtTwoExp")

(add-program-constant "PosEven" (py "pos=>boole"))
(add-computation-rules
 "PosEven 1" "False"
 "PosEven(SZero p)" "True"
 "PosEven(SOne p)" "False")

(set-totality-goal "PosEven")
(fold-alltotal)
(cases)
;; 3-5
(use "TotalVar")
;; 4
(assume "p")
(use "TotalVar")
;; 5
(assume "p")
(use "TotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

(add-program-constant "PosOdd" (py "pos=>boole"))
(add-computation-rules
 "PosOdd 1" "True"
 "PosOdd(SZero p)" "False"
 "PosOdd(SOne p)" "True")

(set-totality-goal "PosOdd")
(fold-alltotal)
(cases)
;; 3-5
(use "BooleTotalVar")
;; 4
(assume "p")
(use "BooleTotalVar")
;; 5
(assume "p")
(use "BooleTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; In 2**n*p with p odd both n and p are uniquely determined.  They can
;; obtained by PosToExp and PosToOdd.

;; PosToExp returns the exponent of two in the prime factor
;; decomposition of a positive number.

(add-program-constant "PosToExp" (py "pos=>nat"))
(add-computation-rules
 "PosToExp 1" "Zero"
 "PosToExp(SZero p)" "Succ(PosToExp p)"
 "PosToExp(SOne p)" "Zero")

(set-totality-goal "PosToExp")
(fold-alltotal)
(ind)
;; 3-5
(use "NatTotalVar")
;; 4
(assume "p" "IH")
(use "TotalNatSucc")
(use "IH")
;; 5
(assume "p" "Useless")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; PosToOdd returns the odd part of a positive number,
(add-program-constant "PosToOdd" (py "pos=>pos"))
(add-computation-rules
 "PosToOdd 1" "1"
 "PosToOdd(SZero p)" "PosToOdd p"
 "PosToOdd(SOne p)" "SOne p")

(set-totality-goal "PosToOdd")
(fold-alltotal)
(ind)
;; 3-5
(use "PosTotalVar")
;; 4
(assume "p" "IH")
(use "IH")
;; 5
(assume "p" "Useless")
(use "PosTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; PosTimesExpOddId
(set-goal "all p 2**PosToExp p*PosToOdd p=p")
(ind)
;; 2-4
(use "Truth")
(assume "p" "IH")
(use "IH")
;; 4
(ng)
(assume "p" "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosTimesExpOddId")

;; PosToExpEq
(set-goal "all n PosToExp(2**n)=n")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosToExpEq")

;; PosToOddEq
(set-goal "all n PosToOdd(2**n)=1")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosToOddEq")

;; PosToExpTimesSOneEq
(set-goal "all p,n PosToExp(2**n*SOne p)=n")
(cases)
;; 2-4
(ind)
;; 5,6
(ng)
(use "Truth")
;; 6
(assume "n" "IH")
(ng)
(use "IH")
;; 3
(assume "p")
(ind)
;; 11,12
(ng)
(use "Truth")
;; 12
(assume "n" "IH")
(ng)
(use "IH")
;; 4
(assume "p")
(ind)
;; 17,18
(ng)
(use "Truth")
;; 19
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosToExpTimesSOneEq")

;; PosToExpTimesEq
(set-goal "all n,p(PosOdd p -> PosToExp(2**n*p)=n)")
(assume "n")
(cases)
;; 3-5
(assume "Useless")
(use "PosToExpEq")
;; 4
(assume "p" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 5
(assume "p" "Useless")
(use "PosToExpTimesSOneEq")
;; Proof finished.
;; (cdp)
(save "PosToExpTimesEq")

;; PosToOddTimesSOneEq
(set-goal "all p,n PosToOdd(2**n*SOne p)=SOne p")
(cases)
;; 2-4
(ind)
;; 5,6
(use "Truth")
;; 6
(assume "n" "IH")
(use "IH")
;; 3
(assume "p")
(ind)
;; 9,10
(use "Truth")
;; 10
(assume "n" "IH")
(ng)
(use "IH")
;; 4
(assume "p")
(ind)
;; 14,15
(use "Truth")
;; 15
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosToOddTimesOneEq")

;; PosToOddTimesEq
(set-goal "all p,n(PosOdd p -> PosToOdd(2**n*p)=p)")
(ind)
;; 2-4
(assume "n" "Useless")
(ng)
(use "PosToOddEq")
;; 3
(assume "p" "IH" "n" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "p" "IH" "n" "Useless")
(use "PosToOddTimesOneEq")
;; Proof finished.
;; (cdp)
(save "PosToOddTimesEq")

;; NatToPosDouble
(set-goal "all n(Zero<n -> SZero(NatToPos n)=NatToPos(NatDouble n))")
(assume "n" "0<n")
(simp "<-" "NatDoublePlusEq")
(simp "NatToPosPlus")
(use "SZeroPosPlus")
(use "0<n")
(use "0<n")
;; Proof finished.
;; (cdp)
(save "NatToPosDouble")

;; PosLogTwoExp
(set-goal "all n PosLog(2**n)=n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "PosLogTwoExp")
;; (add-rewrite-rule "PosLog(2**n)" "n")

;; PosLogTimes
(set-goal "all n,p PosLog(p*2**n)=PosLog p+n")
(ind)
;; 2,3
(assume "p")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 6-8
(ng #t)
(use "PosLogTwoExp")
;; 7
(assume "p")
(ng #t)
(use "IH")
;; 8
(assume "p")
(ng #t)
(simp (pf "SZero(p*2**n)+2**n=SOne p*2**n"))
(simp "IH")
(ng #t)
(use "Truth")
;; ?^15:SZero(p*2**n)+2**n=SOne p*2**n
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PosLogTimes")

;; PosLogTimes cannot be generalized to arbitrary arguments.  Counterexample:
;; (pp (nt (pt "PosLog 6"))) ;2
;; (pp (nt (pt "PosLog 7"))) ;2
;; (pp (nt (pt "PosLog 42"))) ;5

;; PosLeTwoExpToEqTwoExpTimes
(set-goal "all n,m(2**n<=2**m -> 2**m=2**n*2**(m--n))")
(assume "n" "m" "LeH")
(simp "PosExpTwoNatPlus")
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "Truth")
(simp "<-" "TwoExpNatLe")
(use "LeH")
;; Proof finished.
;; (cdp)
(save "PosLeTwoExpToEqTwoExpTimes")

;; PosLogMax
(set-goal "all p,q PosLog(p max q)=PosLog p max PosLog q")
(assume "p" "q")
(use "NatLeAntiSym")
;; 3,4
(cases (pt "p<=q"))
;; 5,6
(assume "p<=q")
(simp "PosMaxEq2")
(use "NatMaxUB2")
(use "p<=q")
;; 6
(assume "Notp<=q")
(simp "PosMaxEq1")
(use "NatMaxUB1")
(use "PosLtToLe")
(use "PosNotLeToLt")
(use "Notp<=q")
;; 4
(cases (pt "p<=q"))
;; 15,16
(assume "p<=q")
(simp "PosMaxEq2")
(use "NatMaxLUB")
(use "PosLeMonLog")
(use "p<=q")
(use "Truth")
(use "p<=q")
;; 16
(assume "Notp<=q")
(simp "PosMaxEq1")
(use "NatMaxLUB")
(use "Truth")
(use "PosLeMonLog")
(use "PosLtToLe")
(use "PosNotLeToLt")
(use "Notp<=q")
(use "PosLtToLe")
(use "PosNotLeToLt")
(use "Notp<=q")
;; Proof finished.
;; (cdp)
(save "PosLogMax")

;; NatToPosMax
(set-goal "all n,m NatToPos(n max m)=NatToPos n max NatToPos m")
(assume "n" "m")
(use "PosLeAntiSym")
;; 3,4
(cases (pt "n<=m"))
;; 5,6
(assume "n<=m")
(simp "NatMaxEq2")
(use "PosMaxUB2")
(use "n<=m")
;; 6
(assume "Notn<=m")
(simp "NatMaxEq1")
(use "PosMaxUB1")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "Notn<=m")
;; 4
(cases (pt "n<=m"))
;; 15,16
(assume "n<=m")
(simp "NatMaxEq2")
(use "PosMaxLUB")
(use "PosLeMonNatToPos")
(use "n<=m")
(use "Truth")
(use "n<=m")
;; 16
(assume "Notn<=m")
(simp "NatMaxEq1")
(use "PosMaxLUB")
(use "Truth")
(use "PosLeMonNatToPos")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "Notn<=m")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "Notn<=m")
;; Proof finished.
;; (cdp)
(save "NatToPosMax")

;; NatPosMax
(set-goal "all n,m cNatPos(n max m)=cNatPos n max cNatPos m")
(assume "n" "m")
(simp "NatPosExFree")
(simp "NatPosExFree")
(simp "NatPosExFree")
(use "NatToPosMax")
;; Proof finished.
;; (cdp)
(save "NatPosMax")
