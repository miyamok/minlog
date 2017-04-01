;; 2016-10-17.  pos.scm.  Based on the former numbers.scm.

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

;; ;; lib/list.scm needed for representing pos as list of booleans

;; (if (not (assoc "list" ALGEBRAS))
;;     (myerror "First execute (libload \"list.scm\")"))

(display "loading pos.scm ...") (newline)

;; (remove-var-name "k")

;; (remove-nat-tokens) removes all tokens added in nat.scm and from
;; DISPLAY-FUNCTIONS all items (nat proc).  The reason is that they
;; will be reintroduced here, with a different assigned procedure.

(remove-nat-tokens)

;; The functions make-numeric-term (used by the parser) and
;; is-numeric-term?, numeric-term-to-number (used by term-to-expr and
;; token-tree-to-string) take pos as default.

(set! NAT-NUMBERS #f)

(define TOKEN-AND-TYPES-TO-NAME-ALIST '())

(define (token-and-types-to-name token types)
  (let ((info (assoc token TOKEN-AND-TYPES-TO-NAME-ALIST)))
    (if info
        (let ((info1 (assoc types (cadr info))))
          (if info1
	      (cadr info1)
	      (apply myerror
		     (append (list "token-and-types-to-name" "token"
				   token "not defined for types")
			     types))))
	(myerror "token-and-types-to-name" "not an overloaded token" token))))

(define (token-and-type-to-name token type)
  (token-and-types-to-name token (list type)))

(define (add-token-and-types-to-name token types name)
  (let ((info (assoc token TOKEN-AND-TYPES-TO-NAME-ALIST)))
    (if info
	(set! TOKEN-AND-TYPES-TO-NAME-ALIST
	      (map (lambda (item)
		     (if (equal? (car item) token)
			 (list token (cons (list types name) (cadr item)))
			 item))
		   TOKEN-AND-TYPES-TO-NAME-ALIST))
	(set! TOKEN-AND-TYPES-TO-NAME-ALIST
	      (cons (list token (list (list types name)))
		    TOKEN-AND-TYPES-TO-NAME-ALIST)))))

(define (add-token-and-type-to-name token type name)
  (add-token-and-types-to-name token (list type) name))

;; 1.  Positive numbers
;; ====================

;; We want to overload operators like +,*,/,<=,<, and automatically
;; raise the type of arguments when reading.  For instance, + should
;; take its arguments, compute the lub rho of their types, raise the
;; type of both arguments to type rho, apply RhoPlus to the results.
;; Moreover, a number should be displayed at the lowest possible level.

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
(save "PosTotalVar")

;; (cdp (proof-to-soundness-proof))
;; Uses the axiom AllTotalIntroSound.

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
(use "EfqEqD")
(use "1=SZero p")
;; 7
(assume "p" "1=SOne p")
(use "EfqEqD")
(use "1=SOne p")
;; 3
(assume "p" "IH1")
(cases) ;14-16
(assume "SZero p=1")
(use "EfqEqD")
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
(use "EfqEqD")
(use "SZero p=SOne q")
;; 4
(assume "p" "IH1")
(cases) ;29-31
(assume "SOne p=1")
(use "EfqEqD")
(use "SOne p=1")
;; 30
(assume "q" "SOne p=SZero q")
(use "EfqEqD")
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
(save "PosIfTotal")

;; PosRecTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(Rec pos=>alpha)"))))
(assume "p^" "Tp")
(elim "Tp") ;3-5
(ng #t)
(assume "alpha^" "Talpha")
(strip)
(use "Talpha")
;; 4
(assume "p^1" "Tp1" "IH" "alpha^" "Talpha"
	"(pos=>alpha=>alpha)^1" "Tf1" "(pos=>alpha=>alpha)^2" "Tf2")
(ng #t)
(use "Tf1")
(use "Tp1")
(use "IH")
(use "Talpha")
(use "Tf1")
(use "Tf2")
;; 5
(assume "p^1" "Tp1" "IH" "alpha^" "Talpha"
	"(pos=>alpha=>alpha)^1" "Tf1" "(pos=>alpha=>alpha)^2" "Tf2")
(ng #t)
(use "Tf2")
(use "Tp1")
(use "IH")
(use "Talpha")
(use "Tf1")
(use "Tf2")
;; Proof finished.
(save "PosRecTotal")

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

(define (add-item-to-algebra-edge-to-embed-term-alist
         alg1-name alg2-name embed-term)
  (set! ALGEBRA-EDGE-TO-EMBED-TERM-ALIST
        (cons (list (list (make-alg alg1-name) (make-alg alg2-name))
		    embed-term)
              ALGEBRA-EDGE-TO-EMBED-TERM-ALIST)))

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

;; When later we have proved totality of PosToNat and NatToInt we need
;; to replace their item accordingly.

(define (replace-item-in-algebra-edge-to-embed-term-alist
         alg1-name alg2-name new-embed-term)
  (let* ((alg1 (make-alg alg1-name))
	 (alg2 (make-alg alg2-name))
	 (new-alist (map (lambda (item)
			   (if (equal? (car item) (list alg1 alg2))
			       (list (car item) new-embed-term)
			       item))
			 ALGEBRA-EDGE-TO-EMBED-TERM-ALIST)))
    (set! ALGEBRA-EDGE-TO-EMBED-TERM-ALIST new-alist)))

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

(define (make-term-creator token min-type-string)
  (lambda (x y)
    (let* ((type1 (term-to-type x))
	   (type2 (term-to-type y))
	   (min-type (py min-type-string))
	   (type (types-lub type1 type2 min-type))
	   (internal-name (token-and-type-to-name token type)))
      (mk-term-in-app-form
       (make-term-in-const-form (pconst-name-to-pconst internal-name))
       x y))))

(define (make-term-creator1 token min-type-string)
  (lambda (x)
    (let* ((min-type (py min-type-string))
           (type (types-lub (term-to-type x) min-type))
	   (internal-name (token-and-type-to-name token type)))
      (mk-term-in-app-form
       (make-term-in-const-form (pconst-name-to-pconst internal-name))
       x))))

(define (make-term-creator-exp token)
  (lambda (x y)
    (let* ((type1 (term-to-type x))
           (type2 (term-to-type y))
	   (internal-name (token-and-types-to-name token (list type1 type2))))
      (mk-term-in-app-form
       (make-term-in-const-form (pconst-name-to-pconst internal-name))
       x y))))

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

(define (make-display-creator name display-string token-type)
	 (lambda (x)
	   (let ((op (term-in-app-form-to-final-op x))
		 (args (term-in-app-form-to-args x)))
	     (if (and (term-in-const-form? op)
		      (string=? name (const-to-name
				      (term-in-const-form-to-const op)))
		      (= 2 (length args)))
		 (list token-type display-string
		       (term-to-token-tree (term-to-original (car args)))
		       (term-to-token-tree (term-to-original (cadr args))))
		 #f))))

(define (make-display-creator1 name display-string token-type)
	 (lambda (x)
	   (let ((op (term-in-app-form-to-final-op x))
		 (args (term-in-app-form-to-args x)))
	     (if (and (term-in-const-form? op)
		      (string=? name (const-to-name
				      (term-in-const-form-to-const op)))
		      (= 1 (length args)))
		 (list token-type display-string
		       (term-to-token-tree (term-to-original (car args))))
		 #f))))

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
(save "PosEqTotal")

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; Code discarded 2016-04-02.
;; Theorems like PosEqTotalReal PosPlusTotalReal removed.  They were
;; designed for use in proof-to-soundness-proof at theorem like
;; PosEqTotal PosPlusTotal.  But proof-to-soundness-proof should not
;; use soundness proofs for theorems of the form Pconst+Total and
;; AlgEqTotal: these proofs have terms involving Rec as content, but
;; proof-to-extracted-term assigns Pconst or identities to them.

;; (display-idpc "TotalBooleMR")

;; ;; PosEqTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "[p,q]p=q")
;; 	    (proof-to-formula (theorem-name-to-proof "PosEqTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (assume "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (use "TotalBooleTrueMR")
;; (assume "q^1" "q^10" "Useless1" "Useless2")
;; (use "TotalBooleFalseMR")
;; (assume "q^1" "q^10" "Useless1" "Useless2")
;; (use "TotalBooleFalseMR")

;; (assume "q^" "q^0" "Useless1" "IH" "q^1" "q^10" "TMRq10q1")
;; (elim "TMRq10q1")
;; (use "TotalBooleFalseMR")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless2")
;; (use "IH")
;; (use "TMRq20q2")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless2")
;; (use "TotalBooleFalseMR")

;; (assume "q^" "q^0" "Useless1" "IH" "q^1" "q^10" "TMRq10q1")
;; (elim "TMRq10q1")
;; (use "TotalBooleFalseMR")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless2")
;; (use "TotalBooleFalseMR")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless2")
;; (use "IH")
;; (use "TMRq20q2")
;; ;; Proof finished.
;; (save "PosEqTotalReal")

;; (pp (rename-variables (nt (proof-to-extracted-term "PosEqTotal"))))
;; ;; =

;; ;; Hence we are allowed to change the extracted term of PosEqTotal into
;; ;; [n,m]n=m.  Then proof-to-soundness-proof at FinAlgEqTotal looks for
;; ;; FinAlgEqTotalReal and uses it.  An error is raised if
;; ;; FinAlgEqTotalReal does not exist.

;; (pp (theorem-to-extracted-term (theorem-name-to-aconst "PosEqTotal")))
;; [p^,q^]p^ =q^

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
(save-totality)

;; (define sproof (proof-to-soundness-proof "PosSTotal"))
;; (cdp sproof)
;; (pp (rename-variables (proof-to-formula sproof)))
;; (proof-to-expr-with-formulas sproof)
;; (define nsproof (np sproof))
;; (proof-to-expr-with-formulas nsproof)
;; (pp (rename-variables (proof-to-formula nsproof)))
;; (pp (rename-variables (nf (proof-to-formula nsproof))))

;; all p^,p^0(TotalPosMR p^0 p^ -> TotalPosMR(PosS p^0)(PosS p^))

;; Code discarded 2016-04-02
;; ;; PosSTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosS")
;; 	    (proof-to-formula (theorem-name-to-proof "PosSTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (use "TotalPosSZeroMR")
;; (use "TotalPosOneMR")
;; (assume "q^" "q^0" "TMRq0q" "IH")
;; (use "TotalPosSOneMR")
;; (use "TMRq0q")
;; (assume "q^" "q^0" "TMRq0q" "IH")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IH")
;; ;; Proof finished.
;; (save "PosSTotalReal")

;; ;; (pp (theorem-to-extracted-term (theorem-name-to-aconst "PosSTotal")))
;; ;; PosS

;; ;; Both PosS and [p^0](Rec pos=>pos)p^0 2([p1,p2]SOne p1)([p1]SZero)
;; ;; are realizers for the formula of the theorem PosSTotal.
;; ;; theorem-to-extracted-term picks PosS, whereas extraction from the
;; ;; proof of PosSTotal gives the latter term with Rec.

;; (proof-to-expr-with-formulas "PosSTotalReal")
;; ;; simpler than et(nsproof).

;; (pp (rename-variables
;;      (proof-to-formula (theorem-name-to-proof "PosSTotalReal"))))
;; ;; allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(PosS p^0)(PosS p^))
;; ;; Also simpler than the formula of sproof.

;; ;; Correctness of PosS as realizer for PosSTotal is verified by
;; ;; PosSTotalReal.  Therefore proof-to-soundness-proof at theorem
;; ;; PosSTotal should use the theorem PosSTotalReal, and similarly for
;; ;; other pconsts.

;; (pp (rename-variables (proof-to-extracted-term "PosSTotal")))

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
(save-totality)

;; Code discarded 2016-04-02
;; ;; PosPredTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosPred")
;; 	    (proof-to-formula (theorem-name-to-proof "PosPredTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (use "TotalPosOneMR")

;; (assume "q^" "q^0" "TMRq0q" "IH")
;; (elim "TMRq0q")
;; (use "TotalPosOneMR")
;; (assume "q^2" "q^20" "TMRq20q2" "IH2")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "IH2")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "TotalPosSZeroMR")
;; (use "TMRq20q2")

;; (assume "q^" "q^0" "TMRq0q" "IH")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "TMRq0q")
;; ;; Proof finished.
;; (save "PosPredTotalReal")

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
(save-totality)

(replace-item-in-algebra-edge-to-embed-term-alist
 "pos" "nat"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
	 (make-term-in-const-form
	  (pconst-name-to-pconst "PosToNat"))
	 (make-term-in-var-form var)))))

;; PosToNatDefSZero is obsolete.  Use PosToNat1CompRule instead.
;; (set-goal "all p PosToNat(SZero p)=NatDouble(PosToNat p)")
;; (assume "p")
;; (use "Truth")
;; ;; Proof finished.
;; (save "PosToNatDefSZero")

;; PosToNatDefSOne is obsolete.  Use PosToNat2CompRule instead.
;; (set-goal "all p PosToNat(SOne p)=Succ(PosToNat(SZero p))")
;; (assume "p")
;; (use "Truth")
;; ;; Proof finished.
;; (save "PosToNatDefSOne")

;; We define the inverse NatToPos of PosToNat , using GRec

(add-program-constant "NatToPosStep" (py "nat=>(nat=>pos)=>pos"))

;; Rules for NatToPosStep

(add-computation-rules
 "NatToPosStep n(nat=>pos)"
 "[if (NatEven n)
      (SZero((nat=>pos)(NatHalf n)))
      [if (n=Succ Zero) One (SOne((nat=>pos)(NatHalf n)))]]")

;; NatToPosStepTotal
(set-totality-goal "NatToPosStep")
(assume "n^" "Tn" "(nat=>pos)^" "Th")
(ng #t)
(use "BooleIfTotal")
(use "NatEvenTotal")
(use "Tn")
(use "TotalPosSZero")
(use "Th")
(use "NatHalfTotal")
(use "Tn")
(use "BooleIfTotal")
(use "NatEqTotal")
(use "Tn")
(use "TotalNatSucc")
(use "TotalNatZero")
(use "TotalPosOne")
(use "TotalPosSOne")
(use "Th")
(use "NatHalfTotal")
(use "Tn")
;; Proof finished.
(save-totality)

(add-program-constant "NatToPos" (py "nat=>pos"))

;; Rules for NatToPos

(add-computation-rules
 "NatToPos n" "(GRec nat pos)([n]n)n NatToPosStep")

;; NatToPosTotal
(set-totality-goal  "NatToPos")
(use "AllTotalElim")
(assume "n")
(ng #t)
(use "BooleIfTotal")
(use "NatEvenTotal")
(use "NatTotalVar")
(use "TotalPosSZero")
(use "PosTotalVar")
(use "BooleIfTotal")
(use "NatEqTotal")
(use "NatTotalVar")
(use "TotalNatSucc")
(use "TotalNatZero")
(use "TotalPosOne")
(use "TotalPosSOne")
(use "PosTotalVar")
;; Proof finished.
(save-totality)

;; NatToPosDef
(set-goal "all n NatToPos n=(GRec nat pos)([n]n)n NatToPosStep")
(assume "n")
(use "Truth")
;; Proof finished
(save "NatToPosDef")

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
(save-totality)

;; Code discarded 2016-04-02
;; ;; PosPlusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosPlus")
;; 	    (proof-to-formula (theorem-name-to-proof "PosPlusTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (assume "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (use "TotalPosSZeroMR")
;; (use "TotalPosOneMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IH")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "TMRq10q1")
;; (assume "q^1" "q^10" "TMRq10q1" "IH")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "PosSTotalReal")
;; (use "TMRq10q1")

;; ;; ?_4:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0+p^0)(pos^ +p^)) ->
;; ;;      allnc p^,p^0(
;; ;;       TotalPosMR p^0 p^ --> TotalPosMR(SZero pos^0+p^0)(SZero pos^ +p^)))
;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "TMRp10p1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0+p^0)(pos^ +p^)) ->
;; ;;      allnc p^,p^0(
;; ;;       TotalPosMR p^0 p^ --> TotalPosMR(SOne pos^0+p^0)(SOne pos^ +p^)))

;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "PosSTotalReal")
;; (use "TMRp10p1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "PosSTotalReal")
;; (use "IHp1")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "PosPlusTotalReal")

;; NatLt0Pos
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
(save "NatLt0Pos")

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
(add-rewrite-rule "PosS(PosPred(SZero p))" "SZero p")

(set-goal "all p One+p=PosS p")
(cases)
(auto)
;; Proof finished
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
(save "GRecDef")

;; NatToPosEqSZeroNatToPosHalf
(set-goal "all n(Zero<n -> NatEven n ->
                   NatToPos n=SZero(NatToPos(NatHalf n)))")
(assume "n" "0<n" "En")
(ng #t)
(simp "En")
(ng #t)
(assert "NatHalf n<n")
 (use "NatHalfLt")
 (use "0<n")
(assume "NatHalf n<n")
(simp "NatHalf n<n")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NatToPosEqSZeroNatToPosHalf")

;; NatToPosEqSOneNatToPosHalf
(set-goal "all n(Zero<n -> (NatEven n -> F) -> (n=Succ Zero -> F) ->
                 NatToPos n=SOne(NatToPos(NatHalf n)))")
(assume "n" "0<n" "NatEven n -> F" "n=Succ Zero -> F")
(ng #t)
(simp "NatEven n -> F")
(ng #t)
(simp "n=Succ Zero -> F")
(ng #t)
(assert "NatHalf n<n")
 (use "NatHalfLt")
 (use "0<n")
(assume "NatHalf n<n")
(simp "NatHalf n<n")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NatToPosEqSOneNatToPosHalf")

;; NatHalfSuccEven
(set-goal "all n(NatEven n -> NatHalf(Succ n)=NatHalf n)")
(use "CVIndPvar")
(assume "Absurd")
(strip)
(use "EfqAtom")
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
(save "NatHalfSuccEven")

;; PosToNatToPosId
(set-goal "all n(Zero<n -> PosToNat(NatToPos n)=n)")
(use "CVIndPvar")
(assume "Absurd")
(strip)
(use "EfqAtom")
(use "Absurd")
(assume "n" "Prog" "0<n")
(cases (pt "NatEven n"))
;; 8,9
(assume "En")
(assert "NatToPos n=SZero(NatToPos(NatHalf n))")
 (use "NatToPosEqSZeroNatToPosHalf")
 (use "0<n")
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
;; 9
(assume "NatEven n -> F")
(cases (pt "n=Succ Zero"))
(assume "n=1")
(simp "n=1")
(ng #t)
(simp "NatEven n -> F")
(ng #t)
(simp "n=1")
(use "Truth")
(assume "n=1 -> F")
(assert "NatToPos n=SOne(NatToPos(NatHalf n))")
 (use "NatToPosEqSOneNatToPosHalf")
 (use "0<n")
 (use "NatEven n -> F")
 (use "n=1 -> F")
(assume "NatToPos n=SOne(NatToPos(NatHalf n))")
(simp "NatToPos n=SOne(NatToPos(NatHalf n))")
(simp "PosToNat2CompRule")
(cases (pt "n"))
(assume "n=0")
(use "EfqAtom")
(simphyp-with-to "NatEven n -> F" "n=0" "Absurd")
(use "Absurd")
(use "Truth")
(assume "n1" "n=Succ n1")
(simp "PosToNat1CompRule")
(assert "NatEven n1")
(use "NatOddSuccToEven")
(simp "<-" "n=Succ n1")
(use "NatEven n -> F")
(assume "En1")
(simp "NatHalfSuccEven")
(assert "PosToNat(SZero(NatToPos(NatHalf n1)))=n1")
 (simp "PosToNat1CompRule")
 (simp "Prog")
 (use "NatDoubleHalfEven")
 (use "En1")
 (cases (pt "n1"))
 (assume "n1=0")
 (use "n=1 -> F")
 (simp "n=Succ n1")
 (use "n1=0")
 (cases)
 (ng #t)
 (assume "n1=1")
 (simphyp-with-to "En1" "n1=1" "Absurd")
 (use "Absurd")
 (ng #t)
 (strip)
 (use "Truth")
 (simp "n=Succ n1")
 (use "NatHalfLtSucc")
(assume "PosToNat(SZero(NatToPos(NatHalf n1)))=n1")
(simp "Prog")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "En1")
(use "NatLtZeroHalfEven")
(cases (pt "n1"))
(assume "n1=0")
(use "n=1 -> F")
(simp "n=Succ n1")
(use "n1=0")
(strip)
(use "Truth")
(use "En1")
(simp "n=Succ n1")
(use "NatHalfLtSucc")
(use "En1")
;; Proof finished.
(save "PosToNatToPosId")

;; NatToPosToNatId
(set-goal "all p NatToPos(PosToNat p)=p")
(ind) 
;; 2-4
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH")
(ng #t)
(simp "NatEvenDouble")
(ng #t)
(assert "Zero<NatDouble(PosToNat p)")
 (ind (pt "p"))
 (use "Truth")
 (assume "p1" "IH1")
 (ng #t)
 (use "NatLt0Double")
 (use "IH1")
 (assume "p1" "IH1")
 (ng #t)
 (use "Truth")
(assume "Zero<NatDouble(PosToNat p)")
(assert "NatHalf(NatDouble(PosToNat p))<NatDouble(PosToNat p)")
 (use "NatHalfLt")
 (use "Zero<NatDouble(PosToNat p)")
(assume "NatHalf(NatDouble(PosToNat p))<NatDouble(PosToNat p)")
(simp "NatHalf(NatDouble(PosToNat p))<NatDouble(PosToNat p)")
(simp "NatHalfDouble")
(simp "IH")
(use "Truth")
;; 4
(assume "p" "IH")
(ng #t)
(assert "NatEven(Succ(NatDouble(PosToNat p))) -> F")
 (use "NatEvenSucc")
 (use "NatEvenDouble")
(assume "NatEven(Succ(NatDouble(PosToNat p))) -> F")
(simp "NatEven(Succ(NatDouble(PosToNat p))) -> F")
(ng #t)
(assert "Zero<NatDouble(PosToNat p)")
 (use "NatLt0Double")
 (use "NatLt0Pos")
(assume "Zero<NatDouble(PosToNat p)")
(assert "NatDouble(PosToNat p)=Zero -> F")
 (assume "NatDouble(PosToNat p)=Zero")
 (simphyp-with-to "Zero<NatDouble(PosToNat p)" "NatDouble(PosToNat p)=Zero"
		  "Absurd")
 (use "Absurd")
(assume "NatDouble(PosToNat p)=Zero -> F")
(simp "NatDouble(PosToNat p)=Zero -> F")
(ng #t)
(assert "NatHalf(Succ(NatDouble(PosToNat p)))<Succ(NatDouble(PosToNat p))")
 (use "NatHalfLt")
 (use "Truth")
(assume "NatHalf(Succ(NatDouble(PosToNat p)))<Succ(NatDouble(PosToNat p))")
(simp "NatHalf(Succ(NatDouble(PosToNat p)))<Succ(NatDouble(PosToNat p))")
(simp "NatHalfSuccDouble")
(simp "IH")
(use "Truth")
;; Proof finished.
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
(save "PosToNatInj")

;; SuccPosS
(set-goal "all n(Zero<n -> NatToPos(Succ n)=PosS(NatToPos n))")
(assert "all n(Zero<n -> Succ n=PosToNat(PosS(NatToPos n)))")
(use "CVIndPvar")
(assume "Absurd")
(strip)
(use "EfqAtom")
(use "Absurd")
(assume "n" "Prog" "0<n")
(cases (pt "NatEven n")) ;10,11
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
(use "0<n")
;; 11
(assume "On")
(cases (pt "n=Succ Zero"))
(assume "n=1")
(simp "n=1")
;; simp normalizes the goal, which we do not want.  Why?  Ok if order
;; in simp-with-intern is changed: consider normalized items last.
(ng #t)
(use "Truth")
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
(use "n=/=1")
(use "On")
(use "0<n")
;; Assertion proved
(assume "SuccPosSAux" "n" "0<n")
(simp "SuccPosSAux")
(simp "NatToPosToNatId")
(use "Truth")
(use "0<n")
;; Proof finished.
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
(use "NatLt0Pos")
;; Proof finished.
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
(save "PosPlusAssoc")
(add-rewrite-rule "p+(q+r)" "p+q+r")

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
(save-totality)

;; Code discarded 2016-04-02
;; ;; PosTimesTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosTimes")
;; 	    (proof-to-formula (theorem-name-to-proof "PosTimesTotal")))))
;; (assume "p^" "p^0" "TMRp0p" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (use "TMRp0p")
;; (assume "q^1" "q^10" "Useless" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IHq1")
;; (assume "q^1" "q^10" "Useless" "IHq1")
;; (ng #t)
;; (use "PosPlusTotalReal")
;; (use "TotalPosSZeroMR")
;; (use "IHq1")
;; (use "TMRp0p")
;; ;; Proof finished.
;; (save "PosTimesTotalReal")

(set-goal "all p One*p=p")
(ind)
(auto)
;; Proof finished.
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
(add-rewrite-rule "SZero p*q" "SZero(p*q)")

;; We prove that NatToPos is an isomorphism w.r.t. *

;; NatDoublePlus
(set-goal "all n,m NatDouble(n+m)=NatDouble n+NatDouble m")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatDoublePlus")

;; NatDoublePlusEq
(set-goal "all n n+n=NatDouble n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatDoublePlusEq")

;; NatTimesDouble
(set-goal "all n,m NatDouble n*NatDouble m=NatDouble(NatDouble(n*m))")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(simp "IH")
(assert "NatDouble(n*m+n)=NatDouble(n*m)+NatDouble n")
 (use "NatDoublePlus")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "NatDouble(NatDouble(n*m)+NatDouble n)=
         NatDouble(NatDouble(n*m))+NatDouble(NatDouble(n))")
 (use "NatDoublePlus")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "NatDouble(NatDouble n)=NatDouble n+NatDouble n")
 (simp "NatDoublePlusEq")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(use "Truth")
;; Proof finished.
(save "NatTimesDouble")

;; NatDoubleTimes2
(set-goal "all n,m NatDouble(n*m)=n*NatDouble m")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(simp "NatDoublePlus")
(simp "IH")
(assert "NatDouble n=n+n")
 (simp "NatDoublePlusEq")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(use "Truth")
;; Proof finished.
(save "NatDoubleTimes2")

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
(save-totality)

;; PosExpOne
(set-goal "all n 1**n=1")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
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
(save "PosLeTotal")

;; Code discarded 2016-04-02
;; ;; PosLtPosLeTotalRealLemma
;; (set-goal "allnc p^,p^0(
;;  TotalPosMR p^0 p^ -->
;;  allnc q^,q^0(
;;   TotalPosMR q^0 q^ -->
;;   TotalBooleMR(p^0<q^0)(p^ <q^) andu TotalBooleMR(p^0<=q^0)(p^ <=q^)))")
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (assume "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (split)
;; (use "TotalBooleFalseMR")
;; (use "TotalBooleTrueMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (split)
;; (use "TotalBooleTrueMR")
;; (use "TotalBooleTrueMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (split)
;; (use "TotalBooleTrueMR")
;; (use "TotalBooleTrueMR")

;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (split)
;; (use "TotalBooleFalseMR")
;; (use "TotalBooleFalseMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "IHp1")
;; (use "TMRq10q1")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (split)
;; (use "IHp1")
;; (use "TMRq10q1")
;; (use "IHp1")
;; (use "TMRq10q1")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc q^,q^0(
;; ;;       TotalPosMR q^0 q^ -->
;; ;;       TotalBooleMR(pos^0<q^0)(pos^ <q^) andu
;; ;;       TotalBooleMR(pos^0<=q^0)(pos^ <=q^)) ->
;; ;;      allnc q^,q^0(
;; ;;       TotalPosMR q^0 q^ -->
;; ;;       TotalBooleMR(SOne pos^0<q^0)(SOne pos^ <q^) andu
;; ;;       TotalBooleMR(SOne pos^0<=q^0)(SOne pos^ <=q^)))
;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (split)
;; (use "TotalBooleFalseMR")
;; (use "TotalBooleFalseMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (split)
;; (use "IHp1")
;; (use "TMRq10q1")
;; (use "IHp1")
;; (use "TMRq10q1")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "IHp1")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "PosLtPosLeTotalRealLemma")

;; ;; (display-pconst "PosLt")
;; ;; (display-pconst "PosLe")

;; ;; PosLtTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosLt")
;; 	    (proof-to-formula (theorem-name-to-proof "PosLtTotal")))))
;; (assume "p^" "p^0" "TMRp0p" "q^" "q^0" "TMRq0q")
;; (use "PosLtPosLeTotalRealLemma")
;; (use "TMRp0p")
;; (use "TMRq0q")
;; ;; Proof finished.
;; (save "PosLtTotalReal")

;; ;; PosLeTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosLe")
;; 	    (proof-to-formula (theorem-name-to-proof "PosLeTotal")))))
;; (assume "p^" "p^0" "TMRp0p" "q^" "q^0" "TMRq0q")
;; (use "PosLtPosLeTotalRealLemma")
;; (use "TMRp0p")
;; (use "TMRq0q")
;; ;; Proof finished.
;; (save "PosLeTotalReal")

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
(save "PosLtToLe")

;; PosLTrans
(set-goal "all p,q,r((p<q -> q<=r -> p<r)
                    &(p<=q -> q<r -> p<r)
                    &(p<=q -> q<=r -> p<=r))")
(ind) ;2-4
(cases) ;5-7
(assume "r")
(ng #t)
(split)
(use "Efq")
(split)
(assume "Useless" "1<p3")
(use "1<p3")
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
(use "Efq")
(split)
(use "Efq")
(use "Efq")
;; 80
(assume "q")
(cases) ;89-91
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 90
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(use "IH1")
;; 91
(assume "r")
(ng #t)
(split)
(assume "p1<p2" "p2<=p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "p2<=p3")
(split)
(use "IH1")
(use "IH1")
;; 81
(assume "q")
(cases) ;115-117
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 116
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(assume "p1<=p2" "p2<p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'right 'left "p1<=p2" "p2<p3")
;; 117
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
(cases) ;143-145
(assume "q")
(ng #t)
(split)
(use "Efq")
(split)
(use "Efq")
(use "Efq")
;; 144
(assume "q")
(cases) ;153-155
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 154
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
;; 155
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(assume "p1<p2" "p2<=p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "p2<=p3")
;; 145
(assume "q")
(cases) ;182-184
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 183
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
;; 184
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(use "IH1")
;; Proof finished.
(save "PosLTrans")

;; Using this and PosLtToLe we can easily derive PosLeLtTrans
;; PosLtLeTrans PosLeTrans PosLtTrans.

;; PosLtLeTrans
(set-goal "all p,q,r(p<q -> q<=r -> p<r)")
(assume "p" "q" "r")
(use "PosLTrans")
;; Proof finished.
(save "PosLtLeTrans")

;; PosLeLtTrans
(set-goal "all p,q,r(p<=q -> q<r -> p<r)")
(assume "p" "q" "r")
(use "PosLTrans")
;; Proof finished.
(save "PosLeLtTrans")

;; PosLeTrans
(set-goal "all p,q,r(p<=q -> q<=r -> p<=r)")
(assume "p" "q" "r")
(use "PosLTrans")
;; Proof finished.
(save "PosLeTrans")

;; PosLtTrans
(set-goal "all p,q,r(p<q -> q<r -> p<r)")
(assume "p" "q" "r" "p1<p2")
(use "PosLeLtTrans")
(use "PosLtToLe")
(use "p1<p2")
;; Proof finished.
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
(add-rewrite-rule "p<p" "False")

(set-goal "all p p<=p")
(ind)
(use "Truth")
(assume "p" "IH")
(use "IH")
(assume "p" "IH")
(use "IH")
;; Proof finished.
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
(add-rewrite-rule "p<p+q" "True")

(set-goal "all p,q p<=q+p")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "p<=q+p" "True")

(set-goal "all p,q p<q+p")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "p<q+p" "True")

(set-goal "all p (PosS p<=1)=False")
(cases)
(use "Truth")
(strip)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
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
(add-rewrite-rule "p+q<=p" "False")

(set-goal "all p,q (p+q<=q)=False")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
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
(add-rewrite-rule "p+q<p" "False")

(set-goal "all p,q (p+q<q)=False")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
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
(save "PosLtMonPred")

;; PosNotLeToLt and PosNotLtToLe are proved using the isomorphic
;; embedding PosToNat of pos into nat.

;; We prove that NatToPos is an isomorphism w.r.t. <= and <.  Main
;; idea: Translate the computation rules for PosLe, PosLt into
;; equational lemmas for NatLe, NatLt with NatDouble nat for SZero pos
;; and Succ(NatDouble nat) for SOne pos.

;; PosToNatLeLt
(set-goal "all p,q((PosToNat p<=PosToNat q)=(p<=q) &
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
 (use "NatLt0Pos")
(assume "Succ Zero<=NatDouble(PosToNat p)")
(simp "Succ Zero<=NatDouble(PosToNat p)")
(use "Truth")
(assert "Succ Zero<NatDouble(PosToNat p)")
 (use "NatLtOneDouble")
 (use "NatLt0Pos")
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
 (use "NatLt0Pos")
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
 (use "NatLt0Pos")
(assume "NatDouble(PosToNat p)<=Succ Zero -> F")
(simp "NatDouble(PosToNat p)<=Succ Zero -> F")
(use "Truth")
(assert "NatDouble(PosToNat p)<Succ Zero -> F")
 (use "NatLtDoubleOne")
 (use "NatLt0Pos")
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
  (use "NatLt0Pos")
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
(save "NatToPosLe")

;; PosToNatLt
(set-goal "all p,q (PosToNat p<PosToNat q)=(p<q)")
(assume "p" "q")
(use "PosToNatLeLt")
;; Proof finished.
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
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
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
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
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
(use "NatLt0Pos")
(simp "<-" "PosToNatPlus")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
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
(use "NatLt0Pos")
(simp "<-" "PosToNatTimes")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
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
(save "PosLeLtMonTimes")

(set-goal "all p,q,r (p*r<=q*r)=(p<=q)")
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
(add-rewrite-rule "p*r<=q*r" "p<=q")

;; PosTimesInj
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
(save "PosTimesInj")

;; PosTimesInjLeft
(set-goal "all p,q,r(p*r=q*r -> p=q)")
(assume "p" "q" "r" "pr=qr")
(use "PosTimesInj" (pt "r"))
(simp "PosTimesComm")
(simp "pr=qr")
(use "PosTimesComm")
;; Proof finished.
(save "PosTimesInjLeft")

;; PosLtMonTimesInv
(set-goal  "all p,q,r(p*q<p*r -> q<r)")
(assume "p" "q" "r" "pq<pr")
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
;; Proof finished.
(save "PosLtMonTimesInv")

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
(save "SuccPosPred")

;; PredPosPred
(set-goal "all p(1<p -> Pred(PosToNat p)=PosToNat(PosPred p))")
(assume "p" "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
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
(save "NatDoubleSZero")

;; Now we can prove that PosToNat is an isomorphism w.r.t. -

;; PosToNatMinus
(set-goal "all p,q(q<p -> PosToNat(p--q)=PosToNat p--PosToNat q)")
(ind)
;; 2-4
(assume "q")
(ng #t)
(use "Efq")
;; 3
(assume "p" "IH1")
(ind)
;; 8-10
(ng)
;; ?_11:T -> PosToNat(PosPred(SZero p))=Pred(NatDouble(PosToNat p))
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
(simp "NatDoubleLt")
(simp "PosToNatLt")
(use "q<p")
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
(save "PosToNatMinus")

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
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
(add-rewrite-rule "p+q--q" "p")

(set-goal "all p,q q+p--q=p")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
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
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
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
(save "PosPlusMinus")

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
(save "PosMinusPlus")

;; PosMinusPlusEq
(set-goal "all p,q(q<p -> p--q+q=p)")
(assume "p" "q" "q<p")
(simp "PosMinusPlus")
(use "Truth")
(use "q<p")
;; Proof finished.
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
(save "PosTimesMinusDistrLeft")

;; Code discarded 2016-04-02
;; ;; BooleIfTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (proof-to-extracted-term "BooleIfTotal")
;; 	    (proof-to-formula boole-if-total-proof))))
;; (assume "boole^" "boole^0" "TMRb0b")
;; (ng #t)
;; (elim "TMRb0b")
;; (ng #t)
;; (assume "alpha^1" "alpha^2" "alpha^10" "TMRa10a1" "alpha^20" "Useless")
;; (use "TMRa10a1")
;; (ng #t)
;; (assume "alpha^1" "alpha^2" "alpha^10" "Useless" "alpha^20" "TMRa20a2")
;; (use  "TMRa20a2")
;; ;; Proof finished.
;; (save "BooleIfTotalReal")

;; ;; PosMinusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosMinus")
;; 	    (proof-to-formula (theorem-name-to-proof "PosMinusTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (assume "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (use "TotalPosOneMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IH")
;; (ng #t)
;; (use "TotalPosOneMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IH")
;; (ng #t)

;; (use "TotalPosOneMR")
;; ;; ?_4:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0--p^0)(pos^ --p^)) ->
;; ;;      allnc p^,p^0(
;; ;;       TotalPosMR p^0 p^ --> TotalPosMR(SZero pos^0--p^0)(SZero pos^ --p^)))
;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (ng #t)
;; (use "PosPredTotalReal")
;; (use "TotalPosSZeroMR")
;; (use "TMRp10p1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "PosPredTotalReal")
;; (use "TotalPosSZeroMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0--p^0)(pos^ --p^)) ->
;; ;;      allnc p^,p^0(
;; ;;       TotalPosMR p^0 p^ --> TotalPosMR(SOne pos^0--p^0)(SOne pos^ --p^)))

;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "TMRp10p1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp10p1")
;; (use "TMRq10q1")
;; (use "TotalPosOneMR")
;; (use "TotalPosSOneMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IHp1")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "PosMinusTotalReal")

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
(save "PosMaxEq1")

;; PosMaxEq2
(set-goal "all p,q(p<=q -> p max q=q)")
(assume "p" "q")
(simp "PosMaxComm")
(use "PosMaxEq1")
;; Proof finished.
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
(save "PosToNatMax")

;; PosMaxUB1
(set-goal "all p,q p<=p max q")
(assume "p" "q")
(assert "NatToPos(PosToNat p)<=NatToPos(PosToNat(p max q))")
 (simp "NatToPosLe")
 (simp "PosToNatMax")
 (use "NatMaxUB1")
 (use "NatLt0Pos")
 (use "NatLt0Pos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "p<=p max q")
(use "p<=p max q")
;; Proof finished.
(save "PosMaxUB1")

;; PosMaxUB2
(set-goal "all p,q q<=p max q")
(assume "p" "q")
(simp "PosMaxComm")
(use "PosMaxUB1")
;; Proof finished.
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
 (use "NatLt0Pos")
 (use "NatLt0Pos")
 (use "NatLt0Pos")
 (use "NatLt0Pos")
 (use "NatLt0Pos")
 (use "NatLt0Pos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "p<=r -> q<=r -> p max q<=r")
(use "p<=r -> q<=r -> p max q<=r")
;; Proof finished.
(save "PosMaxLUB")

;; Rules for PosMin

(add-computation-rules
 "One min p" "One"
 "SZero p min One" "One"
 "SZero p min SZero q" "SZero(p min q)"
 "SZero p min SOne q" "[if (p<=q) (SZero p) (SOne q)]"
 "SOne p min One" "One"
 "SOne p min SZero q" "[if (p<=q) (SZero q) (SOne p)]"
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
(use "Tp1")
(use "Tq1")
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
(save-totality)

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
(save-totality)

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
(save-totality)

;; (pp (nt (pt "PosLog 8")))
;; Succ(Succ(Succ Zero))

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
(save "PosLogZero")

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
(save "PosLtExpTwoSuccLog")

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
(save "PosExpTwoNatPlus")

;; PosExpTwoPosPlus
(set-goal "all p,q 2**p*2**q=2**(p+q)")
(assume "p" "q")
(simp "PosToNatPlus")
(use "PosExpTwoNatPlus")
;; Proof finished.
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
(use "EfqAtom")
(use "Absurd")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
(save "PosLeMonPosExp")

;; (search-about "Pos" "Max")
