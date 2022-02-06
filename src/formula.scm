;; 2022-02-06.  formula.scm
;; 7. Formulas and comprehension terms
;; ===================================

;; 7-1. Constructors and accessors
;; ===============================

;; A prime formula has the form (predicate a r1 ... rn) with a
;; predicate variable or constant a and terms r1 ... rn.  Formulas are
;; built from prime formulas by

;; - (imp formula1 formula2) implication
;; - (all x formula) all quantification
;; - (impnc formula1 formula2) implication without computational content
;; - (allnc x formula) all quantification without computational content

;; - (exca (x1 ... xn) formula)
;;   classical existential quantification (arithmetical version)
;;   (excl (x1 ... xn) formula)
;; - classical existential quantification (logical version)
;; - (tensor formula1 formula2) for proper folding-unfolding

;; We allow that quantified variables are formed without ^, i.e.,
;; range over total objects only.

;; Leibniz equality, the existential quantifier, conjunction and
;; disjunction are provided by means of inductively defined predicates.
;; However, for efficiency reasons we keep built-in versions:

;; - (and formula1 formula2) conjunction
;; - (ex x formula) existential quantification

;; Temporarily we also allow prime formulas of the form (atom r) with a
;; term r of type boole.  They can be replaced by Leibniz equality of
;; the boolean constant True with r, written True eqd r.

(define (make-atomic-formula term) (list 'atom term))

(define atom-form-to-kernel cadr)

(define (atom-form? x)
  (and (list? x) (= 2 (length x)) (eq? 'atom (car x))))

(define (make-predicate-formula predicate . terms)
  (let* ((arity (predicate-to-arity predicate))
	 (types1 (arity-to-types arity))
	 (types2 (map term-to-type terms)))
    (if (not (= (length types1) (length types2)))
	(apply myerror
	       "make-predicate-formula" "types of arity"
	       (append types1
		       (list "should be of the same length as types of terms")
		       terms)))
    (if (equal? types1 types2)
	(cons 'predicate (cons predicate terms))
	(let ((coerce-ops (map types-to-coercion types2 types1)))
	  (cons 'predicate (cons predicate (map (lambda (x y) (x y))
						coerce-ops terms)))))))

(define predicate-form-to-predicate cadr)
(define predicate-form-to-args cddr)

(define (predicate-form? x)
  (and (pair? x) (eq? 'predicate (car x))))

(define (make-=-term term1 term2)
  (let* ((type1 (term-to-type term1))
         (type2 (term-to-type term2))
         (=-term
          (if (equal? type1 type2)
	      (make-term-in-const-form
	       (finalg-to-=-const type1)) ;includes check for finalg
	      (myerror "make-=-term" "equal types expected" type1 type2))))
    (mk-term-in-app-form =-term term1 term2)))

(define (make-= term1 term2)
  (let ((type1 (term-to-type term1))
	(type2 (term-to-type term2)))
    (if (not (equal? type1 type2))
	(myerror "make-=" "equal types expected" type1 type2))
    (if (finalg? type1)
	(make-atomic-formula
	 (mk-term-in-app-form
	  (make-term-in-const-form
	   (finalg-to-=-const type1)) ;includes check for finalg
	  term1 term2))
	(make-eqd term1 term2))))

(define (make-e term)
  (let* ((type (term-to-type term))
         (e-term (make-term-in-const-form
		  (finalg-to-e-const type)))) ;includes check for finalg
    (make-atomic-formula (mk-term-in-app-form e-term term))))

(define (make-total term)
  (let* ((type (term-to-type term))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (total-predconst (make-predconst (make-arity tvar)
					  (make-subst tvar type)
					  -1 "Total")))
    (make-predicate-formula total-predconst term)))

(define (make-totalnc term)
  (let* ((type (term-to-type term))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (totalnc-predconst (make-predconst (make-arity tvar)
					    (make-subst tvar type)
					    -1 "TotalNc")))
    (make-predicate-formula totalnc-predconst term)))

(define (make-cototal term)
  (let* ((type (term-to-type term))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (cototal-predconst (make-predconst (make-arity tvar)
					    (make-subst tvar type)
					    -1 "CoTotal")))
    (make-predicate-formula cototal-predconst term)))

(define (make-cototalnc term)
  (let* ((type (term-to-type term))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (cototalnc-predconst (make-predconst (make-arity tvar)
					      (make-subst tvar type)
					      -1 "CoTotalNc")))
    (make-predicate-formula cototalnc-predconst term)))

(define (make-totalmr term real)
  (let* ((type (term-to-type term))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (totalmr-predconst (make-predconst (make-arity tvar tvar)
					    (make-subst tvar type)
					    -1 "TotalMR")))
    (make-predicate-formula totalmr-predconst term real)))

(define (make-cototalmr term real)
  (let* ((type (term-to-type term))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (cototalMR-predconst (make-predconst (make-arity tvar tvar)
					      (make-subst tvar type)
					      -1 "CoTotalMR")))
    (make-predicate-formula cototalMR-predconst term real)))

(define (make-se term)
  (let* ((type (term-to-type term))
         (se-term (make-term-in-const-form
                   (sfinalg-to-se-const type)))) ;includes check for sfinalg
    (make-atomic-formula (mk-term-in-app-form se-term term))))

(define (make-stotal-or-se term)
  (let ((type (term-to-type term)))
    (if
     (sfinalg? type)
     (make-atomic-formula
      (mk-term-in-app-form
       (make-term-in-const-form
	(make-const (se-at type)
		    "SE" 'fixed-rules
		    (make-arrow type (make-alg "boole")) empty-subst
		    1 'prefix-op))
       term))
     (make-stotal term))))

(define (make-stotal-or-se-or-e term)
  (let ((type (term-to-type term)))
    (cond
     ((finalg? type)
      (make-atomic-formula
       (mk-term-in-app-form
	(make-term-in-const-form
	 (make-const (e-at type)
		     "E" 'fixed-rules
		     (make-arrow type (make-alg "boole")) empty-subst
		     1 'prefix-op))
	term)))
     ((sfinalg? type)
      (make-atomic-formula
       (mk-term-in-app-form
	(make-term-in-const-form
	 (make-const (se-at type)
		     "SE" 'fixed-rules
		     (make-arrow type (make-alg "boole")) empty-subst
		     1 'prefix-op))
	term)))
     (else (make-stotal term)))))

(define (make-eqp term1 term2)
  (let* ((type1 (term-to-type term1))
	 (type2 (term-to-type term2))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (eqp-predconst
	  (if (equal? type1 type2)
	      (make-predconst (make-arity tvar tvar)
			      (make-subst tvar type1)
			      -1 "EqP")
	      (myerror "make-eqp" "equal types expected" type1 type2))))
    (make-predicate-formula eqp-predconst term1 term2)))

(define (make-eqpnc term1 term2)
  (let* ((type1 (term-to-type term1))
	 (type2 (term-to-type term2))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (eqp-predconst
	  (if (equal? type1 type2)
	      (make-predconst (make-arity tvar tvar)
			      (make-subst tvar type1)
			      -1 "EqPNc")
	      (myerror "make-eqpnc" "equal types expected" type1 type2))))
    (make-predicate-formula eqp-predconst term1 term2)))

(define (make-coeqp term1 term2)
  (let* ((type1 (term-to-type term1))
	 (type2 (term-to-type term2))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (coeqp-predconst
	  (if (equal? type1 type2)
	      (make-predconst (make-arity tvar tvar)
			      (make-subst tvar type1)
			      -1 "CoEqP")
	      (myerror "make-coeqp" "equal types expected" type1 type2))))
    (make-predicate-formula coeqp-predconst term1 term2)))

(define (make-coeqpnc term1 term2)
  (let* ((type1 (term-to-type term1))
	 (type2 (term-to-type term2))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (coeqp-predconst
	  (if (equal? type1 type2)
	      (make-predconst (make-arity tvar tvar)
			      (make-subst tvar type1)
			      -1 "CoEqPNc")
	      (myerror "make-coeqpnc" "equal types expected" type1 type2))))
    (make-predicate-formula coeqp-predconst term1 term2)))

(define (make-eqpmr term1 term2 real)
  (let* ((type (term-to-type real))
	 (type1 (term-to-type term1))
	 (type2 (term-to-type term2))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (eqpmr-predconst
	  (if (and (equal? type type1) (equal? type1 type2))
	      (make-predconst (make-arity tvar tvar tvar)
			      (make-subst tvar type)
			      -1 "EqPMR")
	      (myerror "make-eqpmr" "equal types expected" type type1 type2))))
    (make-predicate-formula eqpmr-predconst term1 term2 real)))

(define (make-coeqpmr term1 term2 real)
  (let* ((type (term-to-type real))
	 (type1 (term-to-type term1))
	 (type2 (term-to-type term2))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
         (coeqpmr-predconst
	  (if (and (equal? type type1) (equal? type1 type2))
	      (make-predconst (make-arity tvar tvar tvar)
			      (make-subst tvar type)
			      -1 "CoEqPMR")
	      (myerror "make-coeqpmr"
		       "equal types expected" type type1 type2))))
    (make-predicate-formula coeqpmr-predconst term1 term2 real)))

(define (make-ext term) (make-eqp term term))
(define (make-extnc term) (make-eqpnc term term))

;; Constructor and accessors for formulas:

(define (make-imp premise conclusion) (list 'imp premise conclusion))
(define imp-form-to-premise cadr)
(define imp-form-to-conclusion caddr)
(define (imp-form? x) (and (list? x) (= 3 (length x)) (eq? 'imp (car x))))

(define (make-impnc premise conclusion) (list 'impnc premise conclusion))
(define impnc-form-to-premise cadr)
(define impnc-form-to-conclusion caddr)
(define (impnc-form? x) (and (list? x) (= 3 (length x)) (eq? 'impnc (car x))))

(define (make-and formula1 formula2) (list 'and formula1 formula2))
(define and-form-to-left cadr)
(define and-form-to-right caddr)
(define (and-form? x) (and (list? x) (= 3 (length x)) (eq? 'and (car x))))

(define (make-tensor formula1 formula2) (list 'tensor formula1 formula2))
(define tensor-form-to-left cadr)
(define tensor-form-to-right caddr)
(define (tensor-form? x)
  (and (list? x) (= 3 (length x)) (eq? 'tensor (car x))))

(define (make-all var kernel) (list 'all var kernel))
(define all-form-to-var cadr)
(define all-form-to-kernel caddr)
(define (all-form? x)
  (and (list? x) (= 3 (length x)) (eq? 'all (car x)) (var? (cadr x))))

(define (make-ex var kernel) (list 'ex var kernel))
(define ex-form-to-var cadr)
(define ex-form-to-kernel caddr)
(define (ex-form? x)
  (and (list? x) (= 3 (length x)) (eq? 'ex (car x)) (var? (cadr x))))

(define (make-allnc var kernel) (list 'allnc var kernel))
(define allnc-form-to-var cadr)
(define allnc-form-to-kernel caddr)
(define (allnc-form? x)
  (and (list? x) (= 3 (length x)) (eq? 'allnc (car x)) (var? (cadr x))))

(define (make-exca vars kernel) (list 'exca vars kernel))
(define exca-form-to-vars cadr)
(define exca-form-to-kernel caddr)
(define (exca-form? x)
  (and (list? x) (= 3 (length x)) (eq? 'exca (car x))
       (list? (cadr x)) (pair? (cadr x)) (apply and-op (map var? (cadr x)))))

(define (make-excl vars kernel) (list 'excl vars kernel))
(define excl-form-to-vars cadr)
(define excl-form-to-kernel caddr)
(define (excl-form? x)
  (and (list? x) (= 3 (length x)) (eq? 'excl (car x))
       (list? (cadr x)) (pair? (cadr x)) (apply and-op (map var? (cadr x)))))

(define (make-excu vars kernel) (list 'excu vars kernel))
(define excu-form-to-vars cadr)
(define excu-form-to-kernel caddr)
(define (excu-form? x)
  (and (list? x) (= 3 (length x)) (eq? 'excu (car x))
       (list? (cadr x)) (pair? (cadr x)) (apply and-op (map var? (cadr x)))))

(define (formula-form? x)
  (and (pair? x)
       (memq (tag x) '(atom
		       predicate
		       imp
		       impnc
		       and
		       tensor
		       all
		       ex
		       allnc
		       exca
		       excl
		       excu))))

;; For convenience we add

(define (mk-imp x . rest)
  (if (null? rest)
      x
      (make-imp x (apply mk-imp rest))))

;; imp-form-to-premises computes the first (car x) premises of a formula.

(define (imp-form-to-premises formula . x)
  (cond
   ((null? x)
    (if (imp-form? formula)
	(cons (imp-form-to-premise formula)
	      (imp-form-to-premises (imp-form-to-conclusion formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (imp-form-to-conclusion rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (imp-form-to-premise rho) res)))
	  ((or (= n i) (not (imp-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "imp-form-to-premises" n "premises expected in"
			formula))))))
   (else (myerror "imp-form-to-premises" "non-negative integer expected"
		  (car x)))))

;; imp-form-to-final-conclusion computes the final conclusion (conclusion
;; after removing the first (car x) premises) of a formula.

(define (imp-form-to-final-conclusion formula . x)
  (cond
   ((null? x)
    (if (imp-form? formula)
	(imp-form-to-final-conclusion (imp-form-to-conclusion formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (imp-form-to-conclusion rho))
	   (i 0 (+ 1 i))
	   (res formula (imp-form-to-conclusion res)))
	  ((or (= n i) (not (imp-form? rho)))
	   (if (= n i)
	       res
	       (myerror "imp-form-to-final-conclusion"
			n "premises expected in" formula))))))
   (else (myerror "imp-form-to-final-conclusion"
		  "non-negative integer expected"
		  (car x)))))

(define (imp-form-to-premises-and-final-conclusion formula)
  (if (imp-form? formula)
      (let* ((rec-result (imp-form-to-premises-and-final-conclusion
			  (imp-form-to-conclusion formula)))
	     (formula-list (car rec-result))
	     (final-conclusion (cadr rec-result)))
	(list (cons (imp-form-to-premise formula) formula-list)
	      final-conclusion))
      (list '() formula)))

(define (mk-impnc x . rest)
  (if (null? rest)
      x
      (make-impnc x (apply mk-impnc rest))))

;; impnc-form-to-premises computes the first (car x) premises of a formula.

(define (impnc-form-to-premises formula . x)
  (cond
   ((null? x)
    (if (impnc-form? formula)
	(cons (impnc-form-to-premise formula)
	      (impnc-form-to-premises (impnc-form-to-conclusion formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (impnc-form-to-conclusion rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (impnc-form-to-premise rho) res)))
	  ((or (= n i) (not (impnc-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "impnc-form-to-premises" n "premises expected in"
			formula))))))
   (else (myerror "impnc-form-to-premises" "non-negative integer expected"
		  (car x)))))

;; impnc-form-to-final-conclusion computes the final conclusion (conclusion
;; after removing the first (car x) premises) of a formula.

(define (impnc-form-to-final-conclusion formula . x)
  (cond
   ((null? x)
    (if (impnc-form? formula)
	(impnc-form-to-final-conclusion (impnc-form-to-conclusion formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (impnc-form-to-conclusion rho))
	   (i 0 (+ 1 i))
	   (res formula (impnc-form-to-conclusion res)))
	  ((or (= n i) (not (impnc-form? rho)))
	   (if (= n i)
	       res
	       (myerror "impnc-form-to-final-conclusion"
			n "premises expected in" formula))))))
   (else (myerror "impnc-form-to-final-conclusion"
		  "non-negative integer expected"
		  (car x)))))

(define (impnc-form-to-premises-and-final-conclusion formula)
  (if (impnc-form? formula)
      (let* ((rec-result (impnc-form-to-premises-and-final-conclusion
			  (impnc-form-to-conclusion formula)))
	     (formula-list (car rec-result))
	     (final-conclusion (cadr rec-result)))
	(list (cons (impnc-form-to-premise formula) formula-list)
	      final-conclusion))
      (list '() formula)))

(define imp-impnc-form-to-premise cadr)
(define imp-impnc-form-to-conclusion caddr)
(define (imp-impnc-form? x)
  (and (list? x) (= 3 (length x)) (memq (car x) '(imp impnc))))

(define (imp-impnc-form-to-premises formula . x)
  (cond
   ((null? x)
    (if (imp-impnc-form? formula)
	(cons (imp-impnc-form-to-premise formula)
	      (imp-impnc-form-to-premises
	       (imp-impnc-form-to-conclusion formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (imp-impnc-form-to-conclusion rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (imp-impnc-form-to-premise rho) res)))
	  ((or (= n i) (not (imp-impnc-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "imp-impnc-form-to-premises" n "premises expected in"
			formula))))))
   (else (myerror "imp-impnc-form-to-premises" "non-negative integer expected"
		  (car x)))))

;; imp-impnc-form-to-final-conclusion computes the final conclusion (conclusion
;; after removing the first (car x) premises) of a formula.

(define (imp-impnc-form-to-final-conclusion formula . x)
  (cond
   ((null? x)
    (if (imp-impnc-form? formula)
	(imp-impnc-form-to-final-conclusion
	 (imp-impnc-form-to-conclusion formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (imp-impnc-form-to-conclusion rho))
	   (i 0 (+ 1 i))
	   (res formula (imp-impnc-form-to-conclusion res)))
	  ((or (= n i) (not (imp-impnc-form? rho)))
	   (if (= n i)
	       res
	       (myerror "imp-impnc-form-to-final-conclusion"
			n "premises expected in" formula))))))
   (else (myerror "imp-impnc-form-to-final-conclusion"
		  "non-negative integer expected"
		  (car x)))))

(define (imp-all-allnc-form-to-final-conclusion formula)
  (cond
   ((imp-form? formula)
    (imp-all-allnc-form-to-final-conclusion (imp-form-to-conclusion formula)))
   ((all-form? formula)
    (imp-all-allnc-form-to-final-conclusion (all-form-to-kernel formula)))
   ((allnc-form? formula)
    (imp-all-allnc-form-to-final-conclusion (allnc-form-to-kernel formula)))
   (else formula)))

(define (and-form-to-conjuncts formula)
  (if (and-form? formula)
      (cons (and-form-to-left formula)
	    (and-form-to-conjuncts (and-form-to-right formula)))
      (list formula)))

(define all-allnc-form-to-var cadr)
(define all-allnc-form-to-kernel caddr)
(define (all-allnc-form? x)
  (and (list? x) (= 3 (length x)) (memq (car x) '(all allnc)) (var? (cadr x))))

(define (imp-impnc-all-allnc-form-to-vars formula . x)
  (cond
   ((null? x)
    (cond
     ((imp-form? formula)
      (imp-impnc-all-allnc-form-to-vars (imp-form-to-conclusion formula)))
     ((impnc-form? formula)
      (imp-impnc-all-allnc-form-to-vars (impnc-form-to-conclusion formula)))
     ((all-form? formula)
      (cons (all-form-to-var formula)
	    (imp-impnc-all-allnc-form-to-vars (all-form-to-kernel formula))))
     ((allnc-form? formula)
      (cons (allnc-form-to-var formula)
	    (imp-impnc-all-allnc-form-to-vars (allnc-form-to-kernel formula))))
     (else '())))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (if (zero? n) '()
	  (cond
	   ((imp-form? formula) (imp-impnc-all-allnc-form-to-vars
				 (imp-form-to-conclusion formula) n))
	   ((impnc-form? formula) (imp-impnc-all-allnc-form-to-vars
				 (impnc-form-to-conclusion formula) n))
	   ((all-form? formula)
	    (cons (all-form-to-var formula)
		  (imp-impnc-all-allnc-form-to-vars
		   (all-form-to-kernel formula) (- n 1))))
	   ((allnc-form? formula)
	    (cons (allnc-form-to-var formula)
		  (imp-impnc-all-allnc-form-to-vars
		   (allnc-form-to-kernel formula) (- n 1))))
	   (else '())))))
   (else (myerror "imp-impnc-all-allnc-form-to-vars"
		  "non-negative integer expected"
		  (car x)))))

(define (imp-impnc-all-allnc-form-to-premises formula . x)
  (cond
   ((null? x)
    (cond
     ((imp-form? formula)
      (cons (imp-form-to-premise formula)
	    (imp-impnc-all-allnc-form-to-premises
	     (imp-form-to-conclusion formula))))
     ((impnc-form? formula)
      (cons (impnc-form-to-premise formula)
	    (imp-impnc-all-allnc-form-to-premises
	     (impnc-form-to-conclusion formula))))
     ((all-form? formula)
      (imp-impnc-all-allnc-form-to-premises (all-form-to-kernel formula)))
     ((allnc-form? formula)
      (imp-impnc-all-allnc-form-to-premises (allnc-form-to-kernel formula)))
     (else '())))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (if (zero? n) formula
	  (cond
	   ((imp-form? formula)
	    (cons (imp-form-to-premise formula)
		  (imp-impnc-all-allnc-form-to-premises
		   (imp-form-to-conclusion formula) (- n 1))))
	   ((impnc-form? formula)
	    (cons (impnc-form-to-premise formula)
		  (imp-impnc-all-allnc-form-to-premises
		   (impnc-form-to-conclusion formula) (- n 1))))
	   ((all-form? formula)
	    (imp-impnc-all-allnc-form-to-premises
	     (all-form-to-kernel formula) n))
	   ((allnc-form? formula)
	    (imp-impnc-all-allnc-form-to-premises
	     (allnc-form-to-kernel formula) n))
	   (else '())))))
   (else (myerror "imp-impnc-all-allnc-form-to-premises"
		  "non-negative integer expected"
		  (car x)))))

(define (imp-impnc-all-allnc-form-to-vars-and-premises formula . x)
  (cond
   ((null? x)
    (cond
     ((imp-form? formula)
      (cons (imp-form-to-premise formula)
	    (imp-impnc-all-allnc-form-to-vars-and-premises
	     (imp-form-to-conclusion formula))))
     ((impnc-form? formula)
      (cons (impnc-form-to-premise formula)
	    (imp-impnc-all-allnc-form-to-vars-and-premises
	     (impnc-form-to-conclusion formula))))
     ((all-form? formula)
      (cons (all-form-to-var formula)
	    (imp-impnc-all-allnc-form-to-vars-and-premises
	     (all-form-to-kernel formula))))
     ((allnc-form? formula)
      (cons (allnc-form-to-var formula)
	    (imp-impnc-all-allnc-form-to-vars-and-premises
	     (allnc-form-to-kernel formula))))
     (else '())))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (if (zero? n) '()
	  (cond
	   ((imp-form? formula)
	    (cons (imp-form-to-premise formula)
		  (imp-impnc-all-allnc-form-to-vars-and-premises
		   (imp-form-to-conclusion formula) (- n 1))))
	   ((impnc-form? formula)
	    (cons (impnc-form-to-premise formula)
		  (imp-impnc-all-allnc-form-to-vars-and-premises
		   (impnc-form-to-conclusion formula) (- n 1))))
	   ((all-form? formula)
	    (cons (all-form-to-var formula)
		  (imp-impnc-all-allnc-form-to-vars-and-premises
		   (all-form-to-kernel formula) (- n 1))))
	   ((allnc-form? formula)
	    (cons (allnc-form-to-var formula)
		  (imp-impnc-all-allnc-form-to-vars-and-premises
		   (allnc-form-to-kernel formula) (- n 1))))
	   (else '())))))
   (else (myerror "imp-impnc-all-allnc-form-to-vars-and-premises"
		  "non-negative integer expected"
		  (car x)))))

(define (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
	 formula . x)
  (cond
   ((null? x)
    (cond
     ((imp-form? formula)
      (cons
       (imp-form-to-premise formula)
       (cons #f (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
		 (imp-form-to-conclusion formula)))))
     ((impnc-form? formula)
      (cons
       (impnc-form-to-premise formula)
       (cons #t (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
		 (impnc-form-to-conclusion formula)))))
     ((all-form? formula)
      (cons
       (all-form-to-var formula)
       (cons #f (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
		 (all-form-to-kernel formula)))))
     ((allnc-form? formula)
      (cons
       (allnc-form-to-var formula)
       (cons #t (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
		 (allnc-form-to-kernel formula)))))
     (else '())))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (if (zero? n) '()
	  (cond
	   ((imp-form? formula)
	    (cons
	     (imp-form-to-premise formula)
	     (cons
	      #f (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
		  (imp-form-to-conclusion formula) (- n 1)))))
	   ((impnc-form? formula)
	    (cons
	     (impnc-form-to-premise formula)
	     (cons
	      #t (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
		  (impnc-form-to-conclusion formula) (- n 1)))))
	   ((all-form? formula)
	    (cons
	     (all-form-to-var formula)
	     (cons
	      #f (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
		  (all-form-to-kernel formula) (- n 1)))))
	   ((allnc-form? formula)
	    (cons
	     (allnc-form-to-var formula)
	     (cons
	      #t (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
		  (allnc-form-to-kernel formula) (- n 1)))))
	   (else '())))))
   (else (myerror "imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator"
		  "non-negative integer expected"
		  (car x)))))

(define (imp-impnc-all-allnc-form-to-final-conclusion formula)
  (cond ((imp-impnc-form? formula)
	 (imp-impnc-all-allnc-form-to-final-conclusion
	  (imp-impnc-form-to-conclusion formula)))
	((all-allnc-form? formula)
	 (imp-impnc-all-allnc-form-to-final-conclusion
	  (all-allnc-form-to-kernel formula)))
	(else formula)))

(define (impnc-allnc-pvar-formula? formula)
  (cond
   ((impnc-form? formula)
    (impnc-allnc-pvar-formula? (impnc-form-to-conclusion formula)))
   ((allnc-form? formula)
    (impnc-allnc-pvar-formula? (allnc-form-to-kernel formula)))
   ((predicate-form? formula)
    (pvar-form? (predicate-form-to-predicate formula)))
   (else #f)))

(define (mk-and . x)
  (cond ((null? x) truth)
	((null? (cdr x)) (car x))
	(else (make-and (car x) (apply mk-and (cdr x))))))

(define (make-and-without-truth formula1 formula2)
  (cond ((formula=? formula1 truth) formula2)
	((formula=? formula2 truth) formula1)
	(else (make-and formula1 formula2))))

(define (mk-tensor x . rest)
  (if (null? rest)
      x
      (make-tensor x (apply mk-tensor rest))))

(define (tensor-form-to-parts formula)
  (if (tensor-form? formula)
      (cons (tensor-form-to-left formula)
	    (tensor-form-to-parts (tensor-form-to-right formula)))
      (list formula)))

(define (mk-neg . x) (apply mk-imp (append x (list falsity))))
(define (mk-neg-log . x) (apply mk-imp (append x (list falsity-log))))

;; (mk-all var1 ... formula) results from formula by first generalizing
;; var1, then var2 etc.

(define (mk-all x . rest)
  (if (null? rest)
      x
      (make-all x (apply mk-all rest))))

;; all-form-to-vars computes the first (car x) vars of a formula.

(define (all-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (all-form? formula)
	(cons (all-form-to-var formula)
	      (all-form-to-vars (all-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (all-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (all-form-to-var rho) res)))
	  ((or (= n i) (not (all-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "all-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "all-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; all-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (all-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (all-form? formula)
	(all-form-to-final-kernel (all-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (all-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (all-form-to-kernel res)))
	  ((or (= n i) (not (all-form? rho)))
	   (if (= n i)
	       res
	       (myerror "all-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "all-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))

(define (all-form-to-vars-and-final-kernel formula)
  (if (all-form? formula)
      (let* ((rec-result (all-form-to-vars-and-final-kernel
			  (all-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (all-form-to-var formula) vars) final-kernel))
      (list '() formula)))

(define (mk-ex x . rest)
  (if (null? rest)
      x
      (make-ex x (apply mk-ex rest))))

;; ex-form-to-vars computes the first (car x) vars of a formula.

(define (ex-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (ex-form? formula)
	(cons (ex-form-to-var formula)
	      (ex-form-to-vars (ex-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (ex-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (ex-form-to-var rho) res)))
	  ((or (= n i) (not (ex-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "ex-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "ex-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; ex-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (ex-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (ex-form? formula)
	(ex-form-to-final-kernel (ex-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (ex-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (ex-form-to-kernel res)))
	  ((or (= n i) (not (ex-form? rho)))
	   (if (= n i)
	       res
	       (myerror "ex-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "ex-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))

(define (ex-form-to-vars-and-final-kernel formula)
  (if (ex-form? formula)
      (let* ((rec-result (ex-form-to-vars-and-final-kernel
			  (ex-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (ex-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; (mk-allnc var1 ... formula) results from formula by first generalizing
;; var1, then var2 etc.

(define (mk-allnc x . rest)
  (if (null? rest)
      x
      (make-allnc x (apply mk-allnc rest))))

;; allnc-form-to-vars computes the first (car x) vars of a formula.

(define (allnc-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (allnc-form? formula)
	(cons (allnc-form-to-var formula)
	      (allnc-form-to-vars (allnc-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (allnc-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (allnc-form-to-var rho) res)))
	  ((or (= n i) (not (allnc-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "allnc-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "allnc-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; allnc-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (allnc-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (allnc-form? formula)
	(allnc-form-to-final-kernel (allnc-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (allnc-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (allnc-form-to-kernel res)))
	  ((or (= n i) (not (allnc-form? rho)))
	   (if (= n i)
	       res
	       (myerror "allnc-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "allnc-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))

(define (allnc-form-to-vars-and-final-kernel formula)
  (if (allnc-form? formula)
      (let* ((rec-result (allnc-form-to-vars-and-final-kernel
			  (allnc-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (allnc-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; all-allnc-form-to-vars computes the first (car x) vars of a formula.

(define (all-allnc-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (all-allnc-form? formula)
	(cons (all-allnc-form-to-var formula)
	      (all-allnc-form-to-vars (all-allnc-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (all-allnc-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (all-allnc-form-to-var rho) res)))
	  ((or (= n i) (not (all-allnc-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "all-allnc-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "all-allnc-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; all-allnc-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (all-allnc-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (all-allnc-form? formula)
	(all-allnc-form-to-final-kernel (all-allnc-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (all-allnc-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (all-allnc-form-to-kernel res)))
	  ((or (= n i) (not (all-allnc-form? rho)))
	   (if (= n i)
	       res
	       (myerror "all-allnc-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "all-allnc-form-to-final-kernel"
		  "non-negative integer expected"
		  (car x)))))

(define (all-allnc-form-to-vars-and-final-kernel formula)
  (if (all-allnc-form? formula)
      (let* ((rec-result (all-allnc-form-to-vars-and-final-kernel
			  (all-allnc-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (all-allnc-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; all-allnc-form-to-prefix computes the a list of the first (car x)
;; lists ('all/allnc var) of a formula.

(define (all-allnc-form-to-prefix formula . x)
  (cond
   ((null? x)
    (cond
     ((all-form? formula)
      (cons (list (list 'all (all-form-to-var formula)))
	    (all-allnc-form-to-prefix (all-form-to-kernel formula))))
     ((allnc-form? formula)
      (cons (list (list 'allnc (allnc-form-to-var formula)))
	    (all-allnc-form-to-prefix (allnc-form-to-kernel formula))))
     (else '())))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (all-allnc-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (if (all-form? formula)
			      (list 'all (all-form-to-var rho))
			      (list 'allnc (allnc-form-to-var rho)))
			  res)))
	  ((or (= n i) (not (all-allnc-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "all-allnc-form-to-prefix" n "vars expected in"
			formula))))))
   (else (myerror "all-allnc-form-to-prefix" "non-negative integer expected"
		  (car x)))))

(define (mk-exca x . rest)
  (if (null? rest)
      x
      (let ((kernel-and-rev-vars (reverse rest)))
	(make-exca (cons x (reverse (cdr kernel-and-rev-vars)))
		   (car kernel-and-rev-vars)))))

(define (mk-excl x . rest)
  (if (null? rest)
      x
      (let ((kernel-and-rev-vars (reverse rest)))
	(make-excl (cons x (reverse (cdr kernel-and-rev-vars)))
		   (car kernel-and-rev-vars)))))

(define (mk-excu x . rest)
  (if (null? rest)
      x
      (let ((kernel-and-rev-vars (reverse rest)))
	(make-excu (cons x (reverse (cdr kernel-and-rev-vars)))
		     (car kernel-and-rev-vars)))))

(define (exc-form? x)
  (and (list? x) (= 3 (length x)) (memq (car x) '(exca excl excu))
       (list? (cadr x)) (pair? (cadr x)) (apply and-op (map var? (cadr x)))))

(define exc-form-to-quant car)
(define exc-form-to-vars cadr)
(define exc-form-to-kernel caddr)

;; Now for negation.  make-negation is in boole.scm, because it uses
;; falsity: (define (make-negation formula) (make-imp formula falsity))

(define (negation-form? x)
  (and (imp-form? x) (formula=? (imp-form-to-conclusion x) falsity)))

(define negation-form-to-kernel imp-form-to-premise)

;; make-negation-log is in boole.scm, because it uses falsity-log
;; (define (make-negation-log formula) (make-imp formula falsity-log))

(define (negation-log-form? x)
  (and (imp-form? x) (formula=? (imp-form-to-conclusion x) falsity-log)))

(define negation-log-form-to-kernel imp-form-to-premise)

;; By means of inductively defined predicate constants, we can add
;; existential quantification exd, exl, exr, exnc, exdt, exlt, exrt,
;; exnct.  conjunction andd, andr, andnc (andb is for the boolean
;; operator), disjunction or, orl, orr, oru (orb is for the boolean
;; operator).

;; However, for efficiency reasons it can still be useful to keep the
;; primitives ex, and.  This came up in examples/analysis/average.scm.

;; --> is the notation for uniform implication.

(define (make-exd var kernel)
  (make-predicate-formula
   (make-idpredconst
    (if (t-deg-zero? (var-to-t-deg var)) "ExD" "ExDT")
    (list (var-to-type var)) (list (make-cterm var kernel)))))

(define (exd-form-to-var formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (car (cterm-to-vars (car cterms)))))

(define (exd-form-to-kernel formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (exd-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (member (idpredconst-to-name pred) (list "ExD" "ExDT"))))))

(define (mk-exd x . rest)
  (if (null? rest)
      x
      (make-exd x (apply mk-exd rest))))

(define (exd-form-to-vars-and-final-kernel formula)
  (if (exd-form? formula)
      (let* ((rec-result (exd-form-to-vars-and-final-kernel
			  (exd-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (exd-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; exd-form-to-vars computes the first (car x) vars of a formula.

(define (exd-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (exd-form? formula)
	(cons (exd-form-to-var formula)
	      (exd-form-to-vars (exd-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exd-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (exd-form-to-var rho) res)))
	  ((or (= n i) (not (exd-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "exd-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "exd-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; exd-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (exd-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (exd-form? formula)
	(exd-form-to-final-kernel (exd-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exd-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (exd-form-to-kernel res)))
	  ((or (= n i) (not (exd-form? rho)))
	   (if (= n i)
	       res
	       (myerror "exd-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "exd-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))


(define (make-exl var kernel)
  (make-predicate-formula
   (make-idpredconst
    (if (t-deg-zero? (var-to-t-deg var)) "ExL" "ExLT")
    (list (var-to-type var)) (list (make-cterm var kernel)))))

(define (exl-form-to-var formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (car (cterm-to-vars (car cterms)))))

(define (exl-form-to-kernel formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (exl-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (member (idpredconst-to-name pred) (list  "ExL"  "ExLT"))))))

(define (mk-exl x . rest)
  (if (null? rest)
      x
      (make-exl x (apply mk-exl rest))))

(define (exl-form-to-vars-and-final-kernel formula)
  (if (exl-form? formula)
      (let* ((rec-result (exl-form-to-vars-and-final-kernel
			  (exl-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (exl-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; exl-form-to-vars computes the first (car x) vars of a formula.

(define (exl-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (exl-form? formula)
	(cons (exl-form-to-var formula)
	      (exl-form-to-vars (exl-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exl-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (exl-form-to-var rho) res)))
	  ((or (= n i) (not (exl-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "exl-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "exl-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; exl-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (exl-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (exl-form? formula)
	(exl-form-to-final-kernel (exl-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exl-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (exl-form-to-kernel res)))
	  ((or (= n i) (not (exl-form? rho)))
	   (if (= n i)
	       res
	       (myerror "exl-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "exl-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))

(define (make-exr var kernel)
  (make-predicate-formula
   (make-idpredconst
    (if (t-deg-zero? (var-to-t-deg var)) "ExR" "ExRT")
    (list (var-to-type var)) (list (make-cterm var kernel)))))

(define (exr-form-to-var formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (car (cterm-to-vars (car cterms)))))

(define (exr-form-to-kernel formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (exr-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (member (idpredconst-to-name pred) (list "ExR" "ExRT"))))))

(define (mk-exr x . rest)
  (if (null? rest)
      x
      (make-exr x (apply mk-exr rest))))

(define (exr-form-to-vars-and-final-kernel formula)
  (if (exr-form? formula)
      (let* ((rec-result (exr-form-to-vars-and-final-kernel
			  (exr-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (exr-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; exr-form-to-vars computes the first (car x) vars of a formula.

(define (exr-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (exr-form? formula)
	(cons (exr-form-to-var formula)
	      (exr-form-to-vars (exr-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exr-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (exr-form-to-var rho) res)))
	  ((or (= n i) (not (exr-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "exr-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "exr-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; exr-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (exr-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (exr-form? formula)
	(exr-form-to-final-kernel (exr-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exr-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (exr-form-to-kernel res)))
	  ((or (= n i) (not (exr-form? rho)))
	   (if (= n i)
	       res
	       (myerror "exr-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "exr-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))


(define (make-exnc var kernel)
  (make-predicate-formula
   (make-idpredconst
    (if (t-deg-zero? (var-to-t-deg var)) "ExNc" "ExNcT")
    (list (var-to-type var)) (list (make-cterm var kernel)))))

(define (exnc-form-to-var formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (car (cterm-to-vars (car cterms)))))

(define (exnc-form-to-kernel formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (exnc-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (member (idpredconst-to-name pred) (list "ExNc" "ExNcT"))))))

(define (mk-exnc x . rest)
  (if (null? rest)
      x
      (make-exnc x (apply mk-exnc rest))))

(define (exnc-form-to-vars-and-final-kernel formula)
  (if (exnc-form? formula)
      (let* ((rec-result (exnc-form-to-vars-and-final-kernel
			  (exnc-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (exnc-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; exnc-form-to-vars computes the first (car x) vars of a formula.

(define (exnc-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (exnc-form? formula)
	(cons (exnc-form-to-var formula)
	      (exnc-form-to-vars (exnc-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exnc-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (exnc-form-to-var rho) res)))
	  ((or (= n i) (not (exnc-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "exnc-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "exnc-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; exnc-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (exnc-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (exnc-form? formula)
	(exnc-form-to-final-kernel (exnc-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exnc-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (exnc-form-to-kernel res)))
	  ((or (= n i) (not (exnc-form? rho)))
	   (if (= n i)
	       res
	       (myerror "exnc-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "exnc-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))

(define (make-exi var kernel)
  (if (formula-of-nulltype? kernel)
      (make-exl var kernel)
      (make-exd var kernel)))

(define (mk-exi x . rest)
  (if (null? rest)
      x
      (make-exi x (apply mk-exi rest))))

(define (exi-form? formula)
  (and (predicate-form? formula)
       (let ((pred (predicate-form-to-predicate formula)))
	 (and (idpredconst-form? pred)
	      (member
	       (idpredconst-to-name pred)
	       (list "ExNc" "ExL" "ExR" "ExD"
		     "ExNcT" "ExLT" "ExRT" "ExDT"))))))

(define (exi-mr-exi-form? formula)
  (or (exi-form? formula)
      (and (predicate-form? formula)
	   (let ((pred (predicate-form-to-predicate formula)))
	     (and (idpredconst-form? pred)
		  (member
		   (idpredconst-to-name pred)
		   (list "ExNcMR" "ExLMR" "ExRMR" "ExDMR"
			 "ExNcTMR" "ExLTMR" "ExRTMR" "ExDTMR")))))))

(define (exi-mr-exi-form-to-vars formula)
  (if (exi-mr-exi-form? formula)
      (let ((cterm
	     (car (idpredconst-to-cterms
		   (predicate-form-to-predicate formula)))))
	(append (cterm-to-vars cterm)
		(exi-mr-exi-form-to-vars (cterm-to-formula cterm))))
      '()))

(define (exi-mr-exi-form-to-final-kernel formula)
  (if (exi-mr-exi-form? formula)
      (let ((cterm
	     (car (idpredconst-to-cterms
		   (predicate-form-to-predicate formula)))))
	(exi-mr-exi-form-to-final-kernel (cterm-to-formula cterm)))
      formula))

(define (and-andi-ex-exi-formula-to-vars-and-conjuncts formula . x)
  (let* ((rest (if (null? x) (list '() '()) x))
	 (vars (car rest))
	 (conjs (cadr rest)))
    (cond ((and-form? formula)
	   (apply and-andi-ex-exi-formula-to-vars-and-conjuncts
	    (and-form-to-right formula)
	    (list vars (snoc conjs (and-form-to-left formula)))))
	  ((andi-form? formula)
	   (let ((flas (map cterm-to-formula
			    (idpredconst-to-cterms
			     (predicate-form-to-predicate formula)))))
	     (apply and-andi-ex-exi-formula-to-vars-and-conjuncts
	      (cadr flas)
	      (list vars (snoc conjs (car flas))))))
	  ((ex-form? formula)
	   (apply and-andi-ex-exi-formula-to-vars-and-conjuncts
	    (ex-form-to-kernel formula)
	    (list (snoc vars (ex-form-to-var formula)) conjs)))
	  ((exi-form? formula)
	   (let ((cterm
		  (car (idpredconst-to-cterms
			(predicate-form-to-predicate formula)))))
	     (apply and-andi-ex-exi-formula-to-vars-and-conjuncts
	      (cterm-to-formula cterm)
	      (list (append vars (cterm-to-vars cterm)) conjs))))
	  (else (list vars (snoc conjs formula))))))

(define (make-exdt var kernel)
  (make-predicate-formula
   (make-idpredconst
    "ExDT" (list (var-to-type var)) (list (make-cterm var kernel)))))

(define (exdt-form-to-var formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (car (cterm-to-vars (car cterms)))))

(define (exdt-form-to-kernel formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (exdt-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "ExDT" (idpredconst-to-name pred))))))

(define (mk-exdt x . rest)
  (if (null? rest)
      x
      (make-exdt x (apply mk-exdt rest))))

(define (exdt-form-to-vars-and-final-kernel formula)
  (if (exdt-form? formula)
      (let* ((rec-result (exdt-form-to-vars-and-final-kernel
			  (exdt-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (exdt-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; exdt-form-to-vars computes the first (car x) vars of a formula.

(define (exdt-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (exdt-form? formula)
	(cons (exdt-form-to-var formula)
	      (exdt-form-to-vars (exdt-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exdt-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (exdt-form-to-var rho) res)))
	  ((or (= n i) (not (exdt-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "exdt-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "exdt-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; exdt-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (exdt-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (exdt-form? formula)
	(exdt-form-to-final-kernel (exdt-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exdt-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (exdt-form-to-kernel res)))
	  ((or (= n i) (not (exdt-form? rho)))
	   (if (= n i)
	       res
	       (myerror "exdt-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "exdt-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))

(define (make-exlt var kernel)
  (make-predicate-formula
   (make-idpredconst
    "ExLT" (list (var-to-type var)) (list (make-cterm var kernel)))))

(define (exlt-form-to-var formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (car (cterm-to-vars (car cterms)))))

(define (exlt-form-to-kernel formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (exlt-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "ExLT" (idpredconst-to-name pred))))))

(define (mk-exlt x . rest)
  (if (null? rest)
      x
      (make-exlt x (apply mk-exlt rest))))

(define (exlt-form-to-vars-and-final-kernel formula)
  (if (exlt-form? formula)
      (let* ((rec-result (exlt-form-to-vars-and-final-kernel
			  (exlt-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (exlt-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; exlt-form-to-vars computes the first (car x) vars of a formula.

(define (exlt-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (exlt-form? formula)
	(cons (exlt-form-to-var formula)
	      (exlt-form-to-vars (exlt-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exlt-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (exlt-form-to-var rho) res)))
	  ((or (= n i) (not (exlt-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "exlt-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "exlt-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; exlt-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (exlt-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (exlt-form? formula)
	(exlt-form-to-final-kernel (exlt-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exlt-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (exlt-form-to-kernel res)))
	  ((or (= n i) (not (exlt-form? rho)))
	   (if (= n i)
	       res
	       (myerror "exlt-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "exlt-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))

(define (make-exrt var kernel)
  (make-predicate-formula
   (make-idpredconst
    "ExRT" (list (var-to-type var)) (list (make-cterm var kernel)))))

(define (exrt-form-to-var formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (car (cterm-to-vars (car cterms)))))

(define (exrt-form-to-kernel formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (exrt-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "ExRT" (idpredconst-to-name pred))))))

(define (mk-exrt x . rest)
  (if (null? rest)
      x
      (make-exrt x (apply mk-exrt rest))))

(define (exrt-form-to-vars-and-final-kernel formula)
  (if (exrt-form? formula)
      (let* ((rec-result (exrt-form-to-vars-and-final-kernel
			  (exrt-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (exrt-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; exrt-form-to-vars computes the first (car x) vars of a formula.

(define (exrt-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (exrt-form? formula)
	(cons (exrt-form-to-var formula)
	      (exrt-form-to-vars (exrt-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exrt-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (exrt-form-to-var rho) res)))
	  ((or (= n i) (not (exrt-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "exrt-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "exrt-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; exrt-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (exrt-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (exrt-form? formula)
	(exrt-form-to-final-kernel (exrt-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exrt-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (exrt-form-to-kernel res)))
	  ((or (= n i) (not (exrt-form? rho)))
	   (if (= n i)
	       res
	       (myerror "exrt-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "exrt-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))

(define (make-exnct var kernel)
  (make-predicate-formula
   (make-idpredconst
    "ExNcT" (list (var-to-type var)) (list (make-cterm var kernel)))))

(define (exnct-form-to-var formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (car (cterm-to-vars (car cterms)))))

(define (exnct-form-to-kernel formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (exnct-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "ExNcT" (idpredconst-to-name pred))))))

(define (mk-exnct x . rest)
  (if (null? rest)
      x
      (make-exnct x (apply mk-exnct rest))))

(define (exnct-form-to-vars-and-final-kernel formula)
  (if (exnct-form? formula)
      (let* ((rec-result (exnct-form-to-vars-and-final-kernel
			  (exnct-form-to-kernel formula)))
	     (vars (car rec-result))
	     (final-kernel (cadr rec-result)))
	(list (cons (exnct-form-to-var formula) vars) final-kernel))
      (list '() formula)))

;; exnct-form-to-vars computes the first (car x) vars of a formula.

(define (exnct-form-to-vars formula . x)
  (cond
   ((null? x)
    (if (exnct-form? formula)
	(cons (exnct-form-to-var formula)
	      (exnct-form-to-vars (exnct-form-to-kernel formula)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exnct-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res '() (cons (exnct-form-to-var rho) res)))
	  ((or (= n i) (not (exnct-form? rho)))
	   (if (= n i)
	       (reverse res)
	       (myerror "exnct-form-to-vars" n "vars expected in"
			formula))))))
   (else (myerror "exnct-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; exnct-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) vars) of a formula.

(define (exnct-form-to-final-kernel formula . x)
  (cond
   ((null? x)
    (if (exnct-form? formula)
	(exnct-form-to-final-kernel (exnct-form-to-kernel formula))
	formula))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((rho formula (exnct-form-to-kernel rho))
	   (i 0 (+ 1 i))
	   (res formula (exnct-form-to-kernel res)))
	  ((or (= n i) (not (exnct-form? rho)))
	   (if (= n i)
	       res
	       (myerror "exnct-form-to-final-kernel"
			n "vars expected in"
			formula))))))
   (else (myerror "exnct-form-to-final-kernel" "non-negative integer expected"
		  (car x)))))

(define (make-ord formula1 formula2)
  (make-predicate-formula
   (make-idpredconst
    "OrD" '() (list (make-cterm formula1) (make-cterm formula2)))))

(define (ord-form-to-left formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (ord-form-to-right formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (cadr cterms))))

(define (ord-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "OrD" (idpredconst-to-name pred))))))

(define (mk-ord . x)
  (cond ((null? x) falsity)
	((null? (cdr x)) (car x))
	(else (make-ord (car x) (apply mk-ord (cdr x))))))

(define (make-orl formula1 formula2)
  (make-predicate-formula
   (make-idpredconst
    "OrL" '() (list (make-cterm formula1) (make-cterm formula2)))))

(define (orl-form-to-left formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (orl-form-to-right formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (cadr cterms))))

(define (orl-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "OrL" (idpredconst-to-name pred))))))

(define (mk-orl . x)
  (cond ((null? x) falsity)
	((null? (cdr x)) (car x))
	(else (make-orl (car x) (apply mk-orl (cdr x))))))

(define (make-orr formula1 formula2)
  (make-predicate-formula
   (make-idpredconst
    "OrR" '() (list (make-cterm formula1) (make-cterm formula2)))))

(define (orr-form-to-left formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (orr-form-to-right formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (cadr cterms))))

(define (orr-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "OrR" (idpredconst-to-name pred))))))

(define (mk-orr . x)
  (cond ((null? x) falsity)
	((null? (cdr x)) (car x))
	(else (make-orr (car x) (apply mk-orr (cdr x))))))

(define (make-oru formula1 formula2)
  (make-predicate-formula
   (make-idpredconst
    "OrU" '() (list (make-cterm formula1) (make-cterm formula2)))))

(define (oru-form-to-left formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (oru-form-to-right formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (cadr cterms))))

(define (oru-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "OrU" (idpredconst-to-name pred))))))

(define (mk-oru . x)
  (cond ((null? x) falsity)
	((null? (cdr x)) (car x))
	(else (make-oru (car x) (apply mk-oru (cdr x))))))

(define (make-ornc formula1 formula2)
  (make-predicate-formula
   (make-idpredconst
    "OrNc" '() (list (make-cterm formula1) (make-cterm formula2)))))

(define (ornc-form-to-left formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (ornc-form-to-right formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (cadr cterms))))

(define (ornc-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "OrNc" (idpredconst-to-name pred))))))

(define (mk-ornc . x)
  (cond ((null? x) falsity)
	((null? (cdr x)) (car x))
	(else (make-ornc (car x) (apply mk-ornc (cdr x))))))

(define (make-ori formula1 formula2)
  (let ((nulltype1? (formula-of-nulltype? formula1))
	(nulltype2? (formula-of-nulltype? formula2)))
    (cond ((and nulltype1? nulltype2?)
	   (make-oru formula1 formula2))
	  ((and nulltype1? (not nulltype2?))
	   (make-orr formula1 formula2))
	  ((and (not nulltype1?) nulltype2?)
	   (make-orl formula1 formula2))
	  ((and (not nulltype1?) (not nulltype2?))
	   (make-ord formula1 formula2)))))

(define (mk-ori . x)
  (cond ((null? x) falsity)
	((null? (cdr x)) (car x))
	(else (make-ori (car x) (apply mk-ori (cdr x))))))

(define (ori-mr-ori-form? formula)
  (and (predicate-form? formula)
       (let ((pred (predicate-form-to-predicate formula)))
	 (and (idpredconst-form? pred)
	      (member
	       (idpredconst-to-name pred)
	       (list "OrNc" "OrU" "OrL" "OrR" "OrD"
		     "OrUMR" "OrLMR" "OrRMR" "OrDMR"))))))

(define (make-andd formula1 formula2)
  (make-predicate-formula
   (make-idpredconst
    "AndD" '() (list (make-cterm formula1) (make-cterm formula2)))))

(define (andd-form-to-left formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (andd-form-to-right formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (cadr cterms))))

(define (andd-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "AndD" (idpredconst-to-name pred))))))

(define (mk-andd . x)
  (cond ((null? x) truth)
	((null? (cdr x)) (car x))
	(else (make-andd (car x) (apply mk-andd (cdr x))))))

(define (make-andr formula1 formula2)
  (make-predicate-formula
   (make-idpredconst
    "AndR" '() (list (make-cterm formula1) (make-cterm formula2)))))

(define (andr-form-to-left formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (andr-form-to-right formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (cadr cterms))))

(define (andr-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "AndR" (idpredconst-to-name pred))))))

(define (mk-andr . x)
  (cond ((null? x) truth)
	((null? (cdr x)) (car x))
	(else (make-andr (car x) (apply mk-andr (cdr x))))))

(define (make-andl formula1 formula2)
  (make-predicate-formula
   (make-idpredconst
    "AndL" '() (list (make-cterm formula1) (make-cterm formula2)))))

(define (andl-form-to-left formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (andl-form-to-right formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (cadr cterms))))

(define (andl-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "AndL" (idpredconst-to-name pred))))))

(define (mk-andl . x)
  (cond ((null? x) truth)
	((null? (cdr x)) (car x))
	(else (make-andl (car x) (apply mk-andl (cdr x))))))

(define (make-andnc formula1 formula2)
  (make-predicate-formula
   (make-idpredconst
    "AndNc" '() (list (make-cterm formula1) (make-cterm formula2)))))

(define (andnc-form-to-left formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (car cterms))))

(define (andnc-form-to-right formula)
  (let* ((idpredconst (predicate-form-to-predicate formula))
	 (cterms (idpredconst-to-cterms idpredconst)))
    (cterm-to-formula (cadr cterms))))

(define (andnc-form? x)
  (and (predicate-form? x)
       (let ((pred (predicate-form-to-predicate x)))
	 (and (idpredconst-form? pred)
	      (equal? "AndNc" (idpredconst-to-name pred))))))

(define (mk-andnc . x)
  (cond ((null? x) truth)
	((null? (cdr x)) (car x))
	(else (make-andnc (car x) (apply mk-andnc (cdr x))))))

(define (make-andi formula1 formula2)
  (let ((nulltype1? (formula-of-nulltype? formula1))
	(nulltype2? (formula-of-nulltype? formula2)))
    (cond ((and nulltype1? nulltype2?)
	   (make-andnc formula1 formula2))
	  ((and nulltype1? (not nulltype2?))
	   (make-andr formula1 formula2))
	  ((and (not nulltype1?) nulltype2?)
	   (make-andl formula1 formula2))
	  ((and (not nulltype1?) (not nulltype2?))
	   (make-andd formula1 formula2)))))

(define (mk-andi . x)
  (cond ((null? x) truth)
	((null? (cdr x)) (car x))
	(else (make-andi (car x) (apply mk-andi (cdr x))))))

(define (mk-andi-for-sorted-formulas . x)
  (cond ((null? x) truth)
	((null? (cdr x)) (car x))
	(else
	 (make-andi (car x) (apply mk-andi-for-sorted-formulas (cdr x))))))

(define (andi-form? formula)
  (and (predicate-form? formula)
       (let ((pred (predicate-form-to-predicate formula)))
	 (and (idpredconst-form? pred)
	      (member
	       (idpredconst-to-name pred)
	       (list ;;"AndNc"
		"AndNc" "AndL" "AndR" "AndD"))))))

(define (andi-mr-andi-form? formula)
  (and (predicate-form? formula)
       (let ((pred (predicate-form-to-predicate formula)))
	 (and (idpredconst-form? pred)
	      (member
	       (idpredconst-to-name pred)
	       (list ;;"AndNc"
		"AndNc" "AndL" "AndR" "AndD"
		"AndNcMR" "AndLMR" "AndRMR" "AndDMR"))))))

(define (andi-mr-andi-form-to-conjuncts formula)
  (if (andi-mr-andi-form? formula)
      (let* ((cterms
	      (idpredconst-to-cterms
	       (predicate-form-to-predicate formula)))
	     (flas (map cterm-to-formula cterms)))
	(cons (car flas)
	      (andi-mr-andi-form-to-conjuncts (cadr flas))))
      (list formula)))

(define (and-andi-mr-andi-form-to-conjuncts formula)
  (cond ((andi-mr-andi-form? formula)
	 (let* ((cterms
		 (idpredconst-to-cterms
		  (predicate-form-to-predicate formula)))
		(flas (map cterm-to-formula cterms)))
	   (cons (car flas)
		 (and-andi-mr-andi-form-to-conjuncts (cadr flas)))))
	((and-form? formula)
	 (cons (and-form-to-left formula)
	       (and-andi-mr-andi-form-to-conjuncts
		(and-form-to-right formula))))
	(else (list formula))))

(define (make-andr-without-truth formula1 formula2)
  (cond ((formula=? formula1 truth) formula2)
	((formula=? formula2 truth) formula1)
	(else (make-andr formula1 formula2))))

(define (make-andl-without-truth formula1 formula2)
  (cond ((formula=? formula1 truth) formula2)
	((formula=? formula2 truth) formula1)
	(else (make-andl formula1 formula2))))

(define (andl-andnc-imp-impnc-all-allnc-form-to-final-left x)
  (cond
   ((or (andl-form? x) (andnc-form? x))
    (andl-andnc-imp-impnc-all-allnc-form-to-final-left
     (if (andl-form? x)
	 (andl-form-to-left x)
	 (andnc-form-to-left x))))
   ((imp-impnc-form? x)
    (andl-andnc-imp-impnc-all-allnc-form-to-final-left
     (imp-impnc-form-to-conclusion x)))
   ((all-allnc-form? x)
    (andl-andnc-imp-impnc-all-allnc-form-to-final-left
     (all-allnc-form-to-kernel x)))
   (else x)))

;; (add-ids (list (list "EqD" (make-arity (py "alpha") (py "alpha"))))
;; 	 '("allnc x^ EqD x^ x^" "GenEqD"))

(define (make-eqd term1 term2)
  (let* ((type1 (term-to-type term1))
         (type2 (term-to-type term2))
	 (equal-idpredconst
	  (if (equal? type1 type2)
	      (make-idpredconst "EqD" (list type1) '())
	      (myerror "make-eqd" "equal types expected" type1 type2))))
    (make-predicate-formula equal-idpredconst term1 term2)))

(define (eqd-form? formula)
  (and (predicate-form? formula)
       (let ((pred (predicate-form-to-predicate formula)))
	 (and (idpredconst? pred)
	      (string=? "EqD"
			(idpredconst-to-name pred))))))

(define (make-bicon bicon formula1 formula2)
  (case bicon
    ((imp) (make-imp formula1 formula2))
    ((impnc) (make-impnc formula1 formula2))
    ((and) (make-and formula1 formula2))
    ((tensor) (make-tensor formula1 formula2))
    ((andd) (make-andd formula1 formula2))
    ((andl) (make-andl formula1 formula2))
    ((andr) (make-andr formula1 formula2))
    ((andnc) (make-andnc formula1 formula2))
    ((ord) (make-ord formula1 formula2))
    ((orl) (make-orl formula1 formula2))
    ((orr) (make-orr formula1 formula2))
    ((oru) (make-oru formula1 formula2))
    ((ornc) (make-ornc formula1 formula2))
    (else (myerror "make-bicon" "binary connective expected" bicon))))

(define (bicon-form? x)
  (or (imp-form? x)
      (impnc-form? x)
      (and-form? x)
      (tensor-form? x)
      (andd-form? x)
      (andl-form? x)
      (andr-form? x)
      (andnc-form? x)
      (ord-form? x)
      (orl-form? x)
      (orr-form? x)
      (oru-form? x)
      (ornc-form? x)))

(define (bicon-form-to-bicon x)
  (cond
   ((imp-form? x) 'imp)
   ((impnc-form? x) 'impnc)
   ((and-form? x) 'and)
   ((tensor-form? x) 'tensor)
   ((andd-form? x) 'andd)
   ((andl-form? x) 'andl)
   ((andr-form? x) 'andr)
   ((andnc-form? x) 'andnc)
   ((ord-form? x) 'ord)
   ((orl-form? x) 'orl)
   ((orr-form? x) 'orr)
   ((oru-form? x) 'oru)
   ((ornc-form? x) 'ornc)
   (else (myerror "bicon-form-to-bicon" "binary connective form expected" x))))

(define (bicon-form-to-nc-bicon x)
  (cond
   ((imp-form? x) 'imp)
   ((impnc-form? x) 'imp)
   ((and-form? x) 'and)
   ((tensor-form? x) 'tensor)
   ((andd-form? x) 'andnc)
   ((andl-form? x) 'andnc)
   ((andr-form? x) 'andnc)
   ((andnc-form? x) 'andnc)
   ((ord-form? x) 'ornc)
   ((orl-form? x) 'ornc)
   ((orr-form? x) 'ornc)
   ((oru-form? x) 'ornc)
   ((ornc-form? x) 'ornc)
   (else (myerror "bicon-form-to-nc-bicon"
		  "binary connective form expected" x))))

(define (bicon-form-to-left x)
  (cond
   ((imp-form? x) (imp-form-to-premise x))
   ((impnc-form? x) (impnc-form-to-premise x))
   ((and-form? x) (and-form-to-left x))
   ((tensor-form? x) (tensor-form-to-left x))
   ((andd-form? x) (andd-form-to-left x))
   ((andl-form? x) (andl-form-to-left x))
   ((andr-form? x) (andr-form-to-left x))
   ((andnc-form? x) (andnc-form-to-left x))
   ((ord-form? x) (ord-form-to-left x))
   ((orl-form? x) (orl-form-to-left x))
   ((orr-form? x) (orr-form-to-left x))
   ((oru-form? x) (oru-form-to-left x))
   ((ornc-form? x) (ornc-form-to-left x))
   (else (myerror "bicon-form-to-left" "binary connective form expected" x))))

(define (bicon-form-to-right x)
  (cond
   ((imp-form? x) (imp-form-to-conclusion x))
   ((impnc-form? x) (impnc-form-to-conclusion x))
   ((and-form? x) (and-form-to-right x))
   ((tensor-form? x) (tensor-form-to-right x))
   ((andd-form? x) (andd-form-to-right x))
   ((andl-form? x) (andl-form-to-right x))
   ((andr-form? x) (andr-form-to-right x))
   ((andnc-form? x) (andnc-form-to-right x))
   ((ord-form? x) (ord-form-to-right x))
   ((orl-form? x) (orl-form-to-right x))
   ((orr-form? x) (orr-form-to-right x))
   ((oru-form? x) (oru-form-to-right x))
   ((ornc-form? x) (ornc-form-to-right x))
   (else (myerror "bicon-form-to-right" "binary connective form expected" x))))

;; Occasionally it is useful to have constructors for quantified
;; formulas accepting lists of variables.

(define (make-quant quant vars kernel)
  (case quant
    ((all) (make-all (car vars) kernel))
    ((ex) (make-ex (car vars) kernel))
    ((allnc) (make-allnc (car vars) kernel))
    ((exd) (make-exd (car vars) kernel))
    ((exl) (make-exl (car vars) kernel))
    ((exr) (make-exr (car vars) kernel))
    ((exnc) (make-exnc (car vars) kernel))
    ((exdt) (make-exdt (car vars) kernel))
    ((exlt) (make-exlt (car vars) kernel))
    ((exrt) (make-exrt (car vars) kernel))
    ((exnct) (make-exnct (car vars) kernel))
    ((exca) (make-exca vars kernel))
    ((excl) (make-excl vars kernel))
    ((excu) (make-excu vars kernel))
    (else "make-quant" "quantifier expected" quant)))

(define (mk-quant x . rest) ;x list consisting of quant and vars
  (if (null? rest)
      x
      (if (and (list? x) (= 2 (length x)))
	  (let ((quant (car x))
		(vars (cadr x)))
	    (make-quant quant vars (apply mk-quant rest)))
	  (myerror "mk-quant" "list of quant and vars expected" x))))

(define (quant-form? x)
  (or (all-form? x)
      (ex-form? x)
      (allnc-form? x)
      (exd-form? x)
      (exl-form? x)
      (exr-form? x)
      (exnc-form? x)
      (exdt-form? x)
      (exlt-form? x)
      (exrt-form? x)
      (exnct-form? x)
      (exca-form? x)
      (excl-form? x)
      (excu-form? x)))

(define (quant-form-to-quant x)
  (cond
   ((all-form? x) 'all)
   ((ex-form? x) 'ex)
   ((allnc-form? x) 'allnc)
   ((exd-form? x) 'exd)
   ((exl-form? x) 'exl)
   ((exr-form? x) 'exr)
   ((exnc-form? x) 'exnc)
   ((exdt-form? x) 'exdt)
   ((exlt-form? x) 'exlt)
   ((exrt-form? x) 'exrt)
   ((exnct-form? x) 'exnct)
   ((exca-form? x) 'exca)
   ((excl-form? x) 'excl)
   ((excu-form? x) 'excu)
   (else "quant-form-to-quant" "quantifier form expected" x)))

(define (quant-form-to-nc-quant x)
  (cond
   ((all-form? x) 'all)
   ((allnc-form? x) 'all)
   ((exd-form? x) 'exnc)
   ((exl-form? x) 'exnc)
   ((exr-form? x) 'exnc)
   ((exnc-form? x) 'exnc)
   ((exdt-form? x) 'exnct)
   ((exlt-form? x) 'exnct)
   ((exrt-form? x) 'exnct)
   ((exnct-form? x) 'exnct)
   ((exca-form? x) 'exca)
   ((excl-form? x) 'excl)
   (else (myerror "quant-form-to-nc-quant"
		  "quantifier form expected" x))))

(define (quant-form-to-vars x)
  (cond
   ((all-form? x) (list (all-form-to-var x)))
   ((ex-form? x) (list (ex-form-to-var x)))
   ((allnc-form? x) (list (allnc-form-to-var x)))
   ((exd-form? x) (list (exd-form-to-var x)))
   ((exl-form? x) (list (exl-form-to-var x)))
   ((exr-form? x) (list (exr-form-to-var x)))
   ((exnc-form? x) (list (exnc-form-to-var x)))
   ((exdt-form? x) (list (exdt-form-to-var x)))
   ((exlt-form? x) (list (exlt-form-to-var x)))
   ((exrt-form? x) (list (exrt-form-to-var x)))
   ((exnct-form? x) (list (exnct-form-to-var x)))
   ((exca-form? x) (exca-form-to-vars x))
   ((excl-form? x) (excl-form-to-vars x))
   ((excu-form? x) (excu-form-to-vars x))
   (else "quant-form-to-vars" "quantifier form expected" x)))

(define (quant-form-to-kernel x)
  (cond
   ((all-form? x) (all-form-to-kernel x))
   ((ex-form? x) (ex-form-to-kernel x))
   ((allnc-form? x) (allnc-form-to-kernel x))
   ((exd-form? x) (exd-form-to-kernel x))
   ((exl-form? x) (exl-form-to-kernel x))
   ((exr-form? x) (exr-form-to-kernel x))
   ((exnc-form? x) (exnc-form-to-kernel x))
   ((exdt-form? x) (exdt-form-to-kernel x))
   ((exlt-form? x) (exlt-form-to-kernel x))
   ((exrt-form? x) (exrt-form-to-kernel x))
   ((exnct-form? x) (exnct-form-to-kernel x))
   ((exca-form? x) (exca-form-to-kernel x))
   ((excl-form? x) (excl-form-to-kernel x))
   ((excu-form? x) (excu-form-to-kernel x))
   (else "quant-form-to-kernel" "quantifier form expected" x)))

(define (or-form-to-disjuncts formula . x)
  (cond
   ((null? x)
    (if (and (bicon-form? formula)
	     (memq (bicon-form-to-bicon formula) '(ord orl orr oru ornc)))
	(cons (bicon-form-to-left formula)
	      (or-form-to-disjuncts (bicon-form-to-right formula)))
	(list formula)))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((fla formula (bicon-form-to-right fla))
	   (i 0 (+ 1 i))
	   (res '() (cons (bicon-form-to-left fla) res)))
	  ((or (= n i) (not (and (bicon-form? fla)
				 (memq (bicon-form-to-bicon fla)
				       '(ord orl orr oru ornc)))))
	   (if (= n i)
	       (reverse res)
	       (myerror "or-form-to-disjuncts" n "disjuncts expected in"
			formula))))))
   (else (myerror "or-form-to-disjuncts" "non-negative integer expected"
		  (car x)))))

(define (prime-predicate-form? x)
  (and (predicate-form? x)
       (not (bicon-form? x))
       (not (quant-form? x))))

(define (prime-form? x)
  (or (atom-form? x) (prime-predicate-form? x)))

(define (quant-prime-form? formula)
  (or (prime-form? formula)
      (and (quant-form? formula)
	   (quant-prime-form? (quant-form-to-kernel formula)))))

(define (quant-free? formula)
  (or (atom-form? formula)
      (and (predicate-form? formula)
	   (not (bicon-form? formula))
	   (not (quant-form? formula)))
      (and (bicon-form? formula)
	   (quant-free? (bicon-form-to-left formula))
	   (quant-free? (bicon-form-to-right formula)))))

(define (formula-to-head formula)
  (cond
   ((prime-form? formula) formula)
   ((and (bicon-form? formula)
	 (memq (bicon-form-to-bicon formula) '(imp impnc)))
    (formula-to-head (bicon-form-to-right formula)))
   ((and (quant-form? formula)
	 (memq (quant-form-to-quant formula) '(all allnc)))
    (formula-to-head (quant-form-to-kernel formula)))
   (else (myerror
	  "formula-to-head" "prime, imp, impnc, all or allnc formula expected"
	  formula))))

(define (formula-to-nc-formula formula)
  (cond
   ((atom-form? formula) formula)
   ((prime-predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula))
	  (args (predicate-form-to-args formula)))
      (cond ((pvar-form? pred)
	     (if (formula=? falsity-log formula)
		 falsity
		 (apply make-predicate-formula
			(PVAR-TO-NC-PVAR pred)
			args)))
	    ((predconst-form? pred)
	     (cond ((string=? "Total" (predconst-to-name pred))
		    (term-to-totalnc-formula (car args)))
		   ((string=? "TotalNc" (predconst-to-name pred))
		    (term-to-totalnc-formula (car args)))
		   ((string=? "CoTotal" (predconst-to-name pred))
		    (term-to-cototalnc-formula (car args)))
		   ((string=? "CoTotalNc" (predconst-to-name pred))
		    (term-to-cototalnc-formula (car args)))
		   (else formula)))
	    ((idpredconst-form? pred)
	     (let* ((name (idpredconst-to-name pred))
		    (opt-alg-name (idpredconst-name-to-opt-alg-name name)))
	       (if (or (null? opt-alg-name)
		       (equal? (make-tconst "nulltype")
			       (idpredconst-to-et-type pred)))
		   formula
		   (apply make-predicate-formula
			  (idpredconst-to-nc-idpredconst pred)
			  args)))))))
   ((bicon-form? formula)
    (make-bicon (bicon-form-to-nc-bicon formula)
		(formula-to-nc-formula (bicon-form-to-left formula))
		(formula-to-nc-formula (bicon-form-to-right formula))))
   ((quant-form? formula)
    (let* ((quant (quant-form-to-quant formula))
	   (vars (quant-form-to-vars formula))
	   (kernel (quant-form-to-kernel formula)))
      (make-quant
       (quant-form-to-nc-quant formula)
       vars (formula-to-nc-formula kernel))))
   (else (myerror "formula-to-nc-formula" "formula expected" formula))))

(define (unfold-formula formula)
  (cond
   ((atom-form? formula) formula)
   ((prime-predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula))
	  (args (predicate-form-to-args formula)))
      (cond ((pvar-form? pred) formula)
	    ((predconst-form? pred)
	     (cond ((string=? "Total" (predconst-to-name pred))
		    (term-to-totality-formula (car args)))
		   ((string=? "TotalNc" (predconst-to-name pred))
		    (term-to-totalnc-formula (car args)))
		   ((string=? "CoTotal" (predconst-to-name pred))
		    (term-to-cototality-formula (car args)))
		   ((string=? "CoTotalNc" (predconst-to-name pred))
		    (term-to-cototalnc-formula (car args)))
		   ((string=? "TotalMR" (predconst-to-name pred))
		    (apply terms-to-mr-totality-formula args))
		   ((string=? "CoTotalMR" (predconst-to-name pred))
		    (apply terms-to-mr-cototality-formula args))
		   ((string=? "EqP" (predconst-to-name pred))
		    (terms-to-pure-eqp-formula (car args) (cadr args)))
		   ((string=? "EqPNc" (predconst-to-name pred))
		    (terms-to-pure-eqpnc-formula (car args) (cadr args)))
		   ((string=? "CoEqP" (predconst-to-name pred))
		    (terms-to-pure-eqp-formula
		     (car args) (cadr args)
		     (type-to-cotype (term-to-type (car args)))))
		   ((string=? "CoEqPNc" (predconst-to-name pred))
		    (terms-to-pure-eqpnc-formula
		     (car args) (cadr args)
		     (type-to-cotype (term-to-type (car args)))))
		   ((string=? "EqPMR" (predconst-to-name pred))
		    (apply terms-to-pure-mr-eqp-formula args))
		   ((string=? "CoEqPMR" (predconst-to-name pred))
		    (terms-to-pure-mr-eqp-formula
		     (car args) (cadr args) (caddr args)
		     (type-to-cotype (term-to-type (car args)))))
		   (else formula)))
	    ;; ((string=? "EqPMR" (predconst-to-name pred))
	    ;;  (apply terms-to-mr-eqp-formula args))
	    ;; ((string=? "CoEqPMR" (predconst-to-name pred))
	    ;;  (apply terms-to-mr-coeqp-formula args))))
	    ((idpredconst-form? pred)
	     (let* ((name (idpredconst-to-name pred))
		    (types (idpredconst-to-types pred))
		    (cterms (idpredconst-to-cterms pred))
		    (unfolded-cterms (map unfold-cterm cterms))
		    (unfolded-idpc
		     (idpredconst-name-and-types-and-cterms-to-idpredconst
		      name types unfolded-cterms)))
	       (apply make-predicate-formula unfolded-idpc args)))
	    ;; ((idpredconst-form? pred) formula)
	    (else (myerror "unfold-formula"
			   "predicate expected" pred)))))
   ((bicon-form? formula)
    (make-bicon (bicon-form-to-bicon formula)
		(unfold-formula (bicon-form-to-left formula))
		(unfold-formula (bicon-form-to-right formula))))
   ((quant-form? formula)
    (let ((quant (quant-form-to-quant formula))
	  (vars (quant-form-to-vars formula))
	  (kernel (quant-form-to-kernel formula)))
      (case quant
	((all ex allnc exd exl exr exnc exdt exlt exrt exnct)
	 (make-quant quant vars (unfold-formula kernel)))
	((exca)
	 (mk-neg
	  (apply
	   mk-all
	   (append vars (list (apply mk-imp (append (map unfold-formula
							 (tensor-form-to-parts
							  kernel))
						    (list falsity))))))))
	((excl)
	 (mk-neg-log
	  (apply
	   mk-all
	   (append vars (list (apply mk-imp (append (map unfold-formula
							 (tensor-form-to-parts
							  kernel))
						    (list falsity-log))))))))
	((excu)
	 (mk-neg-log
	  (apply
	   mk-allnc
	   (append vars (list (apply mk-imp (append (map unfold-formula
							 (tensor-form-to-parts
							  kernel))
						    (list falsity-log))))))))
	(else (myerror "unfold-formula" "quantifier form expected" quant)))))
   (else (myerror "unfold-formula" "formula expected" formula))))

(define PVAR-TO-NC-PVAR-ALIST '())

(define (PVAR-TO-NC-PVAR pvar)
  (let ((info (assoc pvar PVAR-TO-NC-PVAR-ALIST)))
    (if info
	(cadr info)
	(let* ((arity (pvar-to-arity pvar))
	       (newpvar (arity-to-new-harrop-pvar arity)))
	  (set! PVAR-TO-NC-PVAR-ALIST
		(cons (list pvar newpvar) PVAR-TO-NC-PVAR-ALIST))
	  newpvar))))

(define (idpredconst-to-nc-idpredconst idpc)
  (let* ((name (idpredconst-to-name idpc))
	 (nc-name (string-append name "Nc"))
	 (info (assoc nc-name IDS)))
    (if info
	(let* ((types (idpredconst-to-types idpc))
	       (cterms (idpredconst-to-cterms idpc)))
	  (make-idpredconst nc-name types cterms))
	(myerror "idpredconst-to-nc-idpredconst" "idpredconst name expected"
		 nc-name))))

(define (fold-formula formula)
  (cond ((prime-form? formula) formula)
	((foldable-exca-form? formula)
	 (let* ((prem (imp-form-to-premise formula))
		(vars-and-final-kernel
		 (all-form-to-vars-and-final-kernel prem))
		(vars (car vars-and-final-kernel))
		(kernel (cadr vars-and-final-kernel)))
	   (make-exca vars
		      (apply mk-tensor
			     (map fold-formula
				  (imp-form-to-premises kernel))))))
	((foldable-excl-form? formula)
	 (let* ((prem (imp-form-to-premise formula))
		(vars-and-final-kernel
		 (all-form-to-vars-and-final-kernel prem))
		(vars (car vars-and-final-kernel))
		(kernel (cadr vars-and-final-kernel)))
	   (make-excl vars
		      (apply mk-tensor
			     (map fold-formula
				  (imp-form-to-premises kernel))))))
	((foldable-excu-form? formula)
	 (let* ((prem (imp-form-to-premise formula))
		(vars-and-final-kernel
		 (allnc-form-to-vars-and-final-kernel prem))
		(vars (car vars-and-final-kernel))
		(kernel (cadr vars-and-final-kernel)))
	   (make-excu vars
		      (apply mk-tensor
			     (map fold-formula
				  (imp-form-to-premises kernel))))))
	((bicon-form? formula)
	 (make-bicon
	  (bicon-form-to-bicon formula)
	  (fold-formula (bicon-form-to-left formula))
	  (fold-formula (bicon-form-to-right formula))))
	((quant-form? formula)
	 (make-quant (quant-form-to-quant formula)
		     (quant-form-to-vars formula)
		     (fold-formula (quant-form-to-kernel formula))))
	(else (myerror "fold-formula" "formula expected" formula))))

(define (foldable-exca-form? formula)
  (and
   (imp-form? formula) (equal? falsity (imp-form-to-conclusion formula))
   (let ((prem (imp-form-to-premise formula)))
     (and (all-form? prem)
	  (let ((kernel (cadr (all-form-to-vars-and-final-kernel prem))))
	    (and (imp-form? kernel)
		 (equal? falsity (imp-form-to-final-conclusion kernel))))))))

(define (foldable-excl-form? formula)
  (and
   (imp-form? formula)
   (equal? falsity-log (imp-form-to-conclusion formula))
   (let ((prem (imp-form-to-premise formula)))
     (and (all-form? prem)
	  (let ((kernel (all-form-to-final-kernel prem)))
	    (and (imp-form? kernel)
		 (equal? falsity-log
			 (imp-form-to-final-conclusion kernel))))))))

(define (foldable-excu-form? formula)
  (and
   (imp-form? formula)
   (equal? falsity-log (imp-form-to-conclusion formula))
   (let ((prem (imp-form-to-premise formula)))
     (and (allnc-form? prem)
	  (let ((kernel (allnc-form-to-final-kernel prem)))
	    (and (imp-form? kernel)
		 (equal? falsity-log
			 (imp-form-to-final-conclusion kernel))))))))

;; The tensor ! is used with classical existential quantifiers only.
;; Hence it should not appear in unfolded formulas.

(define (formula-with-illegal-tensor? formula)
  (cond
   ((prime-form? formula) #f)
   ((bicon-form? formula)
    (or (eq? 'tensor (bicon-form-to-bicon formula))
	(formula-with-illegal-tensor? (bicon-form-to-left formula))
	(formula-with-illegal-tensor? (bicon-form-to-right formula))))
   ((and (quant-form? formula)
	 (memq (quant-form-to-quant formula)
	       '(all ex allnc exd exl exr exnc exdt exlt exrt exnct)))
    (formula-with-illegal-tensor? (quant-form-to-kernel formula)))
   (else (myerror "formula-with-illegal-tensor?"
		  "unfolded formula expected" formula))))

(define (totality-predicate? predicate)
  (or
   (and (predconst-form? predicate)
	(member (predconst-to-name predicate) (list "Total" "TotalMR")))
   (and
    (idpredconst-form? predicate)
    (let* ((idpc-name (idpredconst-to-name predicate))
	   (cterms (idpredconst-to-cterms predicate)))
      (and
       (or (string-prefix? "Total" idpc-name)
	   (string-prefix? "RTotal" idpc-name)
	   (string-prefix? "RFTotal" idpc-name)
	   (string-prefix? "RLTotal" idpc-name))
       (not (string-suffix? idpc-name "MR"))
       (apply
	and-op
	(map (lambda (cterm) ;{x|Px} with P totality predicate
	       (let ((vars (cterm-to-vars cterm))
		     (formula (cterm-to-formula cterm)))
		 (and (= 1 (length vars))
		      (predicate-form? formula)
		      (equal? (map make-term-in-var-form vars)
			      (predicate-form-to-args formula))
		      (totality-predicate?
		       (predicate-form-to-predicate formula)))))
	     cterms)))))))

(define (unfold-totality formula)
  (cond
   ((atom-form? formula) formula)
   ((prime-predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula))
	  (args (predicate-form-to-args formula)))
      (cond ((totality-predicate? pred)
	     (term-to-unfolded-totality-formula (car args)))
	    (else formula))))
   ((bicon-form? formula)
    (make-bicon (bicon-form-to-bicon formula)
		(unfold-totality (bicon-form-to-left formula))
		(unfold-totality (bicon-form-to-right formula))))
   ((quant-form? formula)
    (let ((quant (quant-form-to-quant formula))
	  (vars (quant-form-to-vars formula))
	  (kernel (quant-form-to-kernel formula)))
      (case quant
	((all ex allnc exd exl exr exnc exdt exlt exrt exnct)
	 (make-quant quant vars (unfold-totality kernel)))
	((exca)
	 (mk-neg
	  (apply
	   mk-all
	   (append vars (list (apply mk-imp (append (map unfold-totality
							 (tensor-form-to-parts
							  kernel))
						    (list falsity))))))))
	((excl)
	 (mk-neg-log
	  (apply
	   mk-all
	   (append vars (list (apply mk-imp (append (map unfold-totality
							 (tensor-form-to-parts
							  kernel))
						    (list falsity-log))))))))
	((excu)
	 (mk-neg-log
	  (apply
	   mk-allnc
	   (append vars (list (apply mk-imp (append (map unfold-totality
							 (tensor-form-to-parts
							  kernel))
						    (list falsity-log))))))))
	(else (myerror "unfold-totality" "quantifier form expected" quant)))))
   (else (myerror "unfold-totality" "formula expected" formula))))

;; Moreover we need

(define (formula-of-one-clause-nc-idpredconst? formula)
  (or (and (imp-impnc-form? formula)
	   (formula-of-one-clause-nc-idpredconst?
	    (imp-impnc-form-to-conclusion formula)))
      (and (allnc-form? formula)
	   (formula-of-one-clause-nc-idpredconst?
	    (allnc-form-to-kernel formula)))
      (and (all-form? formula) ;all x^ understood as allnc x^
	   (t-deg-zero? (var-to-t-deg (all-form-to-var formula)))
	   (formula-of-one-clause-nc-idpredconst?
	    (all-form-to-kernel formula)))
      (and (predicate-form? formula)
	   (pvar-form? (predicate-form-to-predicate formula)))))

(define (formula-to-free formula)
  (cond
   ((atom-form? formula) (term-to-free (atom-form-to-kernel formula)))
   ((predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula)))
      (cond
       ((or (pvar-form? pred) (predconst-form? pred))
	(apply union (map term-to-free (predicate-form-to-args formula))))
       ((idpredconst-form? pred)
	(let ((cterms (idpredconst-to-cterms pred)))
	  (apply union
		 (append (map term-to-free (predicate-form-to-args formula))
			 (map cterm-to-free cterms)))))
       (else (myerror "formula-to-free" "predicate expected" pred)))))
   ((bicon-form? formula)
    (union (formula-to-free (bicon-form-to-left formula))
	   (formula-to-free (bicon-form-to-right formula))))
   ((quant-form? formula)
    (set-minus (formula-to-free (quant-form-to-kernel formula))
	       (quant-form-to-vars formula)))
   (else (myerror "formula-to-free" "formula expected" formula))))

(define (formula-to-bound formula)
  (cond
   ((atom-form? formula) (term-to-bound (atom-form-to-kernel formula)))
   ((predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula)))
      (cond
       ((or (pvar-form? pred) (predconst-form? pred))
	(apply union (map term-to-bound (predicate-form-to-args formula))))
       ((idpredconst-form? pred)
	(let ((cterms (idpredconst-to-cterms pred)))
	  (apply
	   union
	   (append (map cterm-to-bound cterms)
		   (map term-to-bound (predicate-form-to-args formula))))))
       (else (myerror "formula-to-bound" "predicate expected" pred)))))
   ((bicon-form? formula)
    (union (formula-to-bound (bicon-form-to-left formula))
	   (formula-to-bound (bicon-form-to-right formula))))
   ((quant-form? formula)
    (union (formula-to-bound (quant-form-to-kernel formula))
	   (quant-form-to-vars formula)))
   (else (myerror "formula-to-bound" "formula expected" formula))))

(define (formula-to-tvars formula)
  (cond
   ((atom-form? formula) (term-to-tvars (atom-form-to-kernel formula)))
   ((predicate-form? formula)
    (apply union
	   (predicate-to-tvars (predicate-form-to-predicate formula))
	   (map term-to-tvars (predicate-form-to-args formula))))
   ((bicon-form? formula)
    (union (formula-to-tvars (bicon-form-to-left formula))
	   (formula-to-tvars (bicon-form-to-right formula))))
   ((quant-form? formula)
    (let* ((vars (quant-form-to-vars formula))
	   (kernel (quant-form-to-kernel formula)))
      (apply union (append (map (lambda (x) (type-to-tvars (var-to-type x)))
				vars)
			   (list (formula-to-tvars kernel))))))
   (else (myerror "formula-to-tvars" "formula expected" formula))))

(define (formula-to-pvars formula)
  (cond
   ((atom-form? formula) '())
   ((predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula)))
      (cond
       ((pvar-form? pred) (list pred))
       ((predconst-form? pred) '())
       ((idpredconst-form? pred)
	(let* ((cterms (idpredconst-to-cterms pred))
	       (formulas (map cterm-to-formula cterms)))
	  (apply union (map formula-to-pvars formulas))))
       (else (myerror "formula-to-pvars" "predicate expected" pred)))))
   ((bicon-form? formula)
    (union (formula-to-pvars (bicon-form-to-left formula))
	   (formula-to-pvars (bicon-form-to-right formula))))
   ((quant-form? formula)
    (formula-to-pvars (quant-form-to-kernel formula)))
   (else (myerror "formula-to-pvars" "formula expected" formula))))

(define (formula-to-spos-pvars formula)
  (cond
   ((atom-form? formula) '())
   ((predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula)))
      (cond
       ((pvar-form? pred) (list pred))
       ((predconst-form? pred) '())
       ((idpredconst-form? pred) (idpredconst-to-spos-pvars pred))
       (else (myerror "formula-to-spos-pvars" "predicate expected" pred)))))
   ((imp-impnc-form? formula)
    (formula-to-spos-pvars (imp-impnc-form-to-conclusion formula)))
   ((and-form? formula)
    (union (formula-to-spos-pvars (and-form-to-left formula))
	   (formula-to-spos-pvars (and-form-to-right formula))))
   ((all-allnc-form? formula)
    (formula-to-spos-pvars (all-allnc-form-to-kernel formula)))
   ((ex-form? formula)
    (formula-to-spos-pvars (ex-form-to-kernel formula)))
   (else (myerror "formula-to-spos-pvars" "formula expected" formula))))

(define (formula-to-idpredconst-names formula)
  (cond
   ((atom-form? formula) '())
   ((predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula)))
      (cond
       ((pvar-form? pred) '())
       ((predconst-form? pred) '())
       ((idpredconst-form? pred)
	(let* ((cterms (idpredconst-to-cterms pred))
	       (formulas (map cterm-to-formula cterms)))
	  (adjoin (idpredconst-to-name pred)
		  (apply union (map formula-to-idpredconst-names formulas)))))
       (else (myerror "formula-to-idpredconst-names"
		      "predicate expected" pred)))))
   ((bicon-form? formula)
    (union (formula-to-idpredconst-names (bicon-form-to-left formula))
	   (formula-to-idpredconst-names (bicon-form-to-right formula))))
   ((quant-form? formula)
    (formula-to-idpredconst-names (quant-form-to-kernel formula)))
   (else (myerror "formula-to-idpredconst-names" "formula expected" formula))))

;; (formula-to-idpredconst-names (pf "exd boole T ord F andl T"))
;; ("OrD" "ExDT" "AndL")

(define (formula-to-depth formula)
  (cond
   ((atom-form? formula)
    (term-to-depth (atom-form-to-kernel formula)))
   ((bicon-form? formula)
    (+ 1 (max (formula-to-depth (bicon-form-to-left formula))
	      (formula-to-depth (bicon-form-to-right formula)))))
   ((quant-form? formula)
    (+ 1 (formula-to-depth (quant-form-to-kernel formula))))
   ((predicate-form? formula)
    (let* ((predicate (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula))
	   (arg-depths (map term-to-depth args))
	   (m (if (null? arg-depths) 0 (apply max arg-depths)))
	   (cterms (if (idpredconst-form? predicate)
		       (idpredconst-to-cterms predicate)
		       '()))
	   (formulas (map cterm-to-formula cterms))
	   (formula-depths (map formula-to-depth formulas))
	   (n (if (null? formula-depths) 0 (apply max formula-depths))))
      (+ 1 (max m n))))
   (else (myerror "formula-to-depth" "formula expected" formula))))

(define (ex-free-formula? formula)
  (cond
   ((prime-form? formula) #t)
   ((bicon-form? formula)
    (and (ex-free-formula? (bicon-form-to-left formula))
	 (ex-free-formula? (bicon-form-to-right formula))))
   ((quant-form? formula)
    (and (not (memq (quant-form-to-quant formula)
		    '(ex exd exl exr exnc exdt exlt exrt exnct)))
	 (ex-free-formula? (quant-form-to-kernel formula))))
   (else (myerror "ex-free-formula?" "formula expected" formula))))

;; nbe-formula-to-type needs a procedure associating type variables to
;; predicate variables, which remembers the assignment done so far.
;; Therefore it refers to the global variable PVAR-TO-TVAR.  This
;; machinery will be used to assign recursion constants to induction
;; constants.  There we need to associate type variables with predicate
;; variables, in such a way that we can later refer to this assignment.

(define (nbe-formula-to-type formula)
  (cond
   ((atom-form? formula) (make-tconst "atomic"))
   ((predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula)))
      (cond
       ((pvar-form? pred) (PVAR-TO-TVAR pred))
       ((predconst-form? pred) (make-tconst "prop"))
       ((idpredconst-form? pred)
	(let* ((idpc-or-coidpc-name (idpredconst-to-name pred))
	       (name (if (assoc idpc-or-coidpc-name COIDS)
			 (substring idpc-or-coidpc-name
				    2 (string-length idpc-or-coidpc-name))
			 idpc-or-coidpc-name))
	       (types (idpredconst-to-types pred))
	       (param-cterms (idpredconst-to-cterms pred))
	       (param-cterm-types
		(map nbe-formula-to-type
		     (map cterm-to-formula param-cterms)))
	       (nbe-alg-name (idpredconst-name-to-nbe-alg-name name)))
	  (apply make-alg nbe-alg-name (append types param-cterm-types)))))))
   ((or (imp-form? formula) (impnc-form? formula))
    (make-arrow (nbe-formula-to-type (bicon-form-to-left formula))
		(nbe-formula-to-type (bicon-form-to-right formula))))
   ((and-form? formula)
    (make-star (nbe-formula-to-type (bicon-form-to-left formula))
	       (nbe-formula-to-type (bicon-form-to-right formula))))
   ((tensor-form? formula)
    (make-alg "ytensor"
	      (nbe-formula-to-type (tensor-form-to-left formula))
	      (nbe-formula-to-type (tensor-form-to-right formula))))
   ((or (all-form? formula) (allnc-form? formula))
    (make-arrow (var-to-type (car (quant-form-to-vars formula)))
		(nbe-formula-to-type (quant-form-to-kernel formula))))
   ((ex-form? formula) (make-tconst "existential"))
   ((and (quant-form? formula)
	 (memq (quant-form-to-quant formula) '(exca excl excu)))
    (nbe-formula-to-type (unfold-formula formula)))
   (else (myerror "nbe-formula-to-type" "formula expected" formula))))

(define (formula-to-prime-subformulas formula)
  (cond
   ((prime-form? formula) (list formula))
   ((bicon-form? formula)
    (union (formula-to-prime-subformulas (bicon-form-to-left formula))
	   (formula-to-prime-subformulas (bicon-form-to-right formula))))
   ((quant-form? formula)
    (formula-to-prime-subformulas (quant-form-to-kernel formula)))
   (else (myerror "formula-to-prime-subformulas" "formula expected"
		  formula))))

(define (formula-to-positive-existential-subformulas formula)
  (cond
   ((prime-form? formula) '())
   ((bicon-form? formula)
    (if (or (imp-form? formula) (impnc-form? formula))
	(union (formula-to-negative-existential-subformulas
		(bicon-form-to-left formula))
	       (formula-to-positive-existential-subformulas
		(bicon-form-to-right formula)))
	(union (formula-to-positive-existential-subformulas
		(bicon-form-to-left formula))
	       (formula-to-positive-existential-subformulas
		(bicon-form-to-right formula)))))
   ((and (quant-form? formula)
	 (memq (quant-form-to-quant formula)
	       '(all allnc exca excl excu)))
    (formula-to-positive-existential-subformulas
     (quant-form-to-kernel formula)))
   ((and (quant-form? formula)
	 (memq (quant-form-to-quant formula)
	       '(ex exd exl exr exnc exdt exlt exrt exnct)))
    (cons formula
	  (formula-to-positive-existential-subformulas
	   (quant-form-to-kernel formula))))
   (else (myerror
	  "formula-to-positive-existential-subformulas" "formula expected"
	  formula))))

(define (formula-to-negative-existential-subformulas formula)
  (cond
   ((prime-form? formula) '())
   ((bicon-form? formula)
    (if (or (imp-form? formula) (impnc-form? formula))
	(union (formula-to-positive-existential-subformulas
		(bicon-form-to-left formula))
	       (formula-to-negative-existential-subformulas
		(bicon-form-to-right formula)))
	(union (formula-to-negative-existential-subformulas
		(bicon-form-to-left formula))
	       (formula-to-negative-existential-subformulas
		(bicon-form-to-right formula)))))
   ((and (quant-form? formula)
	 (memq (quant-form-to-quant formula)
	       '(all allnc exca excl excu)))
    (formula-to-negative-existential-subformulas
     (quant-form-to-kernel formula)))
   ((and (quant-form? formula)
	 (memq (quant-form-to-quant formula)
	       '(ex exd exl exr exnc exdt exlt exrt exnct)))
    (cons formula
	  (formula-to-negative-existential-subformulas
	   (quant-form-to-kernel formula))))
   (else (myerror
	  "formula-to-negative-existential-subformulas" "formula expected"
	  formula))))

(define (formula-to-beta-nf formula)
  (cond
   ((atom-form? formula)
    (make-atomic-formula (term-to-beta-nf (atom-form-to-kernel formula))))
   ((predicate-form? formula)
    (let* ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula))
	   (npred (if (idpredconst-form? pred)
		      (let ((name (idpredconst-to-name pred))
			    (types (idpredconst-to-types pred))
			    (cterms (idpredconst-to-cterms pred)))
			(make-idpredconst
			 name types (map cterm-to-beta-nf cterms)))
		      pred))
	   (nargs (map term-to-beta-nf args)))
      (apply make-predicate-formula npred nargs)))
   ((bicon-form? formula)
    (make-bicon
     (bicon-form-to-bicon formula)
     (formula-to-beta-nf (bicon-form-to-left formula))
     (formula-to-beta-nf (bicon-form-to-right formula))))
   ((quant-form? formula)
    (make-quant
     (quant-form-to-quant formula)
     (quant-form-to-vars formula)
     (formula-to-beta-nf (quant-form-to-kernel formula))))
   (else (myerror "formula-to-beta-nf" "formula expected" formula))))

(define (cterm-to-beta-nf cterm)
  (let ((vars (cterm-to-vars cterm))
	(formula (cterm-to-formula cterm)))
    (apply make-cterm (append vars (list (formula-to-beta-nf formula))))))

(define (formula-to-eta-nf formula)
  (cond
   ((atom-form? formula)
    (make-atomic-formula (term-to-eta-nf (atom-form-to-kernel formula))))
   ((predicate-form? formula)
    (let* ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula))
	   (npred (if (idpredconst-form? pred)
		      (let ((name (idpredconst-to-name pred))
			    (types (idpredconst-to-types pred))
			    (cterms (idpredconst-to-cterms pred)))
			(make-idpredconst
			 name types (map cterm-to-eta-nf cterms)))
		      pred))
	   (nargs (map term-to-eta-nf args)))
      (apply make-predicate-formula npred nargs)))
   ((bicon-form? formula)
    (make-bicon
     (bicon-form-to-bicon formula)
     (formula-to-eta-nf (bicon-form-to-left formula))
     (formula-to-eta-nf (bicon-form-to-right formula))))
   ((quant-form? formula)
    (make-quant
     (quant-form-to-quant formula)
     (quant-form-to-vars formula)
     (formula-to-eta-nf (quant-form-to-kernel formula))))
   (else (myerror "formula-to-eta-nf" "formula expected" formula))))

(define (cterm-to-eta-nf cterm)
  (let ((vars (cterm-to-vars cterm))
	(formula (cterm-to-formula cterm)))
    (apply make-cterm (append vars (list (formula-to-eta-nf formula))))))

(define (formula-to-beta-eta-nf formula)
  (formula-to-eta-nf (formula-to-beta-nf formula)))

(define (cterm-to-beta-eta-nf cterm)
  (cterm-to-eta-nf (cterm-to-beta-nf cterm)))

(define (qf-to-term formula)
  (cond
   ((atom-form? formula) (atom-form-to-kernel formula))
   ((prime-predicate-form? formula)
    (if (formula=? falsity-log formula)
	(make-term-in-const-form false-const)
	(myerror "qf-to-term" "unexpected predicate"
		 formula)))
   ((imp-impnc-form? formula)
    (mk-term-in-app-form
     (make-term-in-const-form imp-const)
     (qf-to-term (bicon-form-to-left formula))
     (qf-to-term (bicon-form-to-right formula))))
   ((or (and-form? formula)
	(andd-form? formula)
	(andl-form? formula)
	(andr-form? formula)
	(andnc-form? formula))
    (mk-term-in-app-form
     (make-term-in-const-form and-const)
     (qf-to-term (bicon-form-to-left formula))
     (qf-to-term (bicon-form-to-right formula))))
   ((or (ord-form? formula)
	(orl-form? formula)
	(orr-form? formula)
	(oru-form? formula)
	(ornc-form? formula))
    (mk-term-in-app-form
     (make-term-in-const-form or-const)
     (qf-to-term (bicon-form-to-left formula))
     (qf-to-term (bicon-form-to-right formula))))
   (else (myerror "qf-to-term" "quantifier free formula expected"
		  formula))))

(define (alpha-equal-formulas-to-renaming formula1 formula2)
  (cond
   ((and (prime-form? formula1) (prime-form? formula2)) '())
   ((and (bicon-form? formula1) (bicon-form? formula2)
	 (equal? (bicon-form-to-bicon formula1)
		 (bicon-form-to-bicon formula2)))
    (append (alpha-equal-formulas-to-renaming
	     (bicon-form-to-left formula1)
	     (bicon-form-to-left formula2))
	    (alpha-equal-formulas-to-renaming
	     (bicon-form-to-right formula1)
	     (bicon-form-to-right formula2))))
   ((and
     (quant-form? formula1) (quant-form? formula2)
     (equal? (quant-form-to-quant formula1) (quant-form-to-quant formula2)))
    (let ((vars1 (quant-form-to-vars formula1))
	  (vars2 (quant-form-to-vars formula2)))
      (if (not (= (length vars1) (length vars2)))
	  (myerror "alpha-equal-formulas-to-renaming"
		   "quantified variables of the same length expected"
		   formula1 formula2))
      (append (list-transform-positive (map list vars1 vars2)
		(lambda (p)
		  (not (equal? (car p) (cadr p)))))
	      (alpha-equal-formulas-to-renaming
	       (quant-form-to-kernel formula1)
	       (quant-form-to-kernel formula2)))))
   (else (myerror "alpha-equal-formulas-to-renaming"
		  "alpha equal formula expected"
		  formula1 formula2))))

;; Comprehension terms have the form (cterm vars formula), where
;; formula may contain further free variables.

(define (make-cterm x . rest)
  (if (null? rest)
      (list 'cterm (list) x)
      (let* ((prev (apply make-cterm rest))
	     (vars (cterm-to-vars prev)))
	(if (not (var-form? x))
	    (myerror "make-cterm" "variable expected" x))
	(if (member x vars)
	    (apply myerror "make-cterm" "distinct variables expected" x vars))
	(list 'cterm (cons x vars)
	      (cterm-to-formula prev)))))

(define cterm-to-vars cadr)
(define cterm-to-formula caddr)

(define (cterm-to-arity cterm)
  (apply make-arity (map var-to-type (cterm-to-vars cterm))))

(define (cterm-form? x)
  (and (pair? x) (eq? 'cterm (car x))))

(define (cterm? x)
  (and (cterm-form? x)
       (list? x)
       (= 3 (length x))
       (let ((vars (cadr x))
	     (formula (caddr x)))
	 (and (apply and-op (map var? vars))
	      (formula? formula)))))

(define (classical-cterm=? cterm1 cterm2 . ignore-deco-flag)
  (or (equal? cterm1 cterm2)
      (apply
       classical-formula=?
       (append
	(list (apply mk-all (append (cterm-to-vars cterm1)
				    (list (cterm-to-formula cterm1))))
	      (apply mk-all (append (cterm-to-vars cterm2)
				    (list (cterm-to-formula cterm2)))))
	ignore-deco-flag))))

(define (cterm=? cterm1 cterm2 . ignore-deco-flag)
  (or (equal? cterm1 cterm2)
      (apply
       formula=?
       (append
	(list (apply mk-all (append (cterm-to-vars cterm1)
				    (list (cterm-to-formula cterm1))))
	      (apply mk-all (append (cterm-to-vars cterm2)
				    (list (cterm-to-formula cterm2)))))
	ignore-deco-flag))))

(define (cterm-to-free cterm)
  (set-minus (formula-to-free (cterm-to-formula cterm))
	     (cterm-to-vars cterm)))

(define (cterm-to-bound cterm)
  (union (cterm-to-vars cterm)
	 (formula-to-bound (cterm-to-formula cterm))))

(define (fold-cterm cterm)
  (list 'cterm
	(cterm-to-vars cterm)
	(fold-formula (cterm-to-formula cterm))))

(define (unfold-cterm cterm)
  (list 'cterm
	(cterm-to-vars cterm)
	(unfold-formula (cterm-to-formula cterm))))

(define (pvar-cterm? cterm)
  (let ((vars (cterm-to-vars cterm))
	(formula (cterm-to-formula cterm)))
    (and (predicate-form? formula)
	 (pvar-form? (predicate-form-to-predicate formula))
	 (let ((args (predicate-form-to-args formula)))
	   (if (apply and-op (map term-in-var-form? args))
	       (let ((argvars (map term-in-var-form-to-var args)))
		 (and (equal? vars argvars)
		      (apply and-op (map t-deg-zero?
					 (map var-to-t-deg vars))))))))))

(define (pvar-cterm-to-pvar cterm)
  (predicate-form-to-predicate (cterm-to-formula cterm)))

(define (idpredconst=? idpc1 idpc2)
  (or (equal? idpc1 idpc2)
      (let* ((name1 (idpredconst-to-name idpc1))
	     (types1 (idpredconst-to-types idpc1))
	     (cterms1 (idpredconst-to-cterms idpc1))
	     (name2 (idpredconst-to-name idpc2))
	     (types2 (idpredconst-to-types idpc2))
	     (cterms2 (idpredconst-to-cterms idpc2)))
	(and (string=? name1 name2)
	     (equal? types1 types2)
	     (= (length cterms1) (length cterms2))
	     (apply and-op (map (lambda (x y) (classical-cterm=? x y))
				cterms1 cterms2))))))

;; formula-to-undec-formula prepares for decoration.  It changes all
;; occurrences of imp, all into impnc, allnc, and in case id-deco? is
;; true, (i) every existential quantification exd, exl, exr into exnc,
;; (ii) every total existential quantification exdt, exlt, exrt into
;; exnct, (iii) every conjunction andd, andl, andr into andnc (andb is
;; for the boolean operator), and (iv) every disjunction or, orl, orr
;; into oru (orb is for the boolean operator).  It does not touch
;; formulas of nulltype under extension, and in case id-deco? is false
;; it does not touch any formula of nulltype.

(define (formula-to-undec-formula formula id-deco?)
  (cond
   ((and id-deco? (formula-of-nulltype-under-extension? formula))
    formula)
   ((and (not id-deco?) (formula-of-nulltype? formula))
    formula)
   ((predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula)))
      (if (idpredconst-form? pred)
	  (apply make-predicate-formula
		 (idpredconst-to-undec-idpredconst pred id-deco?)
		 (predicate-form-to-args formula))
	  formula)))
   ((bicon-form? formula)
    (if
     (imp-form? formula)
     (make-impnc
      (formula-to-undec-formula (bicon-form-to-left formula) id-deco?)
      (formula-to-undec-formula (bicon-form-to-right formula) id-deco?))
     (make-bicon
      (bicon-form-to-bicon formula)
      (formula-to-undec-formula (bicon-form-to-left formula) id-deco?)
      (formula-to-undec-formula (bicon-form-to-right formula) id-deco?))))
   ((quant-form? formula)
    (cond
     ((all-form? formula)
      (make-allnc
       (all-form-to-var formula)
       (formula-to-undec-formula (all-form-to-kernel formula) id-deco?)))
     ((excl-form? formula)
      (fold-formula ;to be adapted to exclnc
       (formula-to-undec-formula (unfold-formula formula) id-deco?)))
     (else (make-quant (quant-form-to-quant formula)
		       (quant-form-to-vars formula)
		       (formula-to-undec-formula
			(quant-form-to-kernel formula) id-deco?)))))
   (else formula)))

(define (cterm-to-undec-cterm cterm id-deco?)
  (let* ((vars (cterm-to-vars cterm))
	 (formula (cterm-to-formula cterm))
	 (undec-formula (formula-to-undec-formula formula id-deco?)))
    (apply make-cterm (append vars (list undec-formula)))))

(define (formula-to-dec-formula formula)
  (cond
   ((prime-form? formula) formula)
   ((bicon-form? formula)
    (if
     (impnc-form? formula)
     (make-imp (formula-to-dec-formula (bicon-form-to-left formula))
	       (formula-to-dec-formula (bicon-form-to-right formula)))
     (make-bicon (bicon-form-to-bicon formula)
		 (formula-to-dec-formula (bicon-form-to-left formula))
		 (formula-to-dec-formula (bicon-form-to-right formula)))))
   ((quant-form? formula)
    (cond
     ((allnc-form? formula)
      (make-all (allnc-form-to-var formula) (formula-to-dec-formula
					     (allnc-form-to-kernel formula))))
     (else (make-quant (quant-form-to-quant formula)
		       (quant-form-to-vars formula)
		       (formula-to-dec-formula
			(quant-form-to-kernel formula))))))
   (else (myerror "formula-to-dec-formula" "formula expected"
		  formula))))

;; formula1 extends formula2 if some impnc, allnc have been changed
;; into imp, all.  Then formula1 has a more complex type.

(define (bicons-to-lub-bicon bicon1 bicon2)
  (if (eq? bicon1 bicon2) bicon1
      (cond ((and (eq? bicon1 'ord) (memq bicon2 '(orl orr oru))) bicon1)
	    ((and (memq bicon1 '(orl orr oru)) (eq? bicon2 'ord)) bicon2)
	    ((and (eq? bicon1 'oru) (memq bicon2 '(orl orr))) bicon2)
	    ((and (memq bicon1 '(orl orr)) (eq? bicon2 'oru)) bicon1)
	    ((and (eq? bicon1 'orl) (eq? bicon2 'orr)) 'ord)
	    ((and (eq? bicon1 'orr) (eq? bicon2 'orl)) 'ord)
	    ((and (eq? bicon1 'andd) (memq bicon2 '(andl andr andnc))) bicon1)
	    ((and (memq bicon1 '(andl andr andnc)) (eq? bicon2 'andd)) bicon2)
	    ((and (eq? bicon1 'andnc) (memq bicon2 '(andl andr))) bicon2)
	    ((and (memq bicon1 '(andl andr)) (eq? bicon2 'andnc)) bicon1)
	    (else (myerror "bicons-to-lub-bicon"
			   "unexpected bicons" bicon1 bicon2)))))

(define (quants-to-lub-quant quant1 quant2)
  (if (eq? quant1 quant2) quant1
      (cond ((and (eq? quant1 'exd) (memq quant2 '(exl exr exnc))) quant1)
	    ((and (memq quant1 '(exl exr exnc)) (eq? quant2 'exd)) quant2)
	    ((and (eq? quant1 'exnc) (memq quant2 '(exl exr))) quant2)
	    ((and (memq quant1 '(exl exr)) (eq? quant2 'exnc)) quant1)
	    ((and (eq? quant1 'exl) (eq? quant2 'exr)) 'exd)
	    ((and (eq? quant1 'exr) (eq? quant2 'exl)) 'exd)
	    ((and (eq? quant1 'exdt) (memq quant2 '(exlt exrt exnct))) quant1)
	    ((and (memq quant1 '(exlt exrt exnct)) (eq? quant2 'exdt)) quant2)
	    ((and (eq? quant1 'exnct) (memq quant2 '(exlt exrt))) quant2)
	    ((and (memq quant1 '(exlt exrt)) (eq? quant2 'exnct)) quant1)
	    ((and (eq? quant1 'exlt) (eq? quant2 'exrt)) 'exdt)
	    ((and (eq? quant1 'exrt) (eq? quant2 'exlt)) 'exdt)
	    (else (myerror  "quants-to-lub-quant"
			    "unexpected quants" quant1 quant2)))))

;; If formula2 is an instance of a decoration of formula1, the result
;; of dec-variants-to-lub-aux follows formula1 and disregards the terms
;; and possibly changed bound variables in formula2.

(define (dec-variants-to-lub id-deco? formula . formulas)
  (if (null? formulas) formula
      (dec-variants-to-lub-aux
       formula (apply dec-variants-to-lub id-deco? formulas)
       id-deco?)))

(define (dec-variants-to-lub-aux formula1 formula2 id-deco?)
  (cond
   ((and (bicon-form? formula1) (bicon-form? formula2))
    (let* ((bicon1 (bicon-form-to-bicon formula1))
	   (bicon2 (bicon-form-to-bicon formula2))
	   (lub-bicon
	    (cond
	     ((eq? bicon1 bicon2) bicon1)
	     ((and (eq? bicon1 'imp) (eq? bicon2 'impnc)) bicon1)
	     ((and (eq? bicon1 'impnc) (eq? bicon2 'imp)) bicon2)
	     (id-deco? (bicons-to-lub-bicon bicon1 bicon2))
	     (else (myerror "dec-variants-to-lub-aux"
			    "decoration variants expected"
			    formula1 formula2)))))
      (make-bicon lub-bicon
		  (dec-variants-to-lub-aux (bicon-form-to-left formula1)
					   (bicon-form-to-left formula2)
					   id-deco?)
		  (dec-variants-to-lub-aux (bicon-form-to-right formula1)
					   (bicon-form-to-right formula2)
					   id-deco?))))
   ((and (quant-form? formula1) (quant-form? formula2))
    (let* ((quant1 (quant-form-to-quant formula1))
	   (quant2 (quant-form-to-quant formula2))
	   (lub-quant
	    (cond
	     ((eq? quant1 quant2) quant1)
	     ((and (eq? quant1 'all) (eq? quant2 'allnc)) quant1)
	     ((and (eq? quant1 'allnc) (eq? quant2 'all)) quant2)
	     (id-deco? (quants-to-lub-quant quant1 quant2))
	     (else (myerror "dec-variants-to-lub-aux"
			    "decoration variants expected"
			    formula1 formula2)))))
      (make-quant lub-quant
		  (quant-form-to-vars formula1)
		  (dec-variants-to-lub-aux (quant-form-to-kernel formula1)
					   (quant-form-to-kernel formula2)
					   id-deco?))))
   ((and (predicate-form? formula1) (predicate-form? formula2)
	 (idpredconst-form? (predicate-form-to-predicate formula1))
	 (idpredconst-form? (predicate-form-to-predicate formula2)))
    (let* ((idpc1 (predicate-form-to-predicate formula1))
	   (idpc2 (predicate-form-to-predicate formula2))
	   (name (idpredconst-to-name idpc1))
	   (types (idpredconst-to-types idpc1))
	   (cterms1 (idpredconst-to-cterms idpc1))
	   (cterms2 (idpredconst-to-cterms idpc2))
	   (lub-cterms
	    (map (lambda (ct1 ct2)
		   (let* ((vars (cterm-to-vars ct1))
			  (fla1 (cterm-to-formula ct1))
			  (fla2 (cterm-to-formula ct2))
			  (lub-fla
			   (dec-variants-to-lub-aux fla1 fla2 id-deco?)))
		     (apply make-cterm (append vars (list lub-fla)))))
		 cterms1 cterms2))
	   (lub-idpc (make-idpredconst name types lub-cterms)))
      (apply make-predicate-formula
	     lub-idpc (predicate-form-to-args formula1))))
   ((and (prime-form? formula1) (prime-form? formula2)) formula1)
   (else (myerror "dec-variants-to-lub-aux" "decoration variants expected"
		  formula1 formula2))))

(define (dec-variants-to-glb-aux formula1 formula2)
  (cond
   ((and (imp-impnc-form? formula1) (imp-impnc-form? formula2))
    (if (or (impnc-form? formula1) (impnc-form? formula2))
	(make-impnc (dec-variants-to-glb-aux
		     (imp-impnc-form-to-premise formula1)
		     (imp-impnc-form-to-premise formula2))
		    (dec-variants-to-glb-aux
		     (imp-impnc-form-to-conclusion formula1)
		     (imp-impnc-form-to-conclusion formula2)))
	(make-imp (dec-variants-to-glb-aux
		   (imp-form-to-premise formula1)
		   (imp-form-to-premise formula2))
		  (dec-variants-to-glb-aux
		   (imp-form-to-conclusion formula1)
		   (imp-form-to-conclusion formula2)))))
   ((and (all-allnc-form? formula1) (all-allnc-form? formula2))
    (if (or (allnc-form? formula1) (allnc-form? formula2))
	(make-allnc (all-allnc-form-to-var formula1)
		    (dec-variants-to-glb-aux
		     (all-allnc-form-to-kernel formula1)
		     (all-allnc-form-to-kernel formula2)))
	(make-all (all-form-to-var formula1)
		  (dec-variants-to-glb-aux
		   (all-form-to-kernel formula1)
		   (all-form-to-kernel formula2)))))
   ((and (bicon-form? formula1) (bicon-form? formula2))
    (make-bicon (bicon-form-to-bicon formula1)
		(dec-variants-to-glb-aux
		 (bicon-form-to-left formula1)
		 (bicon-form-to-left formula2))
		(dec-variants-to-glb-aux
		 (bicon-form-to-right formula1)
		 (bicon-form-to-right formula2))))
   ((and (quant-form? formula1) (quant-form? formula2))
    (make-quant (quant-form-to-quant formula1)
		(quant-form-to-vars formula1)
		(dec-variants-to-glb-aux
		 (quant-form-to-kernel formula1)
		 (quant-form-to-kernel formula2))))
   ((and (prime-form? formula1) (prime-form? formula2))
    formula1)
   (else (myerror "dec-variants-to-glb-aux" "decoration variants expected"
		  formula1 formula2))))

(define (dec-variants-to-glb formula . formulas)
  (if (null? formulas) formula
      (dec-variants-to-glb-aux
       formula (apply dec-variants-to-glb formulas))))

;(pp (dec-variants-to-glb (pf "F -> allnc boole T") (pf "F --> all boole1 T")))

(define (extending-dec-variants? formula1 formula2 id-deco?)
  (extending-dec-variants-aux?
   (unfold-formula formula1) (unfold-formula formula2) '() '() id-deco?))

(define (extending-dec-variants-aux? formula1 formula2 alist alistrev
				     id-deco?)
  (cond
   ((and (bicon-form? formula1) (bicon-form? formula2))
    (let* ((bicon1 (bicon-form-to-bicon formula1))
	   (bicon2 (bicon-form-to-bicon formula2))
	   (bicon-extension-test
	    (or (eq? bicon1 bicon2)
		(and (eq? bicon1 'imp) (eq? bicon2 'impnc))
		(and id-deco? (eq? bicon1 'ord) (memq bicon2 '(orl orr oru)))
		(and id-deco? (memq bicon1 '(orl orr)) (eq? bicon2 'oru))
		(and id-deco? (eq? bicon1 'andd)
		     (memq bicon2 '(andl andr andnc)))
		(and id-deco? (memq bicon1 '(andl andr)) (eq? bicon2 'andnc)))))
      (and
       bicon-extension-test
       (let ((left1 (bicon-form-to-left formula1))
	     (right1 (bicon-form-to-right formula1))
	     (left2 (bicon-form-to-left formula2))
	     (right2 (bicon-form-to-right formula2)))
	 (and (extending-dec-variants-aux? left1 left2 alist alistrev
					   id-deco?)
	      (extending-dec-variants-aux? right1 right2 alist alistrev
					   id-deco?))))))
   ((and (quant-form? formula1) (quant-form? formula2))
    (let* ((quant1 (quant-form-to-quant formula1))
	   (quant2 (quant-form-to-quant formula2))
	   (quant-extension-test
	    (or
	     (eq? quant1 quant2)
	     (and (eq? quant1 'all) (eq? quant2 'allnc))
	     (and id-deco? (eq? quant1 'exd) (memq quant2 '(exl exr exnc)))
	     (and id-deco? (memq quant1 '(exl exr)) (eq? quant2 'exnc))
	     (and id-deco? (eq? quant1 'exdt) (memq quant2 '(exlt exrt exnct)))
	     (and id-deco? (memq quant1 '(exlt exrt)) (eq? quant2 'exnct)))))
      (and quant-extension-test
	   (let ((vars1 (quant-form-to-vars formula1))
		 (vars2 (quant-form-to-vars formula2))
		 (kernel1 (quant-form-to-kernel formula1))
		 (kernel2 (quant-form-to-kernel formula2)))
	     (and (equal? (map var-to-type vars1) (map var-to-type vars2))
		  (equal? (map var-to-t-deg vars1) (map var-to-t-deg vars2))
		  (extending-dec-variants-aux?
		   kernel1 kernel2
		   (append (map list vars1 vars2)
			   alist)
		   (append (map list vars2 vars1)
			   alistrev)
		   id-deco?))))))
   ((and (predicate-form? formula1) (predicate-form? formula2))
    (let ((pred1 (predicate-form-to-predicate formula1))
	  (pred2 (predicate-form-to-predicate formula2))
	  (args1 (predicate-form-to-args formula1))
	  (args2 (predicate-form-to-args formula2)))
      (and
       (= (length args1) (length args2))
       (terms=-aux? args1 args2 alist alistrev)
       (cond
	((and (idpredconst-form? pred1) (idpredconst-form? pred2))
	 (let* ((idpc1 (predicate-form-to-predicate formula1))
		(idpc2 (predicate-form-to-predicate formula2))
		(name1 (idpredconst-to-name idpc1))
		(name2 (idpredconst-to-name idpc2))
		(types1 (idpredconst-to-types idpc1))
		(types2 (idpredconst-to-types idpc2))
		(cterms1 (idpredconst-to-cterms idpc1))
		(cterms2 (idpredconst-to-cterms idpc2)))
	   (and (string=? name1 name2)
		(equal? types1 types2)
		(apply and-op
		       (map (lambda (ct1 ct2)
			      (let ((vars1 (cterm-to-vars ct1))
				    (fla1 (cterm-to-formula ct1))
				    (vars2 (cterm-to-vars ct2))
				    (fla2 (cterm-to-formula ct2)))
				(and
				 (equal? (map var-to-type vars1)
					 (map var-to-type vars2))
				 (equal? (map var-to-t-deg vars1)
					 (map var-to-t-deg vars2))
				 (extending-dec-variants-aux?
				  fla1 fla2
				  (append (map list vars1 vars2)
					  alist)
				  (append (map list vars2 vars1)
					  alistrev)
				  id-deco?))))
			    cterms1 cterms2)))))
	((and (pvar-form? pred1) (pvar-form? pred2))
	 (equal? pred1 pred2))
	((and (predconst-form? pred1) (predconst-form? pred2))
	 (equal? pred1 pred2))
	(else #f)))))
   ((and (atom-form? formula1) (atom-form? formula2))
    (term=-aux? (atom-form-to-kernel formula1)
		(atom-form-to-kernel formula2)
		alist alistrev))
   (else #f)))

(define (strengthened-dec-variants? formula1 formula2)
  (strengthened-dec-variants-aux?
   (unfold-formula formula1) (unfold-formula formula2) '() '()))

(define (strengthened-dec-variants-aux? formula1 formula2 alist alistrev)
  (cond
   ((and (bicon-form? formula1) (bicon-form? formula2))
    (let* ((bicon1 (bicon-form-to-bicon formula1))
	   (bicon2 (bicon-form-to-bicon formula2))
	   (positive-bicon-strengthening-test
	    (or (eq? bicon1 bicon2)
		(case bicon2
		  ((andnc) (memq bicon1 '(andl andr andd)))
		  ((andl) (eq? bicon1 'andd))
		  ((andr) (eq? bicon1 'andd))
		  ((oru) (memq bicon1 '(orl orr ord)))
		  ((orl orr) (eq? bicon1 'ord))
		  (else #f)))))
      (cond
       (positive-bicon-strengthening-test
	(let ((left1 (bicon-form-to-left formula1))
	      (right1 (bicon-form-to-right formula1))
	      (left2 (bicon-form-to-left formula2))
	      (right2 (bicon-form-to-right formula2)))
	  (and
	   (strengthened-dec-variants-aux? left1 left2 alist alistrev)
	   (strengthened-dec-variants-aux? right1 right2 alist alistrev))))
       ((and (imp-impnc-form? formula1) (imp-impnc-form? formula2))
	(and
	 (or (eq? (bicon-form-to-bicon formula1)
		  (bicon-form-to-bicon formula2))
	     (and (impnc-form? formula1) (imp-form? formula2))
	     (and
	      (imp-form? formula1) (impnc-form? formula2)
	      (or (formula-of-nulltype? (imp-form-to-premise formula1))
		  (formula-of-nulltype? (imp-form-to-conclusion formula1))
		  (formula-of-nulltype? (imp-form-to-premise formula2))
		  (formula-of-nulltype? (imp-form-to-conclusion formula2)))))
	 (let ((left1 (bicon-form-to-left formula1))
	       (right1 (bicon-form-to-right formula1))
	       (left2 (bicon-form-to-left formula2))
	       (right2 (bicon-form-to-right formula2)))
	   (and
	    (strengthened-dec-variants-aux? left2 left1 alist alistrev)
	    (strengthened-dec-variants-aux? right1 right2 alist alistrev)))))
       (else (myerror "strengthened-dec-variants-aux?"
		      "unexpected bicons" bicon1 bicon2)))))
   ((and (quant-form? formula1) (quant-form? formula2))
    (let* ((quant1 (quant-form-to-quant formula1))
	   (quant2 (quant-form-to-quant formula2))
	   (positive-quant-strengthening-test
	    (or (eq? quant1 quant2)
		(case quant2
		  ((exnc) (memq quant1 '(exl exr exd)))
		  ((exl exr) (eq? quant1 'exd))
		  ((exnct) (memq quant1 '(exlt exrt exdt)))
		  ((exlt exrt) (eq? quant1 'exdt))
		  (else #f)))))
      (cond
       (positive-quant-strengthening-test
	(let ((vars1 (quant-form-to-vars formula1))
	      (vars2 (quant-form-to-vars formula2))
	      (kernel1 (quant-form-to-kernel formula1))
	      (kernel2 (quant-form-to-kernel formula2)))
	  (and (equal? (map var-to-type vars1) (map var-to-type vars2))
	       (equal? (map var-to-t-deg vars1) (map var-to-t-deg vars2))
	       (strengthened-dec-variants-aux?
		kernel1 kernel2
		(append (map list vars1 vars2) alist)
		(append (map list vars2 vars1) alistrev)))))
       ((and (all-allnc-form? formula1) (all-allnc-form? formula2))
	(and
	 (or (eq? quant1 quant2)
	     (and (all-form? formula1) (allnc-form? formula2))
	     (and (allnc-form? formula1) (all-form? formula2)
		  (or (formula-of-nulltype? (all-form-to-kernel formula1))
		      (formula-of-nulltype? (all-form-to-kernel formula2)))))
	 (let ((vars1 (quant-form-to-vars formula1))
	       (vars2 (quant-form-to-vars formula2))
	       (kernel1 (quant-form-to-kernel formula1))
	       (kernel2 (quant-form-to-kernel formula2)))
	   (and (equal? (map var-to-type vars1) (map var-to-type vars2))
		(equal? (map var-to-t-deg vars1) (map var-to-t-deg vars2))
		(strengthened-dec-variants-aux?
		 kernel1 kernel2
		 (append (map list vars1 vars2) alist)
		 (append (map list vars2 vars1) alistrev)))))))))
   ((and (predicate-form? formula1) (predicate-form? formula2)
	 (idpredconst-form? (predicate-form-to-predicate formula1))
	 (idpredconst-form? (predicate-form-to-predicate formula2)))
    (let* ((idpc1 (predicate-form-to-predicate formula1))
	   (idpc2 (predicate-form-to-predicate formula2))
	   (args1 (predicate-form-to-args formula1))
	   (args2 (predicate-form-to-args formula2))
	   (name (idpredconst-to-name idpc1))
	   (types (idpredconst-to-types idpc1))
	   (cterms1 (idpredconst-to-cterms idpc1))
	   (cterms2 (idpredconst-to-cterms idpc2)))
      (and (apply and-op (map (lambda (ct1 ct2)
				(let ((fla1 (cterm-to-formula ct1))
				      (fla2 (cterm-to-formula ct2)))
				  (strengthened-dec-variants-aux?
				   fla1 fla2 alist alistrev)))
			      cterms1 cterms2))
	   (terms=-aux? args1 args2 alist alistrev))))
   ((and (atom-form? formula1) (atom-form? formula2))
    (term=-aux? (atom-form-to-kernel formula1)
		(atom-form-to-kernel formula2)
		alist alistrev))
   ((and (prime-predicate-form? formula1) (prime-predicate-form? formula2))
    (let ((pred1 (predicate-form-to-predicate formula1))
	  (pred2 (predicate-form-to-predicate formula2))
	  (args1 (predicate-form-to-args formula1))
	  (args2 (predicate-form-to-args formula2)))
      (and (predicate-equal? pred1 pred2)
	   (terms=-aux? args1 args2 alist alistrev))))
   (else #f)))

(define (dec-variants? formula1 formula2 id-deco?)
  (dec-variants-aux?
   (unfold-formula formula1) (unfold-formula formula2) '() '() id-deco?))

(define (dec-variants-aux? formula1 formula2 alist alistrev id-deco?)
  (cond
   ((and (bicon-form? formula1) (bicon-form? formula2))
    (let* ((bicon1 (bicon-form-to-bicon formula1))
	   (bicon2 (bicon-form-to-bicon formula2))
	   (bicon-variant-test
	    (or (eq? bicon1 bicon2)
		(and (eq? bicon1 'imp) (eq? bicon2 'impnc))
		(and (eq? bicon1 'impnc) (eq? bicon2 'imp))
		(and id-deco?
		     (case bicon1
		       ((andd andl andr andnc)
			(memq bicon2 '(andd andl andr andnc)))
		       ((ord orl orr oru) (memq bicon2 '(ord orl orr oru)))
		       (else #f))))))
      (and
       bicon-variant-test
       (let ((left1 (bicon-form-to-left formula1))
	     (right1 (bicon-form-to-right formula1))
	     (left2 (bicon-form-to-left formula2))
	     (right2 (bicon-form-to-right formula2)))
	 (and (dec-variants-aux? left1 left2 alist alistrev id-deco?)
	      (dec-variants-aux? right1 right2 alist alistrev id-deco?))))))
   ((and (quant-form? formula1) (quant-form? formula2))
    (let* ((quant1 (quant-form-to-quant formula1))
	   (quant2 (quant-form-to-quant formula2))
	   (quant-variant-test
	    (or (eq? quant1 quant2)
		(and (eq? quant1 'all) (eq? quant2 'allnc))
		(and (eq? quant1 'allnc) (eq? quant2 'all))
		(and id-deco?
		     (case quant1
		       ((exd exl exr exnc) (memq quant2 '(exd exl exr exnc)))
		       ((exdt exlt exrt exnct)
			(memq quant2 '(exdt exlt exrt exnct)))
		       (else #f))))))
      (and quant-variant-test
	   (let ((vars1 (quant-form-to-vars formula1))
		 (vars2 (quant-form-to-vars formula2))
		 (kernel1 (quant-form-to-kernel formula1))
		 (kernel2 (quant-form-to-kernel formula2)))
	     (and (equal? (map var-to-type vars1) (map var-to-type vars2))
		  (equal? (map var-to-t-deg vars1) (map var-to-t-deg vars2))
		  (dec-variants-aux?
		   kernel1 kernel2
		   (append (map list vars1 vars2) alist)
		   (append (map list vars2 vars1) alistrev)
		   id-deco?))))))
   ((and (predicate-form? formula1) (predicate-form? formula2))
    (let ((pred1 (predicate-form-to-predicate formula1))
	  (pred2 (predicate-form-to-predicate formula2))
	  (args1 (predicate-form-to-args formula1))
	  (args2 (predicate-form-to-args formula2)))
      (and
       (= (length args1) (length args2))
       (terms=-aux? args1 args2 alist alistrev)
       (cond
	((and (idpredconst-form? pred1) (idpredconst-form? pred2))
	 (let* ((idpc1 (predicate-form-to-predicate formula1))
		(idpc2 (predicate-form-to-predicate formula2))
		(name1 (idpredconst-to-name idpc1))
		(name2 (idpredconst-to-name idpc2))
		(types1 (idpredconst-to-types idpc1))
		(types2 (idpredconst-to-types idpc2))
		(cterms1 (idpredconst-to-cterms idpc1))
		(cterms2 (idpredconst-to-cterms idpc2)))
	   (and (string=? name1 name2)
		(equal? types1 types2)
		(apply and-op
		       (map (lambda (ct1 ct2)
			      (let ((vars1 (cterm-to-vars ct1))
				    (fla1 (cterm-to-formula ct1))
				    (vars2 (cterm-to-vars ct2))
				    (fla2 (cterm-to-formula ct2)))
				(and
				 (equal? (map var-to-type vars1)
					 (map var-to-type vars2))
				 (equal? (map var-to-t-deg vars1)
					 (map var-to-t-deg vars2))
				 (dec-variants-aux?
				  fla1 fla2
				  (append (map list vars1 vars2) alist)
				  (append (map list vars2 vars1) alistrev)
				  id-deco?))))
			    cterms1 cterms2)))))
	((and (pvar-form? pred1) (pvar-form? pred2))
	 (equal? pred1 pred2))
	((and (predconst-form? pred1) (predconst-form? pred2))
	 (equal? pred1 pred2))
	(else #f)))))
   ((and (atom-form? formula1) (atom-form? formula2))
    (term=-aux? (atom-form-to-kernel formula1)
		(atom-form-to-kernel formula2)
		alist alistrev))
   (else #f)))

(define (dec-variants-up-to-pvars? formula1 formula2)
  (dec-variants-up-to-pvars-aux?
   (unfold-formula formula1) (unfold-formula formula2) '() '()))

(define (dec-variants-up-to-pvars-aux? formula1 formula2 alist alistrev)
  (cond
   ((and (bicon-form? formula1) (bicon-form? formula2))
    (let* ((bicon1 (bicon-form-to-bicon formula1))
	   (bicon2 (bicon-form-to-bicon formula2))
	   (bicon-variant-test
	    (or (eq? bicon1 bicon2)
		(case bicon1
		  ((imp impnc) (memq bicon2 '(imp impnc)))
		  ((andd andl andr andnc) (memq bicon2 '(andd andl andr andnc)))
		  ((ord orl orr oru) (memq bicon2 '(ord orl orr oru)))
		  (else #f)))))
      (and bicon-variant-test
	   (let ((left1 (bicon-form-to-left formula1))
		 (right1 (bicon-form-to-right formula1))
		 (left2 (bicon-form-to-left formula2))
		 (right2 (bicon-form-to-right formula2)))
	     (and
	      (dec-variants-up-to-pvars-aux? left1 left2 alist alistrev)
	      (dec-variants-up-to-pvars-aux? right1 right2 alist alistrev))))))
   ((and (quant-form? formula1) (quant-form? formula2))
    (let* ((quant1 (quant-form-to-quant formula1))
	   (quant2 (quant-form-to-quant formula2))
	   (quant-variant-test
	    (or (eq? quant1 quant2)
		(case quant1
		  ((all allnc) (memq quant2 '(all allnc)))
		  ((exd exl exr exnc) (memq quant2 '(exd exl exr exnc)))
		  ((exdt exlt exrt exnct) (memq quant2 '(exdt exlt exrt exnct)))
		  (else #f)))))
      (and quant-variant-test
	   (let ((vars1 (quant-form-to-vars formula1))
		 (vars2 (quant-form-to-vars formula2))
		 (kernel1 (quant-form-to-kernel formula1))
		 (kernel2 (quant-form-to-kernel formula2)))
	     (and (equal? (map var-to-type vars1) (map var-to-type vars2))
		  (equal? (map var-to-t-deg vars1) (map var-to-t-deg vars2))
		  (dec-variants-up-to-pvars-aux?
		   kernel1 kernel2
		   (append (map list vars1 vars2) alist)
		   (append (map list vars2 vars1) alistrev)))))))
   ((and (predicate-form? formula1) (predicate-form? formula2))
    (let ((pred1 (predicate-form-to-predicate formula1))
	  (pred2 (predicate-form-to-predicate formula2))
	  (args1 (predicate-form-to-args formula1))
	  (args2 (predicate-form-to-args formula2)))
      (and
       (= (length args1) (length args2))
       (terms=-aux? args1 args2 alist alistrev)
       (cond
	((and (idpredconst-form? pred1) (idpredconst-form? pred2))
	 (let* ((idpc1 (predicate-form-to-predicate formula1))
		(idpc2 (predicate-form-to-predicate formula2))
		(name1 (idpredconst-to-name idpc1))
		(name2 (idpredconst-to-name idpc2))
		(types1 (idpredconst-to-types idpc1))
		(types2 (idpredconst-to-types idpc2))
		(cterms1 (idpredconst-to-cterms idpc1))
		(cterms2 (idpredconst-to-cterms idpc2)))
	   (and (string=? name1 name2)
		(equal? types1 types2)
		(apply and-op
		       (map (lambda (ct1 ct2)
			      (let ((vars1 (cterm-to-vars ct1))
				    (fla1 (cterm-to-formula ct1))
				    (vars2 (cterm-to-vars ct2))
				    (fla2 (cterm-to-formula ct2)))
				(and
				 (equal? (map var-to-type vars1)
					 (map var-to-type vars2))
				 (equal? (map var-to-t-deg vars1)
					 (map var-to-t-deg vars2))
				 (dec-variants-up-to-pvars-aux?
				  fla1 fla2
				  (append (map list vars1 vars2) alist)
				  (append (map list vars2 vars1) alistrev)))))
			    cterms1 cterms2)))))
	((and (pvar-form? pred1) (pvar-form? pred2)) #t)
	((and (predconst-form? pred1) (predconst-form? pred2))
	 (equal? pred1 pred2))
	(else #f)))))
   ((and (atom-form? formula1) (atom-form? formula2))
    (term=-aux? (atom-form-to-kernel formula1)
		(atom-form-to-kernel formula2)
		alist alistrev))
   (else #f)))

(define (uninst-formula-and-pvar-and-dec-inst-formula-to-formulas
	 uninst-formula pvar dec-inst-formula)
  (let* ((vars1 (all-allnc-form-to-vars uninst-formula))
	 (vars2 (all-allnc-form-to-vars dec-inst-formula))
	 (number-of-param-vars (- (length vars2) (length vars1)))
	 (dec-inst-formula0 (all-allnc-form-to-final-kernel
			     dec-inst-formula number-of-param-vars)))
    (let uninst-formula-and-dec-inst-formula0-to-formulas
	((f1 uninst-formula) (f2 dec-inst-formula0))
      (cond
       ((atom-form? f1) '())
       ((prime-predicate-form? f1)
	(let ((predicate (predicate-form-to-predicate f1)))
	  (if (and (pvar-form? predicate) (equal? pvar predicate))
	      (list f2)
	      '())))
       ((bicon-form? f1)
	(append (uninst-formula-and-dec-inst-formula0-to-formulas
		 (bicon-form-to-left f1)
		 (bicon-form-to-left f2))
		(uninst-formula-and-dec-inst-formula0-to-formulas
		 (bicon-form-to-right f1)
		 (bicon-form-to-right f2))))
       ((quant-form? f1)
	(uninst-formula-and-dec-inst-formula0-to-formulas
	 (quant-form-to-kernel f1)
	 (quant-form-to-kernel f2)))
       (else (myerror "uninst-formula-and-dec-inst-formula0-to-formulas"
		      "formula expected" f1))))))

(define (aconst-and-dec-inst-formula-to-extended-tpsubst
	 aconst dec-inst-formula id-deco?)
  (let* ((uninst-formula (aconst-to-uninst-formula aconst))
	 (tpsubst (aconst-to-tpsubst aconst))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		  (lambda (x) (pvar-form? (car x)))))
	 (pvars (map car psubst))
	 (pvar-formulas-alist
	  (map (lambda (pvar)
		 (list
		  pvar
		  (uninst-formula-and-pvar-and-dec-inst-formula-to-formulas
		   uninst-formula pvar dec-inst-formula)))
	       pvars)))
    (append
     tsubst
     (map (lambda (pvar)
	    (list pvar
		  (let* ((cterm (cadr (assoc pvar psubst)))
			 (formula (cterm-to-formula cterm))
			 (formulas (cadr (assoc pvar pvar-formulas-alist))))
		    (apply
		     make-cterm
		     (append
		      (cterm-to-vars cterm)
		      (list (apply dec-variants-to-lub
				   id-deco?
				   (cons formula formulas))))))))
	  pvars))))

(define (idpredconst-to-undec-idpredconst idpc id-deco?)
  (let* ((name (idpredconst-to-name idpc))
	 (types (idpredconst-to-types idpc))
	 (cterms (idpredconst-to-cterms idpc))
	 (undec-cterms (map (lambda (cterm)
			      (cterm-to-undec-cterm cterm id-deco?))
			    cterms))
	 (name-for-undec-idpc
	  (if id-deco?
	      (cond ((member name '("ExD" "ExL" "ExR")) "ExNc")
		    ((member name '("ExDT" "ExLT" "ExRT")) "ExNcT")
		    ((member name '("OrD" "OrL" "OrR")) "OrU")
		    ((member name '("AndD" "AndL" "AndR")) "AndNc")
		    (else name))
	      name)))
    (make-idpredconst name-for-undec-idpc types undec-cterms)))

(define (intro-aconst-to-undec-intro-aconst aconst)
  (let* ((repro-data (aconst-to-repro-data aconst))
	 (i (car repro-data))
	 (idpc (cadr repro-data))
	 (undec-idpc (idpredconst-to-undec-idpredconst idpc)))
    (number-and-idpredconst-to-intro-aconst i undec-idpc)))

(define (elim-aconst-to-undec-elim-aconst aconst)
  (let* ((imp-formulas (aconst-to-repro-data aconst))
	 (undec-imp-formulas
	  (map (lambda (imp-formula)
		 (let ((prem (imp-form-to-premise imp-formula))
		       (conc (imp-form-to-conclusion imp-formula)))
		   (make-imp (formula-to-undec-formula prem #t)
			     (formula-to-undec-formula conc #t))))
	       imp-formulas)))
    (apply imp-formulas-to-elim-aconst undec-imp-formulas)))

;; aconst-to-undec-aconst changes tpsubst, but leaves the uninst-formula
;; intact.  Then the repro-data need to be changed as well.

(define (aconst-to-undec-aconst aconst id-deco?)
  (let* ((name (aconst-to-name aconst))
	 (kind (aconst-to-kind aconst))
	 (uninst-fla (aconst-to-uninst-formula aconst))
	 (tpsubst (aconst-to-tpsubst aconst))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		   (lambda (x) (pvar-form? (car x)))))
	 (undec-psubst
	  (map (lambda (p)
		 (list (car p) (cterm-to-undec-cterm (cadr p) id-deco?)))
	       psubst))
	 (undec-tpsubst (append tsubst undec-psubst))
	 (aconst-without-repro-data
	  (make-aconst name kind uninst-fla undec-tpsubst)))
    (apply make-aconst (append (list name kind uninst-fla undec-tpsubst)
			       (aconst-to-computed-repro-data
				aconst-without-repro-data)))))

(define (eq-formula-to-lhs-and-rhs eq-fla)
  (cond
   ((and (atom-form? eq-fla)
	 (let* ((kernel (atom-form-to-kernel eq-fla))
		(op (term-in-app-form-to-final-op kernel)))
	   (and (term-in-const-form? op)
		(member (const-to-name (term-in-const-form-to-const op))
			(list "=" "RatEqv")))))
    (term-in-app-form-to-args (atom-form-to-kernel eq-fla)))
   ((and (predicate-form? eq-fla)
	 (let ((pred (predicate-form-to-predicate eq-fla)))
	   (and (idpredconst-form? pred)
		(member (idpredconst-to-name pred) (list "EqD" "RealEq")))))
    (predicate-form-to-args eq-fla))
   (else (myerror "eq-formula-to-lhs-and-rhs" "eq-formula expected" eq-fla))))

;; Test
;; (pp (cadr (eq-formula-to-lhs-and-rhs (pf "n=m"))))
;; (pp (cadr (eq-formula-to-lhs-and-rhs (pf "a=b"))))
;; (pp (cadr (eq-formula-to-lhs-and-rhs (pf "a eqd b"))))
;; (pp (cadr (eq-formula-to-lhs-and-rhs (pf "x===y"))))

;; 7-2. Normalization
;; ==================

(define (normalize-formula formula)
  (cond
   ((atom-form? formula)
    (make-atomic-formula (nt (atom-form-to-kernel formula))))
   ((predicate-form? formula)
    (let* ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula))
	   (npred (if (idpredconst-form? pred)
		      (let ((name (idpredconst-to-name pred))
			    (types (idpredconst-to-types pred))
			    (cterms (idpredconst-to-cterms pred)))
			(make-idpredconst
			 name types (map normalize-cterm cterms)))
		      pred))
	   (nargs (map nbe-normalize-term args)))
      (apply make-predicate-formula npred nargs)))
   ((bicon-form? formula)
    (make-bicon (bicon-form-to-bicon formula)
		(normalize-formula (bicon-form-to-left formula))
		(normalize-formula (bicon-form-to-right formula))))
   ((quant-form? formula)
    (make-quant (quant-form-to-quant formula)
		(quant-form-to-vars formula)
		(normalize-formula (quant-form-to-kernel formula))))
   (else (myerror "normalize-formula" "formula expected" formula))))

(define (normalize-cterm cterm)
  (let ((vars (cterm-to-vars cterm))
	(formula (cterm-to-formula cterm)))
    (apply make-cterm (append vars (list (normalize-formula formula))))))

(define nf normalize-formula)

(define (beta-pi-eta-normalize-formula formula)
  (cond
   ((atom-form? formula)
    (make-atomic-formula (nt (atom-form-to-kernel formula))))
   ((predicate-form? formula)
    (let* ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula))
	   (npred (if (idpredconst-form? pred)
		      (let ((name (idpredconst-to-name pred))
			    (types (idpredconst-to-types pred))
			    (cterms (idpredconst-to-cterms pred)))
			(make-idpredconst
			 name types (map beta-pi-eta-normalize-cterm cterms)))
		      pred))
	   (nargs (map bpe-nt args)))
      (apply make-predicate-formula npred nargs)))
   ((bicon-form? formula)
    (make-bicon (bicon-form-to-bicon formula)
		(beta-pi-eta-normalize-formula (bicon-form-to-left formula))
		(beta-pi-eta-normalize-formula (bicon-form-to-right formula))))
   ((quant-form? formula)
    (make-quant (quant-form-to-quant formula)
		(quant-form-to-vars formula)
		(beta-pi-eta-normalize-formula (quant-form-to-kernel formula))))
   (else (myerror "beta-pi-eta-normalize-formula" "formula expected" formula))))

(define (beta-pi-eta-normalize-cterm cterm)
  (let ((vars (cterm-to-vars cterm))
	(formula (cterm-to-formula cterm)))
    (apply make-cterm
	   (append vars (list (beta-pi-eta-normalize-formula formula))))))

;; 7-3. Alpha-equality
;; ===================

(define (classical-formula=? formula1 formula2 . ignore-deco-flag)
  (let ((ignore-deco-flag (and (pair? ignore-deco-flag)
			       (car ignore-deco-flag))))
    (or (equal? formula1 formula2)
	(let ((for1 (unfold-formula formula1))
	      (for2 (unfold-formula formula2)))
	  (or (equal? for1 for2)
	      (let ((nf1 (normalize-formula for1))
		    (nf2 (normalize-formula for2)))
		(or (equal? nf1 nf2)
		    (formula=-aux? nf1 nf2 '() '() ignore-deco-flag))))))))

(define (formula=? formula1 formula2 . ignore-deco-flag)
  (let ((ignore-deco-flag (and (pair? ignore-deco-flag)
			       (car ignore-deco-flag))))
    (formula=-aux? formula1 formula2 '() '() ignore-deco-flag)))

(define (formula=-aux? formula1 formula2 alist alistrev ignore-deco-flag)
  (cond
   ((and (bicon-form? formula1) (bicon-form? formula2))
    (let ((bicon1 (bicon-form-to-bicon formula1))
	  (left1 (bicon-form-to-left formula1))
	  (right1 (bicon-form-to-right formula1))
	  (bicon2 (bicon-form-to-bicon formula2))
	  (left2 (bicon-form-to-left formula2))
	  (right2 (bicon-form-to-right formula2)))
      (if
       ignore-deco-flag
       (and (or (eq? bicon1 bicon2)
		(case bicon1
		  ((imp impnc) (memq bicon2 '(imp impnc)))
		  ((andd andl andr andnc) (memq bicon2 '(andd andl andr andnc)))
		  ((ord orl orr oru ornc) (memq bicon2 '(ord orl orr oru ornc)))
		  (else #f)))
	    (formula=-aux? left1 left2 alist alistrev #t)
	    (formula=-aux? right1 right2 alist alistrev #t))
					;ignore-deco-flag if #f
       (if ;impnc is a special case
	(or (and (eq? bicon1 'impnc) (eq? bicon2 'impnc))
	    (and (eq? bicon1 'imp) (eq? bicon2 'impnc))
	    (and (eq? bicon1 'impnc) (eq? bicon2 'imp)))
	(and (formula=-aux? left1 left2 alist alistrev #t) ;ignore deco left
	     (formula=-aux? right1 right2 alist alistrev #f))
	(and (eq? bicon1 bicon2)
	     (formula=-aux? left1 left2 alist alistrev #f)
	     (formula=-aux? right1 right2 alist alistrev #f))))))
   ((and (quant-form? formula1) (quant-form? formula2))
    (let* ((quant1 (quant-form-to-quant formula1))
	   (vars1 (quant-form-to-vars formula1))
	   (kernel1 (quant-form-to-kernel formula1))
	   (quant2 (quant-form-to-quant formula2))
	   (vars2 (quant-form-to-vars formula2))
	   (kernel2 (quant-form-to-kernel formula2))
	   (prev
	    (and (equal? (map var-to-type vars1) (map var-to-type vars2))
		 (equal? (map var-to-t-deg vars1) (map var-to-t-deg vars2))
		 (formula=-aux?
		  kernel1 kernel2
		  (append (map list vars1 vars2) alist)
		  (append (map list vars2 vars1) alistrev)
		  ignore-deco-flag))))
      (if
       ignore-deco-flag
       (and (or (eq? quant1 quant2)
		(case quant1
		  ((all allnc) (memq quant2 '(all allnc)))
		  ((exd exl exr exnc) (memq quant2 '(exd exl exr exnc)))
		  ((exdt exlt exrt exnct) (memq quant2 '(exdt exlt exrt exnct)))
		  (else #f)))
	    prev)
					;ignore-deco-flag is #f
       (cond ;allnc is a special case
	((and (eq? quant1 'all) (eq? quant2 'allnc))
	 (and (formula-of-nulltype? kernel1) prev))
	((and (eq? quant1 'allnc) (eq? quant2 'all))
	 (and (formula-of-nulltype? kernel2) prev))
	(else (and (eq? quant1 quant2) prev))))))
   ((and (predicate-form? formula1) (predicate-form? formula2))
    (let ((pred1 (predicate-form-to-predicate formula1))
	  (pred2 (predicate-form-to-predicate formula2))
	  (args1 (predicate-form-to-args formula1))
	  (args2 (predicate-form-to-args formula2)))
      (and
       (= (length args1) (length args2))
       (terms=-aux? args1 args2 alist alistrev)
       (cond
	((and (idpredconst-form? pred1) (idpredconst-form? pred2))
	 (let* ((idpc1 (predicate-form-to-predicate formula1))
		(idpc2 (predicate-form-to-predicate formula2))
		(name1 (idpredconst-to-name idpc1))
		(name2 (idpredconst-to-name idpc2))
		(types1 (idpredconst-to-types idpc1))
		(types2 (idpredconst-to-types idpc2))
		(cterms1 (idpredconst-to-cterms idpc1))
		(cterms2 (idpredconst-to-cterms idpc2)))
	   (and (if ignore-deco-flag
		    (or (string=? name1 name2)
			(string=? name1 (string-append name2 "Nc"))
			(string=? (string-append name1 "Nc") name2))
		    (string=? name1 name2))
		(equal? types1 types2)
		(apply and-op
		       (map (lambda (ct1 ct2)
			      (let ((vars1 (cterm-to-vars ct1))
				    (fla1 (cterm-to-formula ct1))
				    (vars2 (cterm-to-vars ct2))
				    (fla2 (cterm-to-formula ct2)))
				(and
				 (equal? (map var-to-type vars1)
					 (map var-to-type vars2))
				 (equal? (map var-to-t-deg vars1)
					 (map var-to-t-deg vars2))
				 (formula=-aux?
				  fla1 fla2
				  (append (map list vars1 vars2) alist)
				  (append (map list vars2 vars1) alistrev)
				  ignore-deco-flag))))
			    cterms1 cterms2)))))
	((and (pvar-form? pred1) (pvar-form? pred2))
	 (equal? pred1 pred2))
	((and (predconst-form? pred1) (predconst-form? pred2))
	 (let ((name1 (predconst-to-name pred1))
	       (name2 (predconst-to-name pred2)))
	   (and (if ignore-deco-flag
		    (or (string=? name1 name2)
			(string=? name1 (string-append name2 "Nc"))
			(string=? (string-append name1 "Nc") name2))
		    (string=? name1 name2))
		(= (predconst-to-index pred1) (predconst-to-index pred2))
		(equal? (predconst-to-tsubst pred1) (predconst-to-tsubst pred2))
		(equal? (predconst-to-uninst-arity pred1)
			(predconst-to-uninst-arity pred2)))))
	(else #f)))))
   ((and (atom-form? formula1) (atom-form? formula2))
    (term=-aux? (atom-form-to-kernel formula1)
		(atom-form-to-kernel formula2)
		alist alistrev))
   (else #f)))

;; rename-variables renames bound variables in terms, formulas and cterms.

(define (vars-and-used-vars-to-new-vars vars used-vars)
  (if
   (null? vars) '()
   (let* ((var (car vars))
	  (rest (cdr vars))
	  (name (var-to-name var))
	  (type (var-to-type var))
	  (t-deg (var-to-t-deg var))
	  (relevant-vars (list-transform-positive used-vars
			   (lambda (x) (string=? name (var-to-name x)))))
	  (relevant-indices (map var-to-index relevant-vars))
	  (new-index (do ((i -1 (+ i 1))
			  (is relevant-indices (remove i is)))
			 ((not (member i is)) i)))
	  (new-var (make-var type new-index t-deg name)))
     (cons new-var
	   (vars-and-used-vars-to-new-vars rest (cons new-var used-vars))))))

(define (rename-variables-aux expr used-vars)
  (cond
   ((term-form? expr)
    (cond
     ((term-in-abst-form? expr)
      (let* ((var (term-in-abst-form-to-var expr))
	     (kernel (term-in-abst-form-to-kernel expr))
	     (new-var (var-and-vars-to-new-var var used-vars))
	     (subst (make-subst-wrt var-term-equal?
				    var (make-term-in-var-form new-var)))
	     (subst-kernel (if (null? subst)
			       kernel
			       (term-substitute kernel subst))))
	(make-term-in-abst-form
	 new-var
	 (rename-variables-aux subst-kernel (cons new-var used-vars)))))
     ((term-in-app-form? expr)
      (make-term-in-app-form
       (rename-variables-aux (term-in-app-form-to-op expr) used-vars)
       (rename-variables-aux (term-in-app-form-to-arg expr) used-vars)))
     ((term-in-pair-form? expr)
      (make-term-in-pair-form
       (rename-variables-aux (term-in-pair-form-to-left expr) used-vars)
       (rename-variables-aux (term-in-pair-form-to-right expr) used-vars)))
     ((term-in-lcomp-form? expr)
      (make-term-in-lcomp-form
       (rename-variables-aux (term-in-lcomp-form-to-kernel expr) used-vars)))
     ((term-in-rcomp-form? expr)
      (make-term-in-rcomp-form
       (rename-variables-aux (term-in-rcomp-form-to-kernel expr) used-vars)))
     ((term-in-if-form? expr)
      (make-term-in-if-form
       (rename-variables-aux (term-in-if-form-to-test expr) used-vars)
       (map (lambda (alt) (rename-variables-aux alt used-vars))
	    (term-in-if-form-to-alts expr))))
     (else expr)))
   ((formula-form? expr)
    (cond
     ((atom-form? expr)
      (make-atomic-formula
       (rename-variables-aux (atom-form-to-kernel expr) used-vars)))
     ((predicate-form? expr)
      (let* ((pred (predicate-form-to-predicate expr))
	     (args (predicate-form-to-args expr))
	     (renamed-args
	      (map (lambda (arg) (rename-variables-aux arg used-vars))
		   args)))
	(cond
	 ((or (pvar-form? pred) (predconst-form? pred))
	  (apply make-predicate-formula pred renamed-args))
	 ((idpredconst-form? pred)
	  (let* ((name (idpredconst-to-name pred))
		 (types (idpredconst-to-types pred))
		 (cterms (idpredconst-to-cterms pred))
		 (renamed-cterms
		  (map (lambda (cterm) (rename-variables-aux cterm used-vars))
		       cterms))
		 (renamed-idpredconst
		  (make-idpredconst name types renamed-cterms)))
	    (apply make-predicate-formula
		   renamed-idpredconst renamed-args)))
	 (else (myerror "rename-variables-aux" "predicate expected" pred)))))
     ((bicon-form? expr)
      (make-bicon
       (bicon-form-to-bicon expr)
       (rename-variables-aux (bicon-form-to-left expr) used-vars)
       (rename-variables-aux (bicon-form-to-right expr) used-vars)))
     ((quant-form? expr)
      (let* ((vars (quant-form-to-vars expr))
	     (kernel (quant-form-to-kernel expr))
	     (quant (quant-form-to-quant expr))
	     (new-vars (vars-and-used-vars-to-new-vars vars used-vars))
	     (subst (make-substitution-wrt
		     var-term-equal?
		     vars (map make-term-in-var-form new-vars)))
	     (subst-kernel (if (null? subst)
			       kernel
			       (formula-substitute kernel subst))))
	(make-quant
	 quant new-vars
	 (rename-variables-aux subst-kernel (append new-vars used-vars)))))
     (else (myerror "rename-variables-aux" "formula expected" expr))))
   ((cterm-form? expr)
    (let* ((vars (cterm-to-vars expr))
	   (formula (cterm-to-formula expr))
	   (new-vars (vars-and-used-vars-to-new-vars vars used-vars))
	   (subst (make-substitution-wrt
		   var-term-equal?
		   vars (map make-term-in-var-form new-vars)))
	   (subst-formula (if (null? subst)
			      formula
			      (formula-substitute formula subst))))
      (apply make-cterm
	     (append new-vars (list (rename-variables-aux
				     subst-formula
				     (append new-vars used-vars)))))))
   (else (myerror "rename-variables-aux"
		  "term, formula or cterm expected" expr))))

(define (rename-variables expr)
  (let ((free (cond ((term-form? expr)
		     (term-to-free expr))
		    ((formula-form? expr)
		     (formula-to-free expr))
		    ((cterm-form? expr)
		     (cterm-to-free expr))
		    (else (myerror "rename-variables"
				   "term, formula or cterm expected" expr)))))
    (rename-variables-aux expr free)))

(define (var-and-vars-to-new-var var vars)
  (let* ((name (var-to-name var))
	 (type (var-to-type var))
	 (t-deg (var-to-t-deg var))
	 (relevant-vars
	  (list-transform-positive vars
	    (lambda (x)
	      (and (string=? name (var-to-name x))
		   (= t-deg (var-to-t-deg x))
		   (equal? type (var-to-type x))))))
	 (relevant-indices (map var-to-index relevant-vars))
	 (new-index (do ((i -1 (+ i 1))
			 (is relevant-indices (remove i is)))
			((not (member i is)) i))))
    (make-var type new-index t-deg name)))

;; 7-4. Display
;; ============

;; For a readable display of formulas we use

(define (predicate-to-token-tree pred)
  (cond
   ((pvar-form? pred)
    (make-token-tree 'pvar (pvar-to-string pred)))
   ((predconst-form? pred)
    (make-token-tree 'predconst (predconst-to-string pred)))
   ((idpredconst-form? pred)
    (let* ((name (idpredconst-to-name pred))
	   (types (idpredconst-to-types pred))
	   (cterms (idpredconst-to-cterms pred))
	   (param-tvars (idpredconst-name-to-tvars name))
	   (param-pvars (idpredconst-name-to-param-pvars name))
	   (pvar (idpredconst-name-to-pvar name))
	   (uninst-arity (pvar-to-arity pvar))
	   (uninst-types (arity-to-types uninst-arity))
	   (non-inferable-param-tvars
	    (set-minus param-tvars
		       (apply union (map type-to-tvars uninst-types)))))
      (if (null? cterms)
	  (make-token-tree 'idpredconst (idpredconst-to-string pred))
	  (apply make-token-tree
		 'idpredconst-op
		 (idpredconst-to-name pred)
		 (if (null? non-inferable-param-tvars)
		     (map cterm-to-token-tree cterms)
		     (append (map type-to-token-tree types)
			     (map cterm-to-token-tree cterms)))))))
   (else (myerror "predicate-to-token-tree" "predicate expected" pred))))

(define (cterm-to-token-tree cterm)
  (make-token-tree
   'cterm
   (string-append "cterm ("
		  (vars-to-comma-string (cterm-to-vars cterm))
		  ") ")
   (formula-to-token-tree (cterm-to-formula cterm))))

(define (formula-to-token-tree formula)
  (cond
   ((atom-form? formula)
    (let ((kernel (atom-form-to-kernel formula)))
      (cond
       ((and (term-in-const-form? kernel)
	     (string=? "True"
		       (const-to-name (term-in-const-form-to-const kernel))))
	(make-token-tree 'atom "T"))
       ((and (term-in-const-form? kernel)
	     (string=? "False"
		       (const-to-name (term-in-const-form-to-const kernel))))
	(make-token-tree 'atom "F"))
       (else (make-token-tree 'atom "" (term-to-token-tree kernel))))))
   ((prime-predicate-form? formula)
    (let* ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula))
	   (pred-string
	    (cond ((pvar-form? pred) (pvar-to-string pred))
		  ((predconst-form? pred) (predconst-to-string pred))
		  ((idpredconst-form? pred) (idpredconst-to-string pred))
		  (else (myerror "formula-to-token-tree" "predicate expected"
				 pred))))
	   (name
	    (cond ((pvar-form? pred) (pvar-to-name pred))
		  ((predconst-form? pred) (predconst-to-name pred))
		  ((idpredconst-form? pred) (idpredconst-to-name pred))
		  (else (myerror "formula-to-token-tree" "predicate expected"
				 pred))))
	   (infix? (or (and (predconst-form? pred)
			    (let ((info (assoc name PREDCONST-DISPLAY)))
			      (and info (eq? 'pred-infix (cadr info)))))
		       (and (idpredconst-form? pred)
			    (let ((info (assoc name IDPREDCONST-DISPLAY)))
			      (and info (eq? 'pred-infix (cadr info))))))))
      (if infix?
	  (apply make-token-tree (append (list 'pred-infix pred-string)
					 (map term-to-token-tree args)))
	  (do ((l args (cdr l))
	       (res (predicate-to-token-tree pred)
		    (let ((arg (car l)))
		      (make-token-tree
		       'predapp ""
		       res
		       (term-to-token-tree arg)))))
	      ((null? l) res)))))
   ((imp-form? formula)
    (make-token-tree
     'imp-op " -> "
     (formula-to-token-tree (imp-form-to-premise formula))
     (formula-to-token-tree (imp-form-to-conclusion formula))))
   ((impnc-form? formula)
    (make-token-tree
     'imp-op " --> "
     (formula-to-token-tree (impnc-form-to-premise formula))
     (formula-to-token-tree (impnc-form-to-conclusion formula))))
   ((and-form? formula)
    (make-token-tree
     'and-op " & "
     (formula-to-token-tree (and-form-to-left formula))
     (formula-to-token-tree (and-form-to-right formula))))
   ((tensor-form? formula)
    (make-token-tree
     'tensor-op " ! "
     (formula-to-token-tree (tensor-form-to-left formula))
     (formula-to-token-tree (tensor-form-to-right formula))))
   ((andd-form? formula)
    (make-token-tree
     'and-op " andd "
     (formula-to-token-tree (andd-form-to-left formula))
     (formula-to-token-tree (andd-form-to-right formula))))
   ((andl-form? formula)
    (make-token-tree
     'and-op " andl "
     (formula-to-token-tree (andl-form-to-left formula))
     (formula-to-token-tree (andl-form-to-right formula))))
   ((andr-form? formula)
    (make-token-tree
     'and-op " andr "
     (formula-to-token-tree (andr-form-to-left formula))
     (formula-to-token-tree (andr-form-to-right formula))))
   ((andnc-form? formula)
    (make-token-tree
     'and-op " andnc "
     (formula-to-token-tree (andnc-form-to-left formula))
     (formula-to-token-tree (andnc-form-to-right formula))))
   ((ord-form? formula)
    (make-token-tree
     'or-op " ord "
     (formula-to-token-tree (ord-form-to-left formula))
     (formula-to-token-tree (ord-form-to-right formula))))
   ((orl-form? formula)
    (make-token-tree
     'or-op " orl "
     (formula-to-token-tree (orl-form-to-left formula))
     (formula-to-token-tree (orl-form-to-right formula))))
   ((orr-form? formula)
    (make-token-tree
     'or-op " orr "
     (formula-to-token-tree (orr-form-to-left formula))
     (formula-to-token-tree (orr-form-to-right formula))))
   ((oru-form? formula)
    (make-token-tree
     'or-op " oru "
     (formula-to-token-tree (oru-form-to-left formula))
     (formula-to-token-tree (oru-form-to-right formula))))
   ((ornc-form? formula)
    (make-token-tree
     'or-op " ornc "
     (formula-to-token-tree (ornc-form-to-left formula))
     (formula-to-token-tree (ornc-form-to-right formula))))
   ((all-form? formula)
    (make-token-tree
     'all-op (var-to-string (all-form-to-var formula))
     (formula-to-token-tree (all-form-to-kernel formula))))
   ((ex-form? formula)
    (make-token-tree
     'ex-op (var-to-string (ex-form-to-var formula))
     (formula-to-token-tree (ex-form-to-kernel formula))))
   ((allnc-form? formula)
    (make-token-tree
     'allnc-op (var-to-string (allnc-form-to-var formula))
     (formula-to-token-tree (allnc-form-to-kernel formula))))
   ((exd-form? formula)
    (make-token-tree
     'exd-op (var-to-string (exd-form-to-var formula))
     (formula-to-token-tree (exd-form-to-kernel formula))))
   ((exl-form? formula)
    (make-token-tree
     'exl-op (var-to-string (exl-form-to-var formula))
     (formula-to-token-tree (exl-form-to-kernel formula))))
   ((exr-form? formula)
    (make-token-tree
     'exr-op (var-to-string (exr-form-to-var formula))
     (formula-to-token-tree (exr-form-to-kernel formula))))
   ((exnc-form? formula)
    (make-token-tree
     'exnc-op (var-to-string (exnc-form-to-var formula))
     (formula-to-token-tree (exnc-form-to-kernel formula))))
   ((exdt-form? formula)
    (make-token-tree
     'exdt-op (var-to-string (exdt-form-to-var formula))
     (formula-to-token-tree (exdt-form-to-kernel formula))))
   ((exlt-form? formula)
    (make-token-tree
     'exlt-op (var-to-string (exlt-form-to-var formula))
     (formula-to-token-tree (exlt-form-to-kernel formula))))
   ((exrt-form? formula)
    (make-token-tree
     'exrt-op (var-to-string (exrt-form-to-var formula))
     (formula-to-token-tree (exrt-form-to-kernel formula))))
   ((exnct-form? formula)
    (make-token-tree
     'exnct-op (var-to-string (exnct-form-to-var formula))
     (formula-to-token-tree (exnct-form-to-kernel formula))))
   ((exca-form? formula)
    (make-token-tree
     'exca-op (map var-to-string (exca-form-to-vars formula))
     (formula-to-token-tree (exca-form-to-kernel formula))))
   ((excl-form? formula)
    (make-token-tree
     'excl-op (map var-to-string (excl-form-to-vars formula))
     (formula-to-token-tree (excl-form-to-kernel formula))))
   ((excu-form? formula)
    (make-token-tree
     'excu-op (map var-to-string (excu-form-to-vars formula))
     (formula-to-token-tree (excu-form-to-kernel formula))))
   (else
    (myerror "formula-to-token-tree" "formula expected" formula))))

(define (formula-to-name-tree formula)
  (cond
   ((atom-form? formula)
    (term-to-name-tree (atom-form-to-kernel formula)))
   ((prime-predicate-form? formula)
    (let* ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula))
	   (pred-string
	    (cond ((pvar-form? pred) (pvar-to-string pred))
		  ((predconst-form? pred) (predconst-to-string pred))
		  ((idpredconst-form? pred) (idpredconst-to-string pred))
		  (else (myerror "formula-to-name-tree" "predicate expected"
				 pred)))))
      (apply list pred-string (map term-to-name-tree args))))
   ((bicon-form? formula)
    (list (formula-to-name-tree (bicon-form-to-left formula))
	  (bicon-form-to-bicon formula)
	  (formula-to-name-tree (bicon-form-to-right formula))))
   ((quant-form? formula)
    (list (quant-form-to-quant formula)
	  (map term-to-name-tree
	       (map make-term-in-var-form (quant-form-to-vars formula)))
	  (formula-to-name-tree (quant-form-to-kernel formula))))
   (else (myerror "formula-to-name-tree" "formula expected" formula))))

;; ppn (pretty print with names) helps to see the implicit coercions
;; for nat sub pos sub int sub rat sub rea.

(define (ppn x)
  (cond
   ((term-form? x)
    (term-to-name-tree (rename-variables x)))
   ((formula-form? x)
    (formula-to-name-tree (fold-formula (rename-variables x))))
   ((string? x)
    (formula-to-name-tree
     (let ((info1 (assoc x THEOREMS)))
       (if info1
	   (fold-formula
	    (rename-variables
	     (proof-to-formula (theorem-name-to-proof x))))
	   (let ((info2 (assoc x GLOBAL-ASSUMPTIONS)))
	     (if info2
		 (fold-formula
		  (rename-variables (aconst-to-formula (cadr info2))))
		 (myerror
		  "ppn" "name of theorem or global assumption expected"
		  x)))))))
   (else (myerror "ppn" "term or formula expected" x))))

;; 7-6. Check
;; ==========

;; check-formula is a test function for formulas.  If the argument is
;; not a formula, an error is returned.

(define (check-formula x)
  (if (not (pair? x)) (myerror "check-formula" "formula expected" x))
  (cond
   ((atom-form? x)
    (let ((kernel (atom-form-to-kernel x)))
      (check-term kernel)
      (if (not (string=? "boole" (type-to-string (term-to-type kernel))))
	  (myerror "check-formula"
		   "atom should have an argument of type boole"
		   (term-to-type kernel)))
      #t))
   ((prime-predicate-form? x)
    (let ((pred (predicate-form-to-predicate x))
	  (args (predicate-form-to-args x)))
      (map check-term args)
      (cond ((pvar-form? pred)
	     (if (not (pvar? pred))
		 (myerror "check-formula" "pvar expected" x)))
	    ((predconst-form? pred)
	     (if (not (predconst? pred))
		 (myerror "check-formula" "predconst expected" x)))
	     ;; (if (member (predconst-to-name pred)
	     ;; 		 (list "Total" "TotalNc" "CoTotal" "CoTotalNc"
	     ;; 		       "TotalMR" "CoTotalMR"))
	     ;; 	 (check-totality-predconst pred)))
	    ((idpredconst-form? pred)
	     (check-idpredconst pred))
	    (else (myerror "check-formula"
			   "pvar, predconst or idpredconst expected" x)))
      (let ((arity (predicate-to-arity pred))
	    (types (map term-to-type args)))
	(if (not (equal? (arity-to-types arity) types))
	    (myerror "check-formula" "equal types expected"
		     (arity-to-types arity) types))))
    #t)
   ((bicon-form? x)
    (let ((left (bicon-form-to-left x))
	  (right (bicon-form-to-right x)))
      (check-formula left)
      (check-formula right)))
   ((quant-form? x)
    (let ((vars (quant-form-to-vars x))
	  (kernel (quant-form-to-kernel x)))
      (do ((l vars (cdr l)))
	  ((null? l))
	(if (not (var? (car l)))
	    (myerror "check-formula" "variable expected" (car l))))
      (check-formula kernel)))
   (else (myerror "check-formula" "formula expected" x))))

;; formula? is a complete test for formula.  Returns true or false.

(define (formula? x)
  (cond
   ((atom-form? x)
    (let ((kernel (atom-form-to-kernel x)))
      (and (term? kernel)
	   (string=? "boole" (type-to-string (term-to-type kernel))))))
   ((prime-predicate-form? x)
    (let ((pred (predicate-form-to-predicate x))
	  (args (predicate-form-to-args x)))
      (and (apply and-op (map term? args))
	   (let ((arity (predicate-to-arity pred))
		 (types (map term-to-type args)))
	     (equal? (arity-to-types arity) types)))))
   ((bicon-form? x)
    (let ((left (bicon-form-to-left x))
	  (right (bicon-form-to-right x)))
      (and (formula? left) (formula? right))))
   ((quant-form? x)
    (let ((vars (quant-form-to-vars x))
	  (kernel (quant-form-to-kernel x)))
      (and (apply and-op (map var? vars))
	   (formula? kernel))))
   (else #f)))

(define cf check-formula)

;; Test function: (cterm-check-to-string x node).  If x is a
;; comprehension term, the result is a string (which should be a
;; readable representation of the comprehension term).  If x is not a
;; comprehension term, an error is raised.

(define (cterm-check-to-string x node)
  (let* ((vars (cterm-to-vars x))
	 (formula (cterm-to-formula x))
	 (string-of-formula
	  (formula-check-to-string formula (append node (list 1))))
	 (result (string-append "(cterm " (vars-to-string vars) " "
				(formula-to-string formula) ")")))
    (do ((l vars (cdr l))
	 (res '() (if
		   (member (car l) (remove (car l) vars))
		   (myerror "cterm-check-to-string" "repeated vars in cterm"
			    vars)
		   (if (variable? (car l))
		       (cons (car l) res)
		       (myerror "cterm-check-to-string" "variable expected"
				(car l))))))
	((null? l)))
    (display-comment (make-string (length node) #\.))
    (display result) (newline)
    result))

;; 7-7. Substitution
;; =================

;; In a simultaneous substitution topsubst for type, object and
;; predicate variables in a formula or a comprehension term it is
;; allowed that the substitution affects vars whose type is changed by
;; topsubst, provided topsubst is admissible for the formula or the
;; comprehension term.

(define (pvar-cterm-equal? pvar cterm)
  (let ((formula (cterm-to-formula cterm)))
    (and (predicate-form? formula)
	 (equal? pvar (predicate-form-to-predicate formula))
	 (equal? (map make-term-in-var-form (cterm-to-vars cterm))
		 (predicate-form-to-args formula)))))

(define (formula-subst formula arg val)
  (let ((equality?
	 (cond
	  ((and (tvar? arg) (type? val)) equal?)
	  ((and (var-form? arg) (term-form? val)) var-term-equal?)
	  ((and (pvar? arg) (cterm-form? val)) pvar-cterm-equal?)
	  (else
	   (myerror "formula-subst" "unexpected arg" arg "and val" val)))))
    (formula-substitute formula (make-subst-wrt equality? arg val))))

(define (cterm-subst cterm arg val)
  (let ((equality?
	 (cond
	  ((and (tvar? arg) (type? val)) equal?)
	  ((and (var-form? arg) (term-form? val)) var-term-equal?)
	  ((and (pvar? arg) (cterm-form? val)) pvar-cterm-equal?)
	  (else (myerror "cterm-subst" "unexpected arg" arg "and val" val)))))
    (cterm-substitute cterm (make-subst-wrt equality? arg val))))

(define (formula-substitute formula topsubst)
  (let* ((tsubst (list-transform-positive topsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (tosubst (list-transform-positive topsubst
		    (lambda (x) (or (tvar-form? (car x))
				    (var-form? (car x)))))))
    (cond
     ((atom-form? formula)
      (make-atomic-formula
       (term-substitute (atom-form-to-kernel formula) tosubst)))
     ((predicate-form? formula)
      (let* ((pred (predicate-form-to-predicate formula))
	     (args (predicate-form-to-args formula))
	     (subst-args (map (lambda (x) (term-substitute x tosubst))
			      args)))
	(cond
	 ((pvar-form? pred)
	  (let ((info (assoc pred topsubst)))
	    (if info
		(let* ((cterm (cadr info))
		       (vars (cterm-to-vars cterm))
		       (formula (cterm-to-formula cterm)))
		  (if
		   (and	DIALECTICA-FLAG
			(or (and (not (pvar-with-positive-content? pred))
				 (not (nulltype?
				       (formula-to-etdp-type formula))))
			    (and (not (pvar-with-negative-content? pred))
				 (not (nulltype?
				       (formula-to-etdn-type formula))))))
		   (myerror
		    "formula-substitute" "formula" formula
		    "has not the right (positive or negative) content for"
		    pred)
		   (formula-substitute
		    formula (make-substitution vars subst-args))))
		(apply make-predicate-formula pred subst-args))))
	 ((predconst-form? pred)
	  (let* ((tsubst0 (predconst-to-tsubst pred))
		 (composed-tsubst (compose-substitutions tsubst0 tsubst))
		 (arity (predconst-to-uninst-arity pred))
		 (new-tsubst (restrict-substitution-wrt
			      composed-tsubst
			      (lambda (x)
				(member x (apply union
						 (map type-to-tvars
						      (arity-to-types
						       arity)))))))
		 (subst-predconst (make-predconst arity
						  new-tsubst
						  (predconst-to-index pred)
						  (predconst-to-name pred))))
	    (apply make-predicate-formula subst-predconst subst-args)))
	 ((idpredconst-form? pred)
	  (let* ((name (idpredconst-to-name pred))
		 (types (idpredconst-to-types pred))
		 (cterms (idpredconst-to-cterms pred))
		 (subst-types
		  (map (lambda (x) (type-substitute x tsubst)) types))
		 (subst-cterms
		  (map (lambda (x) (cterm-substitute x topsubst))
		       cterms))
		 (subst-idpredconst
		  (make-idpredconst name subst-types subst-cterms)))
	    (apply make-predicate-formula subst-idpredconst subst-args)))
	 (else (myerror "formula-substitute" "predicate expected" pred)))))
     ;; ;; An active impnc inactive after substitution is changed to imp
     ;; ((impnc-form? formula)
     ;;  (let* ((prem (impnc-form-to-premise formula))
     ;; 	     (concl (impnc-form-to-conclusion formula))
     ;; 	     (subst-prem (formula-substitute prem topsubst))
     ;; 	     (subst-concl (formula-substitute concl topsubst)))
     ;; 	(if (and (not (formula-of-nulltype? prem))
     ;; 		 (formula-of-nulltype? subst-prem))
     ;; 	    (make-imp subst-prem subst-concl)
     ;; 	    (make-impnc subst-prem subst-concl))))
     ((bicon-form? formula)
      (make-bicon
       (bicon-form-to-bicon formula)
       (formula-substitute (bicon-form-to-left formula) topsubst)
       (formula-substitute (bicon-form-to-right formula) topsubst)))
     ((quant-form? formula)
      (let* ((quant (quant-form-to-quant formula))
	     (vars (quant-form-to-vars formula))
	     (kernel (quant-form-to-kernel formula))
	     (active-substvars
	      (intersection (map car tosubst) (formula-to-free formula)))
	     (active-subst (list-transform-positive tosubst
			     (lambda (x) (member (car x) active-substvars))))
	     (active-terms (map cadr active-subst))
	     (active-psubstvars
	      (intersection (map car topsubst) (formula-to-pvars formula)))
	     (active-psubst (list-transform-positive topsubst
			      (lambda (x) (member (car x) active-psubstvars))))
	     (active-cterms (map cadr active-psubst))
	     (free (apply union (append (map term-to-free active-terms)
					(map cterm-to-free active-cterms))))
	     (new-vars
	      (map
	       (lambda (var)
		 (let ((type (var-to-type var)))
		   (if ;type is not changed
		    (null? (intersection (type-to-tvars type) (map car tsubst)))
		    (if ;there is no clash
		     (not (member var free))
		     var
		     (var-to-new-var var))
		    (if (t-deg-zero? (var-to-t-deg var))
			(type-to-new-partial-var (type-substitute type tsubst))
			(type-to-new-var (type-substitute type tsubst))))))
	       vars))
	     (new-subst (append
			 (make-substitution-wrt
			  var-term-equal?
			  (reverse vars)
			  (reverse (map make-term-in-var-form new-vars)))
			 active-subst)))
	(make-quant
	 quant new-vars (formula-substitute
			 kernel (append tsubst new-subst active-psubst)))))
     (else (myerror "formula-substitute" "formula expected" formula)))))

;; In cterm-substitute renaming is done via an auxiliary formula
;; obtained from the cterm-formula by generalizing cterm-vars.

(define (cterm-substitute cterm topsubst)
  (let* ((vars (cterm-to-vars cterm))
	 (l (length vars))
	 (formula (cterm-to-formula cterm))
	 (aux-formula (apply mk-all (append vars (list formula))))
	 (subst-aux-formula (formula-substitute aux-formula topsubst))
	 (aux-vars-and-kernel
	  (all-form-to-vars-and-final-kernel subst-aux-formula))
	 (aux-vars (car aux-vars-and-kernel))
	 (kernel (cadr aux-vars-and-kernel))
	 (new-vars (list-head aux-vars l))
	 (rest-vars (list-tail aux-vars l))
	 (subst-formula (apply mk-all (append rest-vars (list kernel)))))
    (apply make-cterm (append new-vars (list subst-formula)))))

;; formula-substitute-and-beta0-nf does the same as formula-substitute
;; but also term-substitute-and-beta0-nf.

(define (formula-substitute-and-beta0-nf formula topsubst)
  (let* ((tsubst (list-transform-positive topsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (tosubst (list-transform-positive topsubst
		    (lambda (x) (or (tvar-form? (car x))
				    (var-form? (car x)))))))
    (cond
     ((atom-form? formula)
      (make-atomic-formula
       (term-substitute-and-beta0-nf (atom-form-to-kernel formula) tosubst)))
     ((predicate-form? formula)
      (let* ((pred (predicate-form-to-predicate formula))
	     (args (predicate-form-to-args formula))
	     (subst-args
	      (map (lambda (x) (term-substitute-and-beta0-nf x tosubst))
		   args)))
	(cond
	 ((pvar-form? pred)
	  (let ((info (assoc pred topsubst)))
	    (if info
		(let* ((cterm (cadr info))
		       (vars (cterm-to-vars cterm))
		       (formula (cterm-to-formula cterm)))
		  (if
		   (if DIALECTICA-FLAG
		       (or (and (not (pvar-with-positive-content? pred))
				(not (nulltype?
				      (formula-to-etdp-type formula))))
			   (and (not (pvar-with-negative-content? pred))
				(not (nulltype?
				      (formula-to-etdn-type formula)))))
		       (and (not (pvar-with-positive-content? pred))
			    (not (nulltype? (formula-to-et-type formula)))))
		   (if DIALECTICA-FLAG
		       (myerror
			"formula-substitute-and-beta0-nf" "formula" formula
			"has not the right (positive or negative) content for"
			pred)
		       (myerror "formula-substitute-and-beta0-nf"
				"formula without positive content expected"
				formula))
		   (formula-substitute-and-beta0-nf
		    formula (make-substitution vars subst-args))))
		(apply make-predicate-formula pred subst-args))))
	 ((predconst-form? pred)
	  (let* ((tsubst0 (predconst-to-tsubst pred))
		 (composed-tsubst (compose-substitutions tsubst0 tsubst))
		 (arity (predconst-to-uninst-arity pred))
		 (new-tsubst (restrict-substitution-wrt
			      composed-tsubst
			      (lambda (x)
				(member x (apply union
						 (map type-to-tvars
						      (arity-to-types
						       arity)))))))
		 (predconst (make-predconst arity
					    new-tsubst
					    (predconst-to-index pred)
					    (predconst-to-name pred))))
	    (apply make-predicate-formula predconst subst-args)))
	 ((idpredconst-form? pred)
	  (let* ((name (idpredconst-to-name pred))
		 (types (idpredconst-to-types pred))
		 (cterms (idpredconst-to-cterms pred))
		 (subst-types
		  (map (lambda (x) (type-substitute x tsubst)) types))
		 (subst-cterms
		  (map (lambda (x) (cterm-substitute-and-beta0-nf x topsubst))
		       cterms))
		 (subst-idpredconst
		  (make-idpredconst name subst-types subst-cterms)))
	    (apply make-predicate-formula
		   subst-idpredconst subst-args)))
	 (else (myerror "formula-substitute-and-beta0-nf"
			"predicate expected" pred)))))
     ((bicon-form? formula)
      (make-bicon (bicon-form-to-bicon formula)
		  (formula-substitute-and-beta0-nf
		   (bicon-form-to-left formula) topsubst)
		  (formula-substitute-and-beta0-nf
		   (bicon-form-to-right formula) topsubst)))
     ((quant-form? formula)
      (let* ((quant (quant-form-to-quant formula))
	     (vars (quant-form-to-vars formula))
	     (kernel (quant-form-to-kernel formula))
	     (active-substvars
	      (intersection (map car tosubst) (formula-to-free formula)))
	     (active-subst (list-transform-positive tosubst
			     (lambda (x) (member (car x) active-substvars))))
	     (active-terms (map cadr active-subst))
	     (active-psubstvars
	      (intersection (map car topsubst) (formula-to-pvars formula)))
	     (active-psubst (list-transform-positive topsubst
			      (lambda (x) (member (car x) active-psubstvars))))
	     (active-cterms (map cadr active-psubst))
	     (free (apply union (append (map term-to-free active-terms)
					(map cterm-to-free active-cterms))))
	     (new-vars
	      (map
	       (lambda (var)
		 (let* ((type (var-to-type var))
			(tovars (map car tosubst)))
		   (if ;type is not changed
		    (null? (intersection (type-to-tvars type) (map car tsubst)))
		    (if ;var is not changed and there is no clash
		     (and (not (member var tovars)) (not (member var free)))
		     var
		     (var-to-new-var var))
		    (if (t-deg-zero? (var-to-t-deg var))
			(type-to-new-partial-var (type-substitute type tsubst))
			(type-to-new-var (type-substitute type tsubst))))))
	       vars))
	     (new-subst (append (make-substitution-wrt
				 var-term-equal?
				 vars (map make-term-in-var-form new-vars))
				active-subst)))
	(make-quant
	 quant new-vars (formula-substitute-and-beta0-nf
			 kernel (append tsubst new-subst active-psubst)))))
     (else (myerror "formula-substitute-and-beta0-nf"
		    "formula expected" formula)))))

(define (formula-subst-and-beta0-nf term var term1)
  (formula-substitute-and-beta0-nf term (list (list var term1))))

;; In cterm-substitute-and-beta0-nf renaming is done via an auxiliary
;; formula obtained from the cterm-formula by generalizing cterm-vars.

(define (cterm-substitute-and-beta0-nf cterm topsubst)
  (let* ((vars (cterm-to-vars cterm))
	 (l (length vars))
	 (formula (cterm-to-formula cterm))
	 (aux-formula (apply mk-all (append vars (list formula))))
	 (subst-aux-formula
	  (formula-substitute-and-beta0-nf aux-formula topsubst))
	 (aux-vars-and-kernel
	  (all-form-to-vars-and-final-kernel subst-aux-formula))
	 (aux-vars (car aux-vars-and-kernel))
	 (kernel (cadr aux-vars-and-kernel))
	 (new-vars (list-head aux-vars l))
	 (rest-vars (list-tail aux-vars l))
	 (subst-formula (apply mk-all (append rest-vars (list kernel)))))
    (apply make-cterm (append new-vars (list subst-formula)))))

;; (formula-gen-substitute formula gen-subst) substitutes simultaneously
;; the left hand sides of the alist gen-subst at all occurrences in
;; formula with no free variables captured by the corresponding right
;; hand sides.  gen-subst is an alist associating terms to terms.
;; Renaming takes place if and only if a free variable would become
;; bound.

(define (formula-gen-substitute formula gen-subst)
  (car (formula-gen-substitute-and-newfreeoccs formula gen-subst)))

(define (formula-gen-substitute-and-newfreeoccs formula gen-subst)
  (if
   (null? gen-subst)
   (list formula '())
   (cond
    ((atom-form? formula)
     (let* ((pair (term-gen-substitute-and-newfreeoccs
		   (atom-form-to-kernel formula) gen-subst))
	    (new-kernel (car pair))
	    (new-free-occs (cadr pair)))
       (list (make-atomic-formula new-kernel) new-free-occs)))
    ((predicate-form? formula)
     (let* ((pred (predicate-form-to-predicate formula))
	    (args (predicate-form-to-args formula))
	    (new-pairs (map (lambda (arg) (term-gen-substitute-and-newfreeoccs
					   arg gen-subst))
			    args))
	    (new-args (map car new-pairs))
	    (new-free-occs (apply union (map cadr new-pairs))))
       (cond
	((or (pvar-form? pred) (predconst-form? pred))
	 (list (apply make-predicate-formula pred new-args)
	       new-free-occs))
	((idpredconst-form? pred)
	 (let* ((name (idpredconst-to-name pred))
		(types (idpredconst-to-types pred))
		(cterms (idpredconst-to-cterms pred))
		(new-pairs
		 (map (lambda (cterm)
			(cterm-gen-substitute-and-newfreeoccs cterm gen-subst))
		      cterms))
		(new-cterms (map car new-pairs))
		(new-free-occs (apply union (map cadr new-pairs)))
		(new-idpredconst (make-idpredconst name types new-cterms)))
	   (list (apply make-predicate-formula new-idpredconst new-args)
		 new-free-occs)))
	(else (myerror "formula-gen-substitute-and-newfreeoccs"
		       "predicate expected" pred)))))
    ((bicon-form? formula)
     (let* ((pair1 (formula-gen-substitute-and-newfreeoccs
		    (bicon-form-to-left formula) gen-subst))
	    (pair2 (formula-gen-substitute-and-newfreeoccs
		    (bicon-form-to-right formula) gen-subst))
	    (new-left (car pair1))
	    (new-right (car pair2))
	    (new-free-occs (union (cadr pair1) (cadr pair2))))
       (list (make-bicon (bicon-form-to-bicon formula) new-left new-right)
	     new-free-occs)))
    ((quant-form? formula)
     (let* ((quant (quant-form-to-quant formula))
	    (vars (quant-form-to-vars formula))
	    (kernel (quant-form-to-kernel formula))
					;substitute only those lhss
					;without var from vars
	    (new-subst (do ((s gen-subst (cdr s))
			    (res '() (if (pair? (intersection
						 vars
						 (term-to-free (caar s))))
					 res
					 (cons (car s) res))))
			   ((null? s) (reverse res))))
	    (pair (formula-gen-substitute-and-newfreeoccs kernel new-subst))
	    (new-kernel (car pair))
	    (new-free-occs (cadr pair))
	    (new-vars-and-renaming
	     (do ((l vars (cdr l))
		  (res
		   '(() ())
		   (if (member (car l) new-free-occs)
		       (let ((new-var (var-to-new-var (car l))))
			 (list (cons new-var (car res))
			       (cons (list (car l) (make-term-in-var-form
						    new-var))
				     (cadr res))))
		       (list (cons (car l) (car res)) (cadr res)))))
		 ((null? l) (list (reverse (car res))
				  (reverse (cadr res))))))
	    (new-vars (car new-vars-and-renaming))
	    (renaming (cadr new-vars-and-renaming)))
       (if (null? renaming)
	   (list (make-quant quant vars new-kernel) new-free-occs)
	   (list (make-quant
		  quant new-vars (formula-substitute new-kernel renaming))
		 (set-minus new-free-occs vars)))))
    (else (myerror "formula-gen-substitute-and-newfreeoccs" "formula expected"
		   formula)))))

(define (formula-gen-subst formula term1 term2)
  (formula-gen-substitute formula (make-subst-wrt term=? term1 term2)))

;; In cterm-gen-substitute-and-newfreeoccs renaming is done via an auxiliary
;; formula obtained from the cterm-formula by generalizing cterm-vars.

(define (cterm-gen-substitute-and-newfreeoccs cterm gen-subst)
  (let* ((vars (cterm-to-vars cterm))
	 (l (length vars))
	 (formula (cterm-to-formula cterm))
	 (aux-formula (apply mk-all (append vars (list formula))))
	 (new-pair
	  (formula-gen-substitute-and-newfreeoccs aux-formula gen-subst))
	 (new-aux-formula (car new-pair))
	 (new-free-occs (cadr new-pair))
	 (aux-vars-and-kernel
	  (all-form-to-vars-and-final-kernel new-aux-formula))
	 (aux-vars (car aux-vars-and-kernel))
	 (kernel (cadr aux-vars-and-kernel))
	 (new-vars (list-head aux-vars l))
	 (rest-vars (list-tail aux-vars l))
	 (new-formula (apply mk-all (append rest-vars (list kernel)))))
    (list (apply make-cterm (append new-vars (list new-formula)))
	  new-free-occs)))

;; Display functions for predicate substitutions:

(define (display-p-substitution psubst)
  (display-comment "Predicate substitution:") (newline)
  (for-each (lambda (x)
	      (let* ((pvar (car x))
		     (cterm (cadr x)))
		(if (pvar-form? pvar)
		    (display-comment (pvar-to-string pvar))
		    (myerror "display-p-substitution"
			     "predicate variable expected" pvar))
		(display tab)
		(display "->")
		(display tab)
		(if (cterm-form? cterm)
		    (display (cterm-to-string cterm))
		    (myerror "display-p-substitution" "cterm expected" cterm))
		(newline)))
	    psubst))

(define (display-substitutions top-subst)
  (if (not top-subst) #f)
  (if (not (and (list? top-subst)
		(map and-op (map (lambda (item)
				   (and (list? item)
					(= 2 (length item))))
				 top-subst))))
      (myerror "substitution expected" top-subst))
  (let ((tsubst (list-transform-positive top-subst
		  (lambda (x) (tvar-form? (car x)))))
	(subst (list-transform-positive top-subst
		 (lambda (x) (var-form? (car x)))))
	(psubst (list-transform-positive top-subst
		  (lambda (x) (pvar-form? (car x))))))
    (if (pair? tsubst) (display-t-substitution tsubst))
    (if (pair? subst) (display-substitution subst))
    (if (pair? psubst) (display-p-substitution psubst))))

(define (pp-subst top-subst)
  (do ((s top-subst (cdr s))
       (line "" line))
      ((null? s) (if (> (string-length line) 0)
		     (begin (display-comment line) (newline))))
    (let* ((p (car s))
	   (var (if (pair? p)
		    (car p)
		    (myerror "pp-subst" "substitution item expected" p)))
	   (val (if (pair? (cdr p))
		    (cadr p)
		    (myerror "pp-subst" "substitution item expected" p))))
      (if (tvar-form? var)
	  (let ((string (tvar-to-string var)))
	    (set! line (string-append line "  " string " -> "))
	    (if (> (* 3 (string-length line)) PP-WIDTH)
		(begin
		  (display-comment line)
		  (newline)
		  (set! line "    ")))
	    (set! line (string-append
			line
			(pretty-print-string
			 (string-length line)
			 (- PP-WIDTH (string-length COMMENT-STRING))
			 val)))))
      (if (var-form? var)
	  (let ((string (var-to-string var)))
	    (set! line (string-append line "  " string " -> "))
	    (if (> (* 3 (string-length line)) PP-WIDTH)
		(begin
		  (display-comment line)
		  (newline)
		  (set! line "    ")))
	    (set! line (string-append
			line
			(pretty-print-string
			 (string-length line)
			 (- PP-WIDTH (string-length COMMENT-STRING))
			 val)))))
      (if (pvar-form? var)
	  (let ((string (pvar-to-string var))
		(vars (cterm-to-vars val))
		(fla (cterm-to-formula val)))
	    (set! line (string-append line "  " string " -> "))
	    (if (> (* 3 (string-length line)) PP-WIDTH)
		(begin
		  (display-comment line)
		  (newline)
		  (set! line "    ")))
	    (set! line (string-append
			line " (cterm " (vars-to-string vars) " "))
	    (set! line (string-append
			line
			(pretty-print-string
			 (string-length line)
			 (- PP-WIDTH (string-length COMMENT-STRING))
			 fla)
			")"))))
      (if (pair? (cdr s))
	  (begin (display-comment line) (newline)
		 (set! line ""))))))
