;; 2021-02-24.  term.scm
;; 6. Terms
;; ========

;; 6-1. Constructors and accessors
;; ===============================

;; Terms are built from (typed) variables and constants by abstraction,
;; application, pairing, formation of left and right components
;; (i.e., projections) and the if-construct.  Terms always have the form
;; (tag type ...) where ... is a list with further information.

(define tag car)
(define term-to-type cadr)

;; Constructors, accessors and test for terms in variable form:
;; (term-in-var-form type string var)

(define (make-term-in-var-form var)
  (if (var-form? var)
      (list 'term-in-var-form
	    (var-to-type var)
	    var)
      (myerror "make-term-in-var-form" "variable expected" var)))

(define term-in-var-form-to-var caddr)

(define (term-in-var-form-to-string term)
  (var-to-string (term-in-var-form-to-var term)))

(define (term-in-var-form? term)
  (eq? 'term-in-var-form (tag term)))

;; Constructor, accessor and test for terms in constant form:
;; (term-in-const-form type const)

(define (make-term-in-const-form const)
  (if (const-form? const)
      (list 'term-in-const-form
	    (const-to-type const)
	    const)
      (myerror "make-term-in-const-form" "constant expected" const)))

(define term-in-const-form-to-const caddr)
(define (term-in-const-form? term) (eq? 'term-in-const-form (tag term)))

;; Constructors, accessors and test for abstractions:

(define (make-term-in-abst-form var term)
  (list 'term-in-abst-form
	(make-arrow (var-to-type var) (term-to-type term))
	var
	term))

(define term-in-abst-form-to-var caddr)
(define term-in-abst-form-to-kernel cadddr)

(define (term-in-abst-form? term)
  (eq? 'term-in-abst-form (tag term)))

;; (mk-term-in-abst-form var1 ... term) is formed from term by first
;; abstracting var1, then var2 and so on.

(define (mk-term-in-abst-form x . rest)
  (if (null? rest)
      x
      (if (var-form? x)
	  (let ((prev (apply mk-term-in-abst-form rest)))
	    (make-term-in-abst-form x prev))
	  (myerror "mk-term-in-abst-form" "variable expected" x))))

(define (term-in-abst-form-to-kernel-and-vars term)
  (if (term-in-abst-form? term)
      (let* ((prev (term-in-abst-form-to-kernel-and-vars
		    (term-in-abst-form-to-kernel term)))
             (prev-kernel (car prev))
             (prev-vars (cdr prev)))
        (cons prev-kernel (cons (term-in-abst-form-to-var term) prev-vars)))
      (list term)))

;; term-in-abst-form-to-vars computes the first (car x) abstracted vars

(define (term-in-abst-form-to-vars term . x)
  (cond ((null? x)
	 (if (term-in-abst-form? term)
	     (cons (term-in-abst-form-to-var term)
		   (term-in-abst-form-to-vars
		    (term-in-abst-form-to-kernel term)))
	     '()))
	((and (integer? (car x)) (not (negative? (car x))))
	 (let ((n (car x)))
	   (do ((r term (term-in-abst-form-to-kernel r))
		(i 0 (+ 1 i))
		(res '() (cons (term-in-abst-form-to-var r) res)))
	       ((or (= n i) (not (term-in-abst-form? r)))
		(if (= n i)
		    (reverse res)
		    (myerror "term-in-abst-form-to-vars"
			     n "abstracted vars expected in"
			     term))))))
	(else (myerror "term-in-abst-form-to-vars" "number expected"
		       (car x)))))

;; term-in-abst-form-to-final-kernel computes the final kernel (kernel
;; after removing the first (car x) variables)

(define (term-in-abst-form-to-final-kernel term . x)
  (cond ((null? x)
	 (if (term-in-abst-form? term)
	     (term-in-abst-form-to-final-kernel
	      (term-in-abst-form-to-kernel term))
	     term))
	((and (integer? (car x)) (not (negative? (car x))))
	 (let ((n (car x)))
	   (do ((r term (term-in-abst-form-to-kernel r))
		(i 0 (+ 1 i))
		(res term (term-in-abst-form-to-kernel res)))
	       ((or (= n i) (not (term-in-abst-form? r)))
		(if (= n i)
		    res
		    (myerror "term-in-abst-form-to-final-kernel"
			     n " abstracted vars expected in"
			     term))))))
	(else (myerror "term-in-abst-form-to-final-kernel" "number expected"
		       (car x)))))

(define (abstraction-closure term)
  (apply mk-term-in-abst-form (append (term-to-free term) (list term))))

;; Constructors, accessors and test for applications:

;; Changed 2004-01-10, to enable overloading and coercion when working
;; with rationals.

(define (make-term-in-app-form term1 term2)
  (let ((type1 (term-to-type term1))
	(type2 (term-to-type term2)))
    (if
     (arrow-form? type1)
     (let ((arg-type (arrow-form-to-arg-type type1))
	   (val-type (arrow-form-to-val-type type1)))
       (if
	(type-le? type2 arg-type)
	(list 'term-in-app-form val-type term1
	      ((types-to-embedding type2 arg-type) term2))
	(myerror
	    "make-term-in-app-form" "unexpected terms.  Operator:"
	    term1 "with argument type" arg-type
	    "Argument:" term2 "of type" type2)))
     (myerror "make-term-in-app-form" "arrow form expected" type1))))

(define term-in-app-form-to-op caddr)
(define term-in-app-form-to-arg cadddr)

(define (term-in-app-form? term) (eq? 'term-in-app-form (tag term)))

(define (mk-term-in-app-form term . terms)
  (if (null? terms)
      term
      (let ((type (term-to-type term)))
	(case (tag type)
	  ((tvar tconst alg)
	   (myerror "mk-term-in-app-form" "applicable type expected" type))
	  ((arrow)
	   (apply mk-term-in-app-form
		  (make-term-in-app-form term (car terms))
			(cdr terms)))
	  ((star)
	   (cond ((eq? 'left (car terms))
		  (apply mk-term-in-app-form
			 (make-term-in-lcomp-form term) (cdr terms)))
		 ((eq? 'right (car terms))
		  (apply mk-term-in-app-form
			 (make-term-in-rcomp-form term) (cdr terms)))
		 (else (myerror "mk-term-in-app-form" "left or right expected"
				(car terms)))))
	  (else (myerror "mk-term-in-app-form" "type expected" type))))))

(define (term-in-app-form-to-final-op term)
  (do ((x term (term-in-app-form-to-op x)))
      ((not (term-in-app-form? x)) x)))

(define (term-in-app-form-to-args term)
  (do ((x term (term-in-app-form-to-op x))
       (res '() (cons (term-in-app-form-to-arg x) res)))
      ((not (term-in-app-form? x)) res)))

;; The same again for ``symbolic applications'' (just for printing)

(define (term-in-symbolic-app-form-to-final-op term)
  (do ((x term (term-in-symbolic-app-form-to-op x)))
      ((not (and (term-in-symbolic-app-form? x)
		 (not (is-numeric-term? x)))) x)))

(define (term-in-symbolic-app-form-to-args term)
  (do ((x term (term-in-symbolic-app-form-to-op x))
       (res '() (cons (term-in-symbolic-app-form-to-arg x) res)))
      ((not (and (term-in-symbolic-app-form? x)
		 (not (is-numeric-term? x)))) res)))

;; Finally tell the system that terms in app-form can and should be
;; written as application:

(add-new-application (lambda (type) (arrow-form? type))
		     make-term-in-app-form)

(add-new-application-syntax
 term-in-app-form?
 term-in-app-form-to-arg
 term-in-app-form-to-op)

;; Vector notation for recursion:

(add-new-application
 (lambda (type) (and (alg-form? type)
		     (= 1 (length (alg-name-to-simalg-names
				   (alg-form-to-name type))))))
 (lambda (arg first-step-term)
   (let* ((first-step-type (term-to-type first-step-term))
	  (alg-name (alg-form-to-name (term-to-type arg)))
	  (typed-constr-names (alg-name-to-typed-constr-names alg-name))
	  (first-typed-constr-name
	   (typed-constr-name-to-name typed-constr-names))
	  (first-constr-type
	   (typed-constr-name-to-type first-typed-constr-name))
	  (argtypes (arrow-form-to-arg-types first-constr-type))
	  (argvaltypes (map arrow-form-to-final-val-type argtypes))
	  (number-of-rec-argtypes
	   (do ((l argvaltypes (cdr l))
		(res 0 (if (and (alg-form? (car l))
				(string=? (alg-form-to-name (car l)) alg-name))
			   (+ 1 res)
			   res)))
	       ((null? l) res)))
	  (val-type (arrow-form-to-final-val-type
		     first-step-type
		     (+ (length argtypes) number-of-rec-argtypes)))
	  (arrow-type (make-arrow (term-to-type arg) val-type))
	  (rec-const (type-info-to-rec-const arrow-type))
	  (recop-type (const-to-type rec-const))
	  (step-types (cdr (arrow-form-to-arg-types
                            recop-type
                            (+ 1 (length typed-constr-names)))))
	  (vars (map type-to-new-var (cdr step-types)))
	  (var-terms (map make-term-in-var-form vars)))
     (apply mk-term-in-abst-form
	    (append
	     vars (list (apply mk-term-in-app-form
			       (make-term-in-const-form rec-const)
			       arg first-step-term
			       var-terms )))))))

;; For permutative conversion with if-terms we use an application notation:
;; [if n r [m]s] is written as n(r,[n]s).  (r,[n]s) is called gen-arg.

(define (term-in-if-form-to-final-test term)
  (if (term-in-if-form? term)
      (term-in-if-form-to-final-test
       (term-in-if-form-to-test term))
      term))

(define (term-in-if-form-to-gen-args term)
  (if (term-in-if-form? term)
      (let ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term)))
	(append (term-in-if-form-to-gen-args test)
		(list alts)))
      '()))

(define (mk-term-in-if-form term . gen-args)
  (if (null? gen-args)
      term
      (if (alg-form? (term-to-type term))
	  (let ((alts (car gen-args)))
	    (apply mk-term-in-if-form
		   (make-term-in-if-form term alts) (cdr gen-args)))
	  (myerror "mk-term-in-if-form: alg type expected" type))))

(define (gen-args-to-free gen-args)
  (if (null? gen-args)
      '()
      (let* ((gen-arg (car gen-args))
	     (free (if (term-form? gen-arg)
		       (term-to-free gen-arg)
		       (apply union (map term-to-free gen-arg)))))
	(union free (gen-args-to-free (cdr gen-args))))))

;; Constructors, accessors and test for pairs:

(define (make-term-in-pair-form term1 term2)
  (list 'term-in-pair-form
	(make-star (term-to-type term1) (term-to-type term2))
	term1
	term2))

(define term-in-pair-form-to-left caddr)
(define term-in-pair-form-to-right cadddr)

(define (term-in-pair-form? term)
  (eq? 'term-in-pair-form (tag term)))

(define (mk-term-in-pair-form term . rest)
  (if (null? rest)
      term
      (make-term-in-pair-form
       term
       (apply mk-term-in-pair-form rest))))

;; Constructors, accessors and test for the left and right component:

(define (make-term-in-lcomp-form term)
  (let ((type (term-to-type term)))
    (if (star-form? type)
	(list 'term-in-lcomp-form
	      (star-form-to-left-type type)
	      term)
	(myerror "make-term-in-lcomp-form" "star form expected" type))))

(define term-in-lcomp-form-to-kernel caddr)

(define (term-in-lcomp-form? term)
  (eq? 'term-in-lcomp-form (tag term)))

(define (make-term-in-rcomp-form term)
  (let ((type (term-to-type term)))
    (if (star-form? type)
	(list 'term-in-rcomp-form
	      (star-form-to-right-type type)
	      term)
	(myerror "make-term-in-rcomp-form" "star form expected" type))))

(define term-in-rcomp-form-to-kernel caddr)

(define (term-in-rcomp-form? term)
  (eq? 'term-in-rcomp-form (tag term)))

;; Constructors, accessors and test for if-constructs:

;; In make-term-in-if-form a test in pair form (@@) is converted into
;; the same test in cons form (yprod).  This is needed since nbe
;; internally works with (primitive) pairs.

(define (make-term-in-if-form test alts . rest) ;rest empty or all-formula
  (if
   (term-in-pair-form? test)
   (apply make-term-in-if-form
	  (make-term-in-cons-form (term-in-pair-form-to-left test)
				  (term-in-pair-form-to-right test))
	  alts
	  rest)
   (let* ((alg (term-to-type test))
	  (name (alg-form-to-name alg))
	  (typed-constr-names (alg-name-to-typed-constr-names name))
	  (constr-types (map typed-constr-name-to-type typed-constr-names))
	  (lengths-of-arg-types
	   (map (lambda (x) (length (arrow-form-to-arg-types x)))
		constr-types))
	  (types (map (lambda (alt l)
			(arrow-form-to-final-val-type (term-to-type alt) l))
		      alts lengths-of-arg-types))
	  (lub (apply types-lub types))
	  (coerce-ops (map types-to-coercion
			   types (make-list (length types) lub)))
	  (lifted-alts (map (lambda (op alt) (op alt)) coerce-ops alts)))
     (append (list 'term-in-if-form lub test lifted-alts)
	     rest))))

(define term-in-if-form-to-test caddr)
(define term-in-if-form-to-alts cadddr)
(define term-in-if-form-to-rest cddddr)

(define (term-in-if-form-to-all-formula x)
  (let ((rest (cddddr x)))
    (if (null? rest)
	(myerror "term-in-if-form-to-all-formula" "no all formula present")
	(car rest))))

(define (term-in-if-form? term)
  (eq? 'term-in-if-form (tag term)))

(define (term-form? x)
  (and (pair? x)
       (memq (tag x) '(term-in-var-form
		       term-in-const-form
		       term-in-abst-form
		       term-in-app-form
		       term-in-pair-form
		       term-in-lcomp-form
		       term-in-rcomp-form
		       term-in-if-form))))

(define (make-term-in-pair-form-wrt-yprod term1 term2)
  (let* ((type1 (term-to-type term1))
	 (type2 (term-to-type term2))
	 (tsubst (make-substitution (list (py "alpha1") (py "alpha2"))
				    (list type1 type2)))
	 (constr (const-substitute
		  (term-in-const-form-to-const
		   (pt "(PairConstr alpha1 alpha2)"))
		  tsubst #t)))
    (mk-term-in-app-form (make-term-in-const-form constr) term1 term2)))

;; Code discarded 2021-02-13
;; (define (make-term-in-pair-form-wrt-yprod term1 term2)
;;   (let* ((type1 (term-to-type term1))
;; 	 (type2 (term-to-type term2))
;; 	 (tsubst (make-substitution (list (py "alpha1") (py "alpha2"))
;; 				    (list type1 type2)))
;; 	 (constr (constr-name-to-constr "PairConstr" tsubst)))
;;     (mk-term-in-app-form (make-term-in-const-form constr) term1 term2)))

(define (make-term-in-lcomp-form-wrt-yprod term)
  (let* ((type (term-to-type term))
	 (type1 (if (yprod-form? type)
		    (yprod-form-to-left-type type)
		    (myerror "make-term-in-lcomp-form-wrt-yprod"
			     "yprod-form expected" type)))
	 (type2 (yprod-form-to-right-type type))	 
	 (tsubst (make-substitution (list (py "alpha1") (py "alpha2"))
				    (list type1 type2)))
	 (pconst (pconst-name-to-pconst "PairOne"))
	 (info (assoc "PairOne" PROGRAM-CONSTANTS))
	 (info1 (assoc-wrt substitution-equal? tsubst (car (cddddr info))))
	 (subst-pconst ;updates PROGRAM-CONSTANTS if not yet done
	  (const-substitute pconst tsubst (if info1 #t #f))))
    (make-term-in-app-form (make-term-in-const-form subst-pconst) term)))

(define (make-term-in-rcomp-form-wrt-yprod term)
  (let* ((type (term-to-type term))
	 (type1 (if (yprod-form? type)
		    (yprod-form-to-left-type type)
		    (myerror "make-term-in-lcomp-form-wrt-yprod"
			     "yprod-form expected" type)))
	 (type2 (yprod-form-to-right-type type))	 
	 (tsubst (make-substitution (list (py "alpha1") (py "alpha2"))
				    (list type1 type2)))
	 (pconst (pconst-name-to-pconst "PairTwo"))
	 (info (assoc "PairTwo" PROGRAM-CONSTANTS))
	 (info1 (assoc-wrt substitution-equal? tsubst (car (cddddr info))))
	 (subst-pconst ;updates PROGRAM-CONSTANTS if not yet done
	  (const-substitute pconst tsubst (if info1 #t #f))))
    (make-term-in-app-form (make-term-in-const-form subst-pconst) term)))

;; 6-2.  Alpha equality
;; ====================

;; To define alpha-equality for terms we use (following Robert Staerk)
;; an auxiliary function (corr x y alist alistrev).  Here
;; alist = ((u1 v1) ... (un vn)), alistrev = ((v1 u1) ... (vn un)).

;; (corr x y alist alistrev) iff one of the following holds.
;; 1. There is a first entry (x v) of the form (x _) in alist
;;    and a first entry (y u) of the form (y _) in alistrev,
;;    and we have v=y and u=x.
;; 2. There is no entry of the form (x _) in alist
;;    and no entry of the form (y _) in alistrev,
;;    and we have x=y.

(define (corr x y alist alistrev)
  (let ((info-x (assoc x alist))
        (info-y (assoc y alistrev)))
    (if (and info-x info-y)
        (equal? info-x (reverse info-y))
        (and (not info-x) (not info-y) (equal? x y)))))

(define (term=? term1 term2)
  (term=-aux? term1 term2 '() '()))

(define (terms=? terms1 terms2)
  (terms=-aux? terms1 terms2 '() '()))

(define (term=-aux? term1 term2 alist alistrev)
  (or (and (term-in-var-form? term1) (term-in-var-form? term2)
           (corr (term-in-var-form-to-var term1)
		 (term-in-var-form-to-var term2)
		 alist alistrev))
      (and (term-in-const-form? term1) (term-in-const-form? term2)
	   (const=? (term-in-const-form-to-const term1)
		    (term-in-const-form-to-const term2)))
      (and (term-in-abst-form? term1) (term-in-abst-form? term2)
           (let ((var1 (term-in-abst-form-to-var term1))
		 (var2 (term-in-abst-form-to-var term2))
		 (kernel1 (term-in-abst-form-to-kernel term1))
		 (kernel2 (term-in-abst-form-to-kernel term2)))
	     (and (equal? (var-to-type var1) (var-to-type var2))
		  (term=-aux? kernel1 kernel2
			      (cons (list var1 var2) alist)
			      (cons (list var2 var1) alistrev)))))
      (and (term-in-app-form? term1) (term-in-app-form? term2)
           (let ((op1 (term-in-app-form-to-op term1))
                 (op2 (term-in-app-form-to-op term2))
                 (arg1 (term-in-app-form-to-arg term1))
                 (arg2 (term-in-app-form-to-arg term2)))
             (and (term=-aux? op1 op2 alist alistrev)
                  (term=-aux? arg1 arg2 alist alistrev))))
      (and (term-in-pair-form? term1) (term-in-pair-form? term2)
           (let ((left1 (term-in-pair-form-to-left term1))
                 (left2 (term-in-pair-form-to-left term2))
                 (right1 (term-in-pair-form-to-right term1))
                 (right2 (term-in-pair-form-to-right term2)))
             (and (term=-aux? left1 left2 alist alistrev)
                  (term=-aux? right1 right2 alist alistrev))))
      (and (term-in-lcomp-form? term1) (term-in-lcomp-form? term2)
           (let ((kernel1 (term-in-lcomp-form-to-kernel term1))
                 (kernel2 (term-in-lcomp-form-to-kernel term2)))
	     (term=-aux? kernel1 kernel2 alist alistrev)))
      (and (term-in-rcomp-form? term1) (term-in-rcomp-form? term2)
           (let ((kernel1 (term-in-rcomp-form-to-kernel term1))
                 (kernel2 (term-in-rcomp-form-to-kernel term2)))
	     (term=-aux? kernel1 kernel2 alist alistrev)))
      (and (term-in-if-form? term1) (term-in-if-form? term2)
           (let ((test1 (term-in-if-form-to-test term1))
                 (test2 (term-in-if-form-to-test term2))
                 (alts1 (term-in-if-form-to-alts term1))
                 (alts2 (term-in-if-form-to-alts term2)))
             (and (term=-aux? test1 test2 alist alistrev)
                  (terms=-aux?
		   alts1 alts2 alist alistrev))))))

(define (terms=-aux? terms1 terms2 alist alistrev)
  (or (and (null? terms1) (null? terms2))
      (and (term=-aux? (car terms1) (car terms2) alist alistrev)
           (terms=-aux? (cdr terms1) (cdr terms2) alist alistrev))))

;; 6-3.  Operations on terms, display
;; ==================================

(define (term-to-free term)
  (case (tag term)
    ((term-in-var-form) (list (term-in-var-form-to-var term)))
    ((term-in-const-form) '())
    ((term-in-abst-form)
     (let* ((var (term-in-abst-form-to-var term))
	    (kernel (term-in-abst-form-to-kernel term))
	    (free (term-to-free kernel)))
       (remove var free)))
    ((term-in-app-form)
     (let ((free1 (term-to-free (term-in-app-form-to-op term)))
	   (free2 (term-to-free (term-in-app-form-to-arg term))))
       (union free1 free2)))
    ((term-in-pair-form)
     (union (term-to-free (term-in-pair-form-to-left term))
	    (term-to-free (term-in-pair-form-to-right term))))
    ((term-in-lcomp-form)
     (term-to-free (term-in-lcomp-form-to-kernel term)))
    ((term-in-rcomp-form)
     (term-to-free (term-in-rcomp-form-to-kernel term)))
    ((term-in-if-form)
     (apply union (map term-to-free
		       (cons (term-in-if-form-to-test term)
			     (term-in-if-form-to-alts term)))))
    (else (myerror "term-to-free" "term expected" term))))

(define (term-to-bound term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) '())
    ((term-in-abst-form)
     (let* ((var (term-in-abst-form-to-var term))
	    (kernel (term-in-abst-form-to-kernel term))
	    (bound (term-to-bound kernel)))
       (adjoin var bound)))
    ((term-in-app-form)
     (let ((bound1 (term-to-bound (term-in-app-form-to-op term)))
	   (bound2 (term-to-bound (term-in-app-form-to-arg term))))
       (union bound1 bound2)))
    ((term-in-pair-form)
     (union (term-to-bound (term-in-pair-form-to-left term))
	    (term-to-bound (term-in-pair-form-to-right term))))
    ((term-in-lcomp-form)
     (term-to-bound (term-in-lcomp-form-to-kernel term)))
    ((term-in-rcomp-form)
     (term-to-bound (term-in-rcomp-form-to-kernel term)))
    ((term-in-if-form)
     (apply union (map term-to-bound
		       (cons (term-in-if-form-to-test term)
			     (term-in-if-form-to-alts term)))))
    (else (myerror "term-to-bound" "term expected" term))))

(define (term-to-tvars term)
  (case (tag term)
    ((term-in-var-form)
     (type-to-tvars (var-to-type (term-in-var-form-to-var term))))
    ((term-in-const-form)
     (type-to-tvars (const-to-type (term-in-const-form-to-const term))))
    ((term-in-abst-form)
     (let* ((var (term-in-abst-form-to-var term))
	    (kernel (term-in-abst-form-to-kernel term))
	    (tvars1 (type-to-tvars (var-to-type var)))
	    (tvars2 (term-to-tvars kernel)))
       (union tvars1 tvars2)))
    ((term-in-app-form)
     (let ((tvars1 (term-to-tvars (term-in-app-form-to-op term)))
	   (tvars2 (term-to-tvars (term-in-app-form-to-arg term))))
       (union tvars1 tvars2)))
    ((term-in-pair-form)
     (union (term-to-tvars (term-in-pair-form-to-left term))
	    (term-to-tvars (term-in-pair-form-to-right term))))
    ((term-in-lcomp-form)
     (term-to-tvars (term-in-lcomp-form-to-kernel term)))
    ((term-in-rcomp-form)
     (term-to-tvars (term-in-rcomp-form-to-kernel term)))
    ((term-in-if-form)
     (apply union (map term-to-tvars
		       (cons (term-in-if-form-to-test term)
			     (term-in-if-form-to-alts term)))))
    (else (myerror "term-to-tvars" "term expected" term))))

;; Finally we need an operation assigning to every term its degree of
;; totality, which can be t-deg-zero (i.e., 0) or else t-deg-one (i.e.,
;; 1).

(define (term-to-t-deg-aux term bound-vars)
  (case (tag term)
    ((term-in-var-form)
     (let ((var (term-in-var-form-to-var term)))
       (if (member var bound-vars) t-deg-one (var-to-t-deg var))))
    ((term-in-const-form) (const-to-t-deg
			   (term-in-const-form-to-const term)))
    ((term-in-abst-form)
     (let ((var (term-in-abst-form-to-var term))
	   (kernel (term-in-abst-form-to-kernel term)))
       (term-to-t-deg-aux kernel (cons var bound-vars))))
    ((term-in-app-form)
     (let* ((op (term-in-app-form-to-op term))
	    (arg (term-in-app-form-to-arg term))
	    (t-deg-op (term-to-t-deg-aux op bound-vars))
	    (t-deg-arg (term-to-t-deg-aux arg bound-vars)))
       (if (and (t-deg-one? t-deg-op) (t-deg-one? t-deg-arg))
	   t-deg-one
	   t-deg-zero)))
    ((term-in-pair-form)
     (let* ((left (term-in-pair-form-to-left term))
	    (right (term-in-pair-form-to-right term))
	    (t-deg-left (term-to-t-deg-aux left bound-vars))
	    (t-deg-right (term-to-t-deg-aux right bound-vars)))
       (if (and (t-deg-one? t-deg-left) (t-deg-one? t-deg-right))
	   t-deg-one
	   t-deg-zero)))
    ((term-in-lcomp-form)
     (term-to-t-deg-aux (term-in-lcomp-form-to-kernel term) bound-vars))
    ((term-in-rcomp-form)
     (term-to-t-deg-aux (term-in-rcomp-form-to-kernel term) bound-vars))
    ((term-in-if-form)
     (let* ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term))
	    (t-deg-test (term-to-t-deg-aux test bound-vars))
	    (t-deg-alts (map (lambda (x) (term-to-t-deg-aux x bound-vars))
			     alts)))
       (if (apply and-op (t-deg-one? t-deg-test)
		  (map t-deg-one? t-deg-alts))
	   t-deg-one
	   t-deg-zero)))
    (else (myerror "term-to-t-deg-aux" "term expected" term))))

(define (term-to-t-deg term)
  (term-to-t-deg-aux term '()))

(define (synt-total? term)
  (t-deg-one? (term-to-t-deg term)))

(define (term-in-projection-form? term)
  (and (term-in-abst-form? term)
       (let ((vars (term-in-abst-form-to-vars term))
	     (kernel (term-in-abst-form-to-final-kernel term)))
	 (and (term-in-var-form? kernel)
	      (member (term-in-var-form-to-var kernel) vars)))))

;; Allow overloading of tokens (like + * for nat, pos, int, rat, rea
;; or :: ++ for list, str):

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

;; To define the tokens that are used by the parser we provide

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

;; Initially we don't know what numerals look like
(define is-numeric-term? (lambda (term) #f))

(define numeric-term-to-number
  (lambda (term) (myerror "numeric-term-no-number"
			  "This function has to be supplied by the user")))

(define DISPLAY-FUNCTIONS '())

(define (add-display type proc)
  (set! DISPLAY-FUNCTIONS
	(cons (list type proc) DISPLAY-FUNCTIONS)))

(define (add-display-end type proc)
  (set! DISPLAY-FUNCTIONS
	(append DISPLAY-FUNCTIONS (list (list type proc)))))

;; make-display-creator and make-display-creator1 moved here from lib/pos.scm
;; make-param-term-creator2 and make-param-term-creator1 added.  They
;; are used by the parser to create the correct pconsts for overloaded
;; tokens, for algebras with parameters (example: ++ for list and str)

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

(define (make-param-term-creator2 token)
  (lambda (x y)
    (let* ((alg1 (term-to-type x))
	   (name1 (alg-form-to-name alg1))
	   (tvars1 (alg-name-to-tvars name1))
	   (uninst-alg1 (apply make-alg name1 tvars1))
	   (types1 (alg-form-to-types alg1))
	   (alg2 (term-to-type y))
	   (name2 (alg-form-to-name alg2))
	   (tvars2 (alg-name-to-tvars name2))
	   (uninst-alg2 (apply make-alg name2 tvars2))
	   (types2 (alg-form-to-types alg2))
	   (pconst-name
	    (token-and-types-to-name token (list uninst-alg1 uninst-alg2)))
	   (types
	    (cond ((and (pair? types1) (= (length types1) (length types2)))
		   (map (lambda (type1 type2) (types-lub type1 type2))
			 types1 types2))
		  ((null? types1) types2)
		  ((null? types2) types1)
		  (else (myerror "make-param-term-creator2"
				 "parameter types differ in length"
				 alg1 alg2))))
	   (tvars (cond ((equal? tvars1 tvars2) tvars1)
			((null? tvars1) tvars2)
			((null? tvars2) tvars1)
			(else (myerror "make-param-term-creator2"
				       "tvars differ for alg-names"
				       name1 name2))))
	   (tsubst (make-substitution tvars types))
	   (uninst-pconst (pconst-name-to-pconst pconst-name))
	   (pconst (const-substitute uninst-pconst tsubst #t))) ;no update
      (mk-term-in-app-form (make-term-in-const-form pconst) x y))))

(define (make-param-term-creator1 token)
  (lambda (x)
    (let* ((alg (term-to-type x))
	   (name (alg-form-to-name alg))
	   (tvars (alg-name-to-tvars name))
	   (uninst-alg (apply make-alg name tvars))
	   (types (alg-form-to-types alg))
	   (pconst-name (token-and-type-to-name token uninst-alg))
	   (tsubst (make-substitution tvars types))
	   (uninst-pconst (pconst-name-to-pconst pconst-name))
	   (pconst (const-substitute uninst-pconst tsubst #t))) ;no update
      (mk-term-in-app-form (make-term-in-const-form pconst) x))))

(define (term-to-token-tree term)
  (cond
   ((is-numeric-term? term)
    (make-token-tree 'number (numeric-term-to-number term)))
   ((app-term-with-low-original-types? term)
    (default-term-to-token-tree term))
   (else
    (let ((type (term-to-type term)))
      (do ((l DISPLAY-FUNCTIONS (cdr l))
	   (res #f (let* ((item (car l))
			  (pattern (car item)))
		     (if (type-match pattern type)
			 ((cadr item) term)
			 #f))))
	  ((or res (null? l))
	   (cond
	    (res res)
	    ((term-in-symbolic-app-form? term)
	     (let ((op (term-in-symbolic-app-form-to-op term))
		   (arg (term-in-symbolic-app-form-to-arg term)))
	       (if
		(term-in-symbolic-app-form? op)
		(let ((opop (term-in-symbolic-app-form-to-op op))
		      (oparg (term-in-symbolic-app-form-to-arg op)))
		  (if
		   (and
		    (term-in-const-form? opop)
		    (string=? "cId" (const-to-name
				     (term-in-const-form-to-const opop)))
		    (term-in-abst-form? oparg))
		   (let ((var (term-in-abst-form-to-var oparg))
			 (kernel (term-in-abst-form-to-kernel oparg)))
		     (make-token-tree 'if-op "let"
				      (term-to-token-tree
				       (make-term-in-var-form var))
				      (term-to-token-tree arg)
				      (term-to-token-tree kernel)))
		   (make-token-tree 'appterm ""
				    (term-to-token-tree op)
				    (term-to-token-tree arg))))
		(make-token-tree 'appterm ""
				 (term-to-token-tree op)
				 (term-to-token-tree arg)))))
	    (else (default-term-to-token-tree term)))))))))

(define (app-term-with-low-original-types? term)
  (if (not (term-form? term))
      (myerror "app-term-with-low-original-types?"
	       "term expected" term))
  (let ((op (term-in-app-form-to-final-op term)))
    (and
     (term-in-app-form? term)
     (term-in-const-form? op)
     (let* ((const (term-in-const-form-to-const op))
	    (name (const-to-name const))
	    (const-arg-types (arrow-form-to-arg-types (const-to-type const)))
	    (l (length const-arg-types))
	    (args (term-in-app-form-to-args term)))
       (and
	(= (length args) l)
	(or (and
	     (= 2 l)
	     (or (string=? name "=")
		 (string=? name "RatEq")
		 (string=? name "NatPlus")
		 (string=? name "IntPlus")
		 (string=? name "RatPlus")
		 (string=? name "RealPlus")
		 (string=? name "CpxPlus")
		 (string=? name "IntMinus")
		 (string=? name "RatMinus")
		 (string=? name "RealMinus")
		 (string=? name "CpxMinus")
		 (string=? name "NatTimes")
		 (string=? name "IntTimes")
		 (string=? name "RatTimes")
		 (string=? name "RealTimes")
		 (string=? name "CpxTimes")
		 (string=? name "NatExp")
		 (string=? name "IntExp") ;RatExp needs special treatment
		 (string=? name "RealExp")
		 (string=? name "CpxExp")
		 (string=? name "NatMax")
		 (string=? name "IntMax")
		 (string=? name "RatMax")
		 (string=? name "RealMax")
		 (string=? name "CpxMax")
		 (string=? name "NatMin")
		 (string=? name "IntMin")
		 (string=? name "RatMin")
		 (string=? name "RealMin")
		 (string=? name "CpxMin")
		 (string=? name "NatLt")
		 (string=? name "IntLt")
		 (string=? name "RatLt")
		 (string=? name "RealPos")
		 (string=? name "NatLe")
		 (string=? name "IntLe")
		 (string=? name "RatLe"))
	     (let* ((orig-args (map term-to-original args))
		    (orig-arg-types (map term-to-type orig-args))
		    (lub-of-orig-arg-types (apply types-lub orig-arg-types))
		    (alg-name-op (alg-form-to-name (car const-arg-types)))
		    (alg-name-args (alg-form-to-name lub-of-orig-arg-types)))
	       (not (string=? alg-name-op alg-name-args))))
	    (and ;Div only exists for rat, real, cpx
	     (= 2 l)
	     (or (string=? name "RatDiv")
		 (string=? name "RealDiv")
		 (string=? name "CpxDiv"))
	     (let* ((orig-args (map term-to-original args))
		    (orig-arg-types (map term-to-type orig-args))
		    (lub-of-orig-arg-types
		     (apply types-lub (make-alg "rat") orig-arg-types))
		    (alg-name-op (alg-form-to-name (car const-arg-types)))
		    (alg-name-args (alg-form-to-name lub-of-orig-arg-types)))
	       (not (string=? alg-name-op alg-name-args))))
	    (and (= 2 l)
		 (string=? name "RatExp")
		 (let* ((orig-args (map term-to-original args))
			(orig-arg-types (map term-to-type orig-args))
			(orig-arg-type1 (car orig-arg-types))
			(orig-arg-type2 (cadr orig-arg-types))
			(alg-name1 (alg-form-to-name orig-arg-type1))
			(alg-name2 (alg-form-to-name orig-arg-type2)))
		   (and (not (string=? "rat" alg-name1))
			(not (string=? "int" alg-name2)))))
	    (and (= 1 l)
		 (or (string=? name "IntAbs")
		     (string=? name "RatAbs")
		     (string=? name "RealAbs")
		     (string=? name "CpxAbs"))
		 (let* ((orig-arg (term-to-original (car args)))
			(orig-arg-type (term-to-type orig-arg))
			(alg-name-op (alg-form-to-name orig-arg-type))
			(alg-name-arg (alg-form-to-name orig-arg-type)))
		   (not (string=? alg-name-op alg-name-arg))))))))))

(define CASE-DISPLAY #f)
(define OLD-CASE-DISPLAY #f)

(define (default-term-to-token-tree term)
  (case (tag term)
    ((term-in-var-form)
     (make-token-tree 'var (term-in-var-form-to-string term)))
    ((term-in-const-form)
     (make-token-tree 'const (term-in-const-form-to-string term))) ;unfold?
    ((term-in-abst-form)
     (make-token-tree
      'binding-op (var-to-string (term-in-abst-form-to-var term))
      (term-to-token-tree (term-in-abst-form-to-kernel term))))
    ((term-in-app-form)
     (make-token-tree
      'appterm ""
      (term-to-token-tree (term-in-app-form-to-op term))
      (term-to-token-tree (term-in-app-form-to-arg term))))
    ((term-in-pair-form)
     (make-token-tree
      'pair-op "@"
      (term-to-token-tree (term-in-pair-form-to-left term))
      (term-to-token-tree (term-in-pair-form-to-right term))))
    ((term-in-lcomp-form)
     (make-token-tree
      'prefix-op "left"
      (term-to-token-tree (term-in-lcomp-form-to-kernel term))))
    ((term-in-rcomp-form)
     (make-token-tree
      'prefix-op "right"
      (term-to-token-tree (term-in-rcomp-form-to-kernel term))))
    ((term-in-if-form)
     (let* ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term))
	    (alg (term-to-type test))
	    (alg-name (alg-form-to-name alg)))
       (if
	(and CASE-DISPLAY (not (nested-alg-name? alg-name)))
	(let* ((typed-constr-names (alg-name-to-typed-constr-names alg-name))
	       (constr-names (map typed-constr-name-to-name typed-constr-names))
	       (constr-types (map typed-constr-name-to-type typed-constr-names))
	       (alg-tvars (alg-name-to-tvars alg-name))
	       (tparams (alg-form-to-types alg))
	       (tsubst (make-substitution alg-tvars tparams))
	       (constrs (map (lambda (constr-name)
			       (const-substitute
				(constr-name-to-constr constr-name)
				tsubst #t))
			     constr-names))
	       (lengths-of-arg-types
		(map (lambda (x) (length (arrow-form-to-arg-types x)))
		     constr-types))
	       (expanded-alts
		(map (lambda (alt l)
		       (term-to-simple-outer-eta-expansion alt l))
		     alts lengths-of-arg-types))
	       (alt-vars-list (map (lambda (alt l)
				     (term-in-abst-form-to-vars alt l))
				   expanded-alts lengths-of-arg-types))
	       (patterns
		(map (lambda (constr vars)
		       (apply mk-term-in-app-form
			      (make-term-in-const-form constr)
			      (map make-term-in-var-form vars)))
		     constrs alt-vars-list))
	       (alt-kernels (map (lambda (alt l)
				   (term-in-abst-form-to-final-kernel alt l))
				 expanded-alts lengths-of-arg-types)))
	  (apply make-token-tree
		 'case-op "case"
		 (term-to-token-tree test)
		 (map (lambda (pattern alt-kernel)
			(make-token-tree 'caseitem-op " -> "
					 (term-to-token-tree pattern)
					 (term-to-token-tree alt-kernel)))
		      patterns alt-kernels)))
	(apply make-token-tree
	       'if-op "if"
	       (term-to-token-tree (term-in-if-form-to-test term))
	       (map term-to-token-tree
		    (term-in-if-form-to-alts term))))))
    (else (myerror "default-term-to-token-tree" "term expected" term))))

(define (term-to-simple-outer-eta-expansion term . opt-number)
  (let* ((type (term-to-type term))
	 (l (if (pair? opt-number)
		(if (and (integer? (car opt-number))
			 (not (negative? (car opt-number)))
			 (<= (car opt-number)
			     (length (arrow-form-to-arg-types type))))
		    (car opt-number)
		    (myerror
		     "term-to-simple-outer-eta-expansion"
		     "non-negative integer <= length of arg-types expected"
		     (car opt-number)))
		(length (arrow-form-to-arg-types type)))))
    (if (or (= 0 l) (not (arrow-form? type)))
	term
	(if (term-in-abst-form? term)
	    (let ((var (term-in-abst-form-to-var term))
		  (kernel (term-in-abst-form-to-kernel term)))
	      (make-term-in-abst-form
	       var (term-to-simple-outer-eta-expansion kernel (- l 1))))
	    (let* ((arg-type (arrow-form-to-arg-type type))
		   (val-type (arrow-form-to-val-type type))
		   (var (type-to-new-var arg-type)))
	      (rename-variables
	       (make-term-in-abst-form
		var (term-to-simple-outer-eta-expansion
		     (make-term-in-app-form
		      term (make-term-in-var-form var))
		     (- l 1)))))))))

(define (type-info-to-rec-string fst . rest)
  (let* ((param-types (if (number? fst) (list-head rest fst) '()))
	 (arrow-types (if (number? fst) (list-tail rest fst) (cons fst rest)))
	 (f (length param-types))
	 (type-strings (map type-to-string (append param-types arrow-types)))
	 (strings (if (zero? f) type-strings
		      (cons (number-to-string f) type-strings)))
	 (strings-with-sep (map (lambda (x) (string-append " " x)) strings)))
    (apply string-append "(" "Rec" (append strings-with-sep (list ")")))))

(define (term-in-const-form-to-string term)
  (let* ((const (term-in-const-form-to-const term))
	 (name (const-to-name const))
	 (tvars (const-to-tvars const))
	 (tsubst (const-to-tsubst const)))
    (cond
     ((string=? "Rec" name)
      (let* ((uninst-arrow-types (rec-const-to-uninst-arrow-types const))
	     (inst-arrow-types (map (lambda (x) (type-substitute x tsubst))
				    uninst-arrow-types))
	     (type-strings (map type-to-string inst-arrow-types))
	     (strings-with-sep
	      (map (lambda (x) (string-append " " x)) type-strings)))
        (apply string-append "(" name (append strings-with-sep (list ")")))))
     ((string=? "Cases" name)
      (let* ((uninst-type (const-to-uninst-type const))
	     (alg-type (arrow-form-to-arg-type uninst-type))
             (val-type (arrow-form-to-final-val-type uninst-type))
             (uninst-arrow-type (make-arrow alg-type val-type))
             (subst-arrow-type (type-substitute uninst-arrow-type tsubst))
             (type-string (type-to-string subst-arrow-type)))
	(string-append "(" name " " type-string ")")))
     ((string=? "GRecGuard" name)
      (let* ((uninst-type-info (grecguard-const-to-uninst-type-info const))
	     (inst-type-info (map (lambda (x) (type-substitute x tsubst))
				  uninst-type-info))
	     (type-strings (map type-to-string inst-type-info))
	     (strings-with-sep
	      (map (lambda (x) (string-append " " x)) type-strings)))
        (apply string-append "(" name (append strings-with-sep (list ")")))))
     ((string=? "GRec" name) ;obsolete
      (let* ((type (const-to-type const))
             (measure-type (arrow-form-to-arg-type type))
             (arg-types (arrow-form-to-arg-types measure-type))
             (m (length arg-types))
             (val-type (arrow-form-to-final-val-type type (+ m 2)))
             (strings (map type-to-string (append arg-types (list val-type))))
             (strings-with-sep
	      (map (lambda (x) (string-append " " x)) strings)))
        (apply string-append "(" name (append strings-with-sep (list ")")))))
     ((string=? "CoRec" name)
      (let* ((uninst-alg-or-arrow-types
	      (corec-const-to-uninst-alg-or-arrow-types const))
	     (inst-alg-or-arrow-types (map (lambda (x)
					     (type-substitute x tsubst))
					   uninst-alg-or-arrow-types))
	     (type-strings (map type-to-string inst-alg-or-arrow-types))
	     (strings-with-sep
	      (map (lambda (x) (string-append " " x)) type-strings)))
        (apply string-append "(" name (append strings-with-sep (list ")")))))
     ((string=? "Destr" name)
      (let* ((alg (arrow-form-to-arg-type (const-to-type const)))
	     (type-string (type-to-string alg)))
	(string-append "(" name " " type-string ")")))
     ((string=? "SE" name) name)
     (else
      (if
       (or (null? tvars) CASE-DISPLAY)
       name
       (let* ((types (map (lambda (x) (type-substitute x tsubst)) tvars))
	      (strings (map type-to-string types))
	      (strings1 (if (< 1 (length strings))
			    (map (lambda (x)
				   (if (memq #\space (string->list x))
				       (string-append "(" x ")")
				       x))
				 strings)
			    strings))
	      (strings-with-sep
	       (map (lambda (string) (string-append " " string))
		    strings1)))
	 (apply string-append
		"(" name (append strings-with-sep (list ")")))))))))

;; term-to-external-expr aims at producing a readable Scheme/Haskell
;; expression that can be evaluated (work of Fredrik Nordvall Forsberg).

;; The case for Scheme, it transforms an application of a program
;; constant c to args, where c has a corresponding built-in Scheme
;; operator written in uncurried form with (length args) many
;; arguments, into the corresponding Scheme expression.  Example:
;; ((NatLe r1) r2) is transformed into (<= e1 e2).  If however c is
;; applied to fewer arguments, then the default translation of c is
;; used.  Example: (NatLe r1) is transformed into (|NatLe| e1).  To run
;; this expression one needs to define the default translation of c on
;; the Scheme level, in curried form.  Example: (define |NatLe| (lambda
;; (x) (lambda (y) (<= x y)))).  For the usual built-in operators this
;; can be done globally.  For constants occurring in a special example
;; it must be done locally.  Example: in the gcd example we have the
;; Step function.  The general term-to-external-expr produces (by
;; default) |Step|, and then in gcd.scm |Step| needs to be defined on
;; the Scheme level.  By default |Step| is treated as a curried
;; function.  However, with an optional argument '("Step" 4) in
;; term-to-external-expr one can enforce that |Step| is treated as a
;; function with four arguments.
;
;; Equality with name "=" requires a special treatment: if there are
;; exactly two arguments, it is transformed into an =-expression if the
;; type of = refers to a number type (nat, pos, int or rat), and to an
;; equal?-expression otherwise.  If it is applied to fewer arguments,
;; then one needs FinAlg= as a special default name, since the internal
;; name = cannot be used.
;
;; In term-to-external-expr, terms in numeric form wrt either pos or
;; nat are both displayed as the corresponding number.  Therefore both
;; is-numeric-term-wrt-pos? and is-numeric-term-wrt-nat? have been
;; moved here, and similarly numeric-term-wrt-pos-to-number and
;; numeric-term-wrt-nat-to-number.

(define BUILTIN-HASKELL-ALGEBRAS
  (list "ysumu" "uysum" "ysum" "yprod"
	"boole" "unit" "int" "rat" "list"))

(define BUILTIN-HASKELL-PCONSTS
  (list "RatPlus" "IntPlus" "PosPlus" "NatPlus"
	"RatMinus" "IntMinus" "PosMinus" "NatMinus"
	"RatTimes" "IntTimes" "PosTimes" "NatTimes"
	"RatDiv"
        "RatExp" "IntExp" "PosExp" "NatExp"
        "RatLe" "IntLe" "PosLe" "NatLe"
	"RatLt" "IntLt" "PosLt" "NatLt"
	"RatMax" "IntMax" "PosMax" "NatMax"
	"RatMin" "IntMin" "PosMin" "NatMin"
	"Quot" "Rem"
	"cId"
	"NegConst" "AndConst" "OrConst" "ImpConst"
	"PosToNat"
        "S" "IntS" "PosS"
        "IntPred"
        "PairOne" "PairTwo"
	"ListAppend" "ListAppd" "ListLength" "ListProj" "ListMap"

	"Inhab" ;handled via type classes

	;; used internally by pconst-name-to-haskell-function
        ;; (should never appear in terms):
	"TranslationPosNegForInt" "TranslationPosHalfEven" "TranslationPosAsInt"
        "TranslationNatMinusPosDiff" "TranslationPosPredNonOne"
	"TranslationNumerator" "TranslationDenominator"))

(define RESERVED-HASKELL-NAMES
  (list "Bool" "Char" "Double" "Either" "FilePath"
        "Float" "Int" "Integer" "IO" "IOError"
        "Maybe" "Ordering" "ReadS" "ShowS" "String"
        "Bounded" "Enum" "Eq" "Floating" "Fractional"
        "Functor" "Integral" "Monad" "Num" "Ord"
        "Read" "Real" "RealFloat" "RealFrac" "Show"
        "Rational"
        "EQ" "False" "GT" "Just" "Left" "LT" "Nothing"
        "Right" "True"
        "abs" "acos" "acosh" "all" "and" "any"
        "appendFile" "applyM" "asTypeOf" "asin"
        "asinh" "atan" "atan2" "atanh" "break"
        "catch" "ceiling" "compare" "concat"
        "concatMap" "const" "cos" "cosh" "curry"
        "cycle" "decodeFloat" "div" "divMod" "drop"
        "dropWhile" "elem" "encodeFloat" "enumFrom"
        "enumFromThen" "enumFromThenTo" "enumFromTo"
        "error" "even" "exp" "exponent" "fail"
        "filter" "flip" "floatDigits" "floatRadix"
        "floatRange" "floor" "fmap" "foldl" "foldl1"
        "foldr" "foldr1" "fromEnum" "fromInteger"
        "fromIntegral" "fromRational" "fst" "gcd"
        "getChar" "getContents" "getLine" "head"
        "id" "init" "interact" "ioError"
        "isDenormalized" "isIEEE" "isInfinite"
        "isNaN" "isNegativeZero" "iterate" "last"
        "lcm" "length" "lex" "lines" "log" "logBase"
        "lookup" "map" "mapM" "mapM_" "max"
        "maxBound" "maximum" "maybe" "min" "minBound"
        "minimum" "mod" "negate" "not" "notElem"
        "null" "odd" "or" "otherwise" "pi" "pred"
        "print" "product" "properFraction" "putChar"
        "putStr" "putStrLn" "quot" "quotRem" "read"
        "readFile" "readIO" "readList" "readLn"
        "readParen" "reads" "readsPrec" "realToFrac"
        "recip" "rem" "repeat" "replicate" "return"
        "reverse" "round" "scaleFloat" "scanl"
        "scanl1" "scanr" "scanr1" "seq" "sequence"
        "sequence_" "show" "showChar" "showList"
        "showParen" "showString" "shows" "showsPrec"
        "significand" "signum" "sin" "sinh" "snd"
        "span" "splitAt" "sqrt" "subtract" "succ"
        "sum" "tail" "take" "takeWhile" "tan" "tanh"
        "toEnum" "toInteger" "toRational" "truncate"
        "uncurry" "undefined" "unlines" "until"
        "unwords" "unzip" "unzip3" "userError"
        "words" "writeFile" "zip" "zip3" "zipWith"
        "zipWith3"
        ;; from Data.List
        "(++)" "head" "last" "tail" "init" "null" "length"
        "map" "reverse" "intersperse" "intercalate" "transpose"
        "subsequences" "permutations" "foldl" "foldl"
        "foldl1" "foldl1" "foldr" "foldr1" "concat" "concatMap"
        "and" "or" "any" "all" "sum" "product" "maximum" "minimum"
        "scanl" "scanl1" "scanr" "scanr1" "mapAccumL" "mapAccumR"
        "iterate" "repeat" "replicate" "cycle" "unfoldr" "take"
        "drop" "splitAt" "takeWhile" "dropWhile" "dropWhileEnd"
        "span" "break" "stripPrefix" "group" "inits" "tails"
        "isPrefixOf" "isSuffixOf" "isInfixOf" "elem" "notElem"
        "lookup" "find" "filter" "partition" "(!!)" "elemIndex"
        "elemIndices" "findIndex" "findIndices" "zip" "zip3" "zip4"
        "zip5" "zip6" "zip7" "zipWith" "zipWith3" "zipWith4"
        "zipWith5" "zipWith6" "zipWith7" "unzip" "unzip3" "unzip4"
        "unzip5" "unzip6" "unzip7" "lines" "words" "unlines"
        "unwords" "nub" "delete" "(\\)" "union" "intersect"
        "sort" "insert" "nubBy" "deleteBy" "deleteFirstsBy"
        "unionBy" "intersectBy" "groupBy" "sortBy" "insertBy"
        "maximumBy" "minimumBy" "genericLength" "genericTake"
        "genericDrop" "genericSplitAt" "genericIndex" "genericReplicate"
        ;; from Data.Ratio
        "Ratio" "Rational" "(%)" "numerator" "denominator" "approxRational"))

;; If flag is false, the translation of the term for general recursion
;; will not include the measure function and will instead have
;; computation rule
;;
;;   grecNoMeasure :: alpha -> (alpha -> (alpha -> beta) -> beta) -> beta
;;   grecNoMeasure x g = g x (\ y -> grec y g)
;;
;; instead of
;;
;;   grec :: (alpha -> Nat)
;;              -> alpha -> (alpha -> (alpha -> beta) -> beta) -> beta
;;   grec m x g = g x (\ y -> if (m y < m x) then grec m y g else inhab)
;;
;; This is possible because of Haskell's lazy evaluation, and gives
;; rise to a sound realizer, which in general is more efficent since
;; it is not calculating the measure function.  Note however that this
;; semantics is noticably different from Minlog's semantics, since
;; grec is a total function (by design), whereas grecNoMeasure is not
;; (e.g. measure m = id and g x h = h x -- notice that g is not only
;; doing recursive calls on smaller arguments).  However, every
;; instance of grecNoMeasure arising from an extracted proof will
;; terminate, as the proof is only using the induction hypothesis for
;; smaller terms, and the relation R(x, y) <=> m x < m y is
;; wellfounded.
;;
;; To summarise: if flag is set to true, the Haskell semantics is
;; exactly the same as the Minlog semantics.  If the flag is set to
;; false, a more efficient Haskell semantics is achieved, but with a
;; risk of non-termination if used incorrectly, that is trying to do
;; recursive calls on arguments that are not smaller according to the
;; measure.

(define HASKELL-GREC-MEASURE-FLAG #f)

(define (generate-haskell-preamble algebras inhabs? module-name)
  (let* ((pragmas (apply string-append-with-sep ", "
		    (append
		     (if (check-exists
			  (lambda (alg) (not (null? (alg-name-to-tvars alg))))
			  (set-minus  algebras BUILTIN-HASKELL-ALGEBRAS))
			 (list "DeriveFunctor")
			 '())
		     (if inhabs? (list "ScopedTypeVariables") '())))))
    (apply string-append-with-sep "\n\n"
     (append
      (if (string=? pragmas "") '() (list (string-append "{-# LANGUAGE "
							 pragmas
       						 " #-}")))
      (list (string-append "module " module-name " where"))
      (if (member "rat" algebras) (list "import Data.Ratio") '())
      (if (member "list" algebras) (list "import Data.List") '())
      (if inhabs? (list "class Inhabited a where\n  inhab :: a") '())))))

;; term-to-extraction-info returns a list (pconst-names fixed-rules
;; algebras inhab) of program constants, fixed rules (recursion,
;; corecursion, guarded general recursion, destructors), algebra names
;; and types where the canonical inhabitant has been used in t or in a
;; program constant mentioned in t.

(define (term-to-extraction-info t)

  ;; term-to-consts-info returns a list of quadruples (k c t s) where
  ;; c is a constant of kind k (pconst or fixed-rule) which occurs in
  ;; term, and c is associated with the algebra t, simultaneously with
  ;; the algebras in the list s.
  (define (term-to-consts-info term)
    (cond
     ((term-in-var-form? term)
      '())
     ((term-in-const-form? (term-in-app-form-to-final-op term))
      (let* ((op (term-in-app-form-to-final-op term))
	     (args (term-in-app-form-to-args term))
	     (const (term-in-const-form-to-const op))
	     (name (const-to-name const))
	     (kind (const-to-kind const))
	     (type (const-to-type const))
	     (prevs (apply append (map term-to-consts-info args))))
        (cond
         ((string=? name "Rec")
          (let* ((algs (map arrow-form-to-arg-type
			    (rec-const-to-uninst-arrow-types const))))
	    (append (map (lambda (x) (list kind name x algs)) algs) prevs)))
         ((string=? name "CoRec")
          (let* ((uninst-alg-or-arrow-types 
                  (corec-const-to-uninst-alg-or-arrow-types const))
		 (algs 
                  (map arrow-form-to-final-val-type uninst-alg-or-arrow-types))
		 (rel-algs
		  (map arrow-form-to-final-val-type 
		       (list-transform-positive uninst-alg-or-arrow-types
			 arrow-form?)))
		 (rel-alg-names (map alg-form-to-name rel-algs))
		 (alg-name (car rel-alg-names))
		 (simalg-names (alg-name-to-simalg-names alg-name))
		 (ordered-rel-algs
		  (map (lambda (name)
			 (list-ref rel-algs
				   (- (length rel-alg-names)
				      (length (member name rel-alg-names)))))
		       (list-transform-positive simalg-names
			 (lambda (name) (member name rel-alg-names))))))
	    (append (map (lambda (x) (list kind name x ordered-rel-algs)) algs)
		    prevs)))
	 ((string=? name "Destr")
          (let* ((alg (destr-const-to-alg const)))
            (cons (list kind name alg '()) prevs)))
         ((string=? name "GRecGuard")
          (let* ((algs (arrow-form-to-arg-types
                        (arrow-form-to-arg-type type))))
            (cons (list kind name algs '()) prevs)))
         (else
          (cons (list kind name type '()) prevs)))))
     ((term-in-app-form? term)
      (let* ((op (term-in-app-form-to-op term))
	     (arg (term-in-app-form-to-arg term)))
	(append (term-to-consts-info op) (term-to-consts-info arg))))
     ((term-in-abst-form? term)
      (term-to-consts-info (term-in-abst-form-to-kernel term)))
     ((term-in-pair-form? term)
      (let* ((left (term-in-pair-form-to-left term))
	     (right (term-in-pair-form-to-right term)))
	(append (term-to-consts-info left) (term-to-consts-info right))))
     ((term-in-lcomp-form? term)
      (term-to-consts-info (term-in-lcomp-form-to-kernel term)))
     ((term-in-rcomp-form? term)
      (term-to-consts-info (term-in-rcomp-form-to-kernel term)))
     ((term-in-if-form? term)
      (let* ((test (term-in-if-form-to-test term))
	     (alts (term-in-if-form-to-alts term))
	     (prevs (map term-to-consts-info alts)))
	(apply append (term-to-consts-info test) prevs)))
     (else (myerror "term-to-consts-info" "unknown tag" (tag term)))))

  ;; pconst-name-to-consts-info applies term-to-consts-info to the
  ;; right hand side of all computation rules for the program constant
  ;; name
  (define (pconst-name-to-consts-info name)
    (let ((rules (pconst-name-to-comprules name)))
      (remove-duplicates
       (apply append (map (compose term-to-consts-info rule-to-rhs) rules)))))

  (define (info-to-pconst-names info)
    (map cadr (list-transform-positive info
		(lambda (x) (equal? (car x) 'pconst)))))

  ;; The main body of term-to-extraction-info
  (let* ((type (term-to-type t))
	 (initial-info (remove-duplicates (term-to-consts-info t)))
         (info-from-pconsts
	  (do ((done '())
	       (todo (info-to-pconst-names initial-info))
	       (current #f)
	       (current-result #f)
	       (result initial-info))
	      ((null? todo) (remove-duplicates result))
	    (set! current (car todo))
	    (set! current-result (if (or
                                      (member current done)
                                      (member current BUILTIN-HASKELL-PCONSTS))
				     '()
				     (pconst-name-to-consts-info current)))
	    (set! result (append current-result result))
	    (set! done (cons current done))
	    (set! todo (append (info-to-pconst-names current-result)
			       (cdr todo)))))
	 (pconst-names (remove-duplicates
			(map cadr
			     (list-transform-positive info-from-pconsts
			       (lambda (x) (equal? (car x) 'pconst))))))
	 (fixed-rules (remove-duplicates
                       (map (lambda (x) (if (member (cadr x)
                                                    '("Rec" "CoRec" "Destr"))
                                            (list (cadr x)
                                                  (alg-form-to-name (caddr x))
                                                  (map alg-form-to-name
                                                       (cadddr x)))
                                            (cdr x)))
                            (list-transform-positive info-from-pconsts
			      (lambda (x) (and
                                           (equal? (car x) 'fixed-rules)
                                           (not (string=? (cadr x) "="))))))))
	 (algebras (remove-duplicates
		    (apply append
			   (map type-to-alg-with-simalg-names
				(cons type
                                      (map
                                       (lambda (x)
                                         (if (and
                                              (equal? (car x) 'fixed-rules)
                                              (string=? (cadr x) "GRecGuard"))
                                             (apply mk-arrow (caddr x))
                                             (caddr x)))
                                       info-from-pconsts))))))
         (inhab (union
                 (if HASKELL-GREC-MEASURE-FLAG
                     (map (compose arrow-form-to-final-val-type caddr)
                          (list-transform-positive info-from-pconsts
                            (lambda (x) (string=? (cadr x) "GRecGuard"))))
                     '())
		  (map caddr
		       (list-transform-positive info-from-pconsts
			   (lambda (x)
				 (string=? (cadr x) "Inhab")))))))
    (list pconst-names fixed-rules algebras inhab)))

;; algebras-to-haskell-data returns a string containing Haskell data
;; type declarations for the algebra names given
(define (algebras-to-haskell-data algebras module-name)

  (define (foreach-constructor constr)
    (let* ((args (arrow-form-to-arg-types (typed-constr-name-to-type constr)))
           (arg-names
            (apply string-append-with-sep " "
                   (map (lambda (x) (type-to-haskell-type x module-name))
                        args))))
      (string-append
       (string-capitalize-first (typed-constr-name-to-name constr))
       " " arg-names)))

  (define (foreach-alg alg)
    (let* ((tvars (alg-name-to-tvars alg))
           (tvar-names (apply string-append-with-sep " "
                              (map tvar-to-string tvars)))
           (constr (alg-name-to-typed-constr-names alg))
           (alg-form (arrow-form-to-final-val-type
                      (typed-constr-name-to-type (car constr))))
           (constr-list (apply string-append-with-sep " | "
                               (map foreach-constructor constr)))
           ;; In order to consider e.g. "list alpha" finitary:
           (tsubst (make-substitution
		    tvars (repeat (py "unit") (length tvars))))
	   (deriving-clause
            (apply string-append-with-sep ", "
                   (append (if (finalg? (type-substitute alg-form tsubst))
                               (list "Show" "Read" "Eq" "Ord") '())
                           (if (null? tvars) '() (list "Functor")))))
           (name (if (null? tvars)
                     (string-capitalize-first alg)
                     (string-append (string-capitalize-first alg) " "
                                    tvar-names))))
      (cond ((string=? name "Nat") "type Nat = Integer")
            ((string=? name "Pos") "type Pos = Integer")
            (else (string-append
                   "data " name " = " constr-list
                   (if (string=? deriving-clause "")
                       ""
                       (string-append
			"\n  deriving (" deriving-clause ")")))))))

  ;; Body of algebras-to-haskell-data
  (let* ((used-algebras (set-minus algebras BUILTIN-HASKELL-ALGEBRAS))
         (haskell-data (map foreach-alg used-algebras)))
    (apply string-append-with-sep "\n\n" haskell-data)))

;; HASKELL-VARIABLES contains a translation from Minlog variable names
;; to shorter names to be used in the Haskell translation.  Meant to be
;; a cure for variable names like
;;   lpar_nattonat_rpartolpar_nattonat_atnat_rpartonat_hat
;;
;; HASKELL-DEFAULT-VARIABLES contains the names to be used for types
;; without a custom default variable name, where the type name is too
;; long to use.  The invariant that this does not clash with any
;; user-defined names, nor algebra names, needs to hold.  Further, the
;; function find-non-clashing-var-name finds such a name

(define HASKELL-VARIABLES '())
(define HASKELL-DEFAULT-VARIABLES '())

(define (reset-haskell-default-var)
  (begin
    (set! HASKELL-VARIABLES '())
    (set! HASKELL-DEFAULT-VARIABLES '())))

(define (find-non-clashing-var-name type)
  ;; helper functions for next-string, which given a string
  ;; gives the next string according to the ordering
  ;; a < b < ... < z < aa < ab < ...,
  (define alphabet " abcdefghijklmnopqrstuvwxyz") ;make a = 1
  (define base (string-length alphabet))
  (define (char-value char)
    (string-contains alphabet (list->string (cons char '())) 0))
  (define (char-list->sum char-list) ;char-list non-empty
    (if (null? (cdr char-list)) (char-value (car char-list))
        (+ (char-value (car char-list))
           (* base (char-list->sum (cdr char-list))))))
  (define (string->sum s)
    (char-list->sum (reverse (string->list s))))
  (define (sum->string n)
    (if (< n base)
        (list->string (cons (string-ref alphabet n) '()))
        (string-append (sum->string (remainder n base))
                       (sum->string (quotient n base)))))
  (define (next-string s) (string-reverse
                           (string-replace-substring ;carry.  make z + 1 = aa
                            (sum->string (+ (string->sum s) 1))
                            " "
                            "a")))
  (define (non-clashing? var)
    (not (or
          (member
	   var
	   '("all" "ex" "allnc" "excl" "exca" "excu"
	     "CoRec" "coRec" "Destr" "lambda" "left" "right" "cterm" "if"
	     "Pvar" "MPC" "PROOF" "CLASSIC" "INTUITIONISTIC" "END" "LOAD"
	     "INCLUDE" "SCHEME" "TYPE" "PRED" "ALGEBRA" "FUNCTION" "PARTIAL"
	     "REWRITE" "SYNTAX" "PAIROP" "IMPOP" "OROP" "ANDOP" "RELOP"
	     "ADDOP" "MULOP" "PREFIXOP" "POSTFIXOP" "CONST"))
          (if (member var RESERVED-NAMES) #t #f)
          (if (assoc var TYPE-VARIABLES) #t #f)
          (if (assoc var TYPE-CONSTANTS) #t #f)
          (if (assoc var ALGEBRAS) #t #f)
          (if (assoc var CONSTRUCTORS) #t #f)
          (if (assoc var VARIABLES) #t #f)
          (list-search-positive HASKELL-DEFAULT-VARIABLES
            (lambda (x) (string=? (cadr x) var)))
          (if (assoc var PROGRAM-CONSTANTS) #t #f)
          (if (assoc var PREDCONST-NAMES) #t #f)
          (if (assoc var IDS) #t #f)
          (if (assoc var PREDICATE-VARIABLES) #t #f)
          (if (assoc var THEOREMS) #t #f)
          (if (assoc var GLOBAL-ASSUMPTIONS) #t #f))))

  ;; body of find-non-clashing-var-name
  (cond ;try some nicer names first
   ((and (arrow-form? type) (non-clashing? "f")) "f")
   ((and (arrow-form? type) (non-clashing? "g")) "g")
   ((and (arrow-form? type) (non-clashing? "h")) "h")
   ((and (alg-form? type) (non-clashing? "x")) "x")
   ((and (alg-form? type) (non-clashing? "y")) "y")
   ((and (alg-form? type) (non-clashing? "z")) "z")
   ((and (alg-form? type) (non-clashing? "w")) "w")
   ((and (star-form? type) (non-clashing? "p")) "p")
   ((and (star-form? type) (non-clashing? "q")) "q")
   (else (do ((var "a" (next-string var)))
             ((non-clashing? var) var)))))

(define (haskellify-string string)
     (string-replace-substring
      (string-replace-substring
       (string-replace-substring
        (string-replace-substring
         (string-replace-substring
          (string-replace-substring string ")" "_rpar")
          "(" "lpar_") "=>" "to") " " "_") "^" "_hat") "@" "_at"))

(define (haskellify-var var)
  (let* ((var-name (var-to-string var))
         (type (var-to-type var))
         (var-prefix (list->string (remove-final-^
                                    (remove-final-numeric-chars
                                     (string->list var-name)))))
         (already-done (assoc var HASKELL-VARIABLES))
         (friendlier-var
          (cond
	   ;; ((member var-prefix VARIABLE-NAMES) var-name) ;user-chosen var
	   (already-done (cadr already-done)) ;must be consistent
	   ((and
	     (< (string-length var-name) 5) ;short names are okay
	     (or
	      (not (string-contains var-name "(" 0))   ;(unless they get
	      (not (string-contains var-name ")" 0)))) ;expanded to lpar)
	    var-name)
	   (else
	    (let* (;; (chosen-var-name (assoc type HASKELL-DEFAULT-VARIABLES))
		   (chosen-var-name
		    (if (member var-prefix VARIABLE-NAMES)
			(list type var-prefix) ;user chosen var-prefix
			(assoc type HASKELL-DEFAULT-VARIABLES))) ;default prefix
		   (relevant-indices
		    (map caddr
			 (list-transform-positive HASKELL-VARIABLES
			   (lambda (x) (equal? (var-to-type (car x)) type)))))
		   (index (if (null? relevant-indices) -1
			      (+ 1 (apply max relevant-indices))))
		   (index-string (if (= index -1) ""
				     (number->string index)))
		   (var-stem (if (not chosen-var-name)
				 (find-non-clashing-var-name type)
				 (cadr chosen-var-name)))
		   (new-var (string-append var-stem
					   index-string)))
	      (begin
		(if (not chosen-var-name)
		    (set! HASKELL-DEFAULT-VARIABLES
			  (cons (list type var-stem)
				HASKELL-DEFAULT-VARIABLES)))
		(set! HASKELL-VARIABLES (cons (list var new-var index)
					      HASKELL-VARIABLES))
		new-var))))))
    (string-downcase-first (haskellify-string friendlier-var))))

;; Problem for the scheme translation: parentheses in var names are
;; displayed with a semicolon.  Example: \x28;nat=>nat=>nat@@nat\x29;.
;; This confuses the parser who takes the semicolon as a comment
;; symbol.  Cure:

(define (rename-parentheses-and-spaces string)
  (string-replace-substring
   (string-replace-substring
    (string-replace-substring string "(" "lpar_") ")" "_rpar") " " "__"))

;; lang can be either 'haskell or 'scheme

(define (term-to-external-expr term lang module-name . opt-name-arity-alist)
  (let* ((names (map car opt-name-arity-alist))
	 (arities (map cadr opt-name-arity-alist)))
    (cond
     ((term-in-var-form? term)
      (case lang
	((scheme) (string->symbol
		   (rename-parentheses-and-spaces
		    (term-in-var-form-to-string term))))
	((haskell) (haskellify-var (term-in-var-form-to-var term)))))
     ((is-numeric-term-wrt-pos? term)
      (let* ((res (numeric-term-wrt-pos-to-number term)))
	(case lang
	  ((scheme) res)
	  ((haskell) (number->string res)))))
     ((is-numeric-term-wrt-nat? term)
      (let* ((res (numeric-term-wrt-nat-to-number term)))
	(case lang
	  ((scheme) res)
	  ((haskell) (number->string res)))))
     ((is-int-numeric-term? term)
      (let* ((res (int-numeric-term-to-number term)))
	(case lang
	  ((scheme) res)
	  ((haskell) (number->string res)))))
     ((is-rat-numeric-term? term)
      (let* ((res (rat-numeric-term-to-number term)))
	(case lang
	  ((scheme) res)
	  ((haskell) (string-append "(" (number->string res) ")")))))
     ((term-in-const-form? (term-in-app-form-to-final-op term))
      (let* ((op (term-in-app-form-to-final-op term))
	     (args (term-in-app-form-to-args term))
	     (const (term-in-const-form-to-const op))
	     (name (const-to-name const)) ;PairConstr
	     (l (length args))
	     (prevs (map (lambda (term)
			   (apply term-to-external-expr term lang module-name
				  opt-name-arity-alist))
			 args))
	     (info (assoc name opt-name-arity-alist))
	     (arity (if info (cadr info))))
	(cond
	 ((and info (<= arity l)) ;opt-name-arity-alist overrides everything
	  (non-null-list-to-app-expr
	   lang
	   (cons (if (zero? arity) (string->symbol name)
		     (cons (string->symbol name) (list-head prevs arity)))
		 (list-tail prevs arity))))
	 ((string=? name "=") ;different treatment for diff. algs in scheme
	  (case lang
	    ((scheme)
	     (let* ((finalg (arrow-form-to-arg-type (const-to-type const)))
		    (finalg-name (alg-form-to-name finalg)))
	       (if (= l 2)
		   (if (member finalg-name '("nat" "pos" "int" "rat"))
		       (cons '= prevs)
		       (cons 'equal? prevs))
		   (let ((symbol
			  (string->symbol (string-append finalg-name "="))))
		     (non-null-list-to-app-expr lang (cons symbol prevs))))))
	    ((haskell) (if (= l 2)
			   (string-append "(" (car prevs) " == " (cadr prevs)
                                          ")")
                           (non-null-list-to-app-expr
			    lang (cons "(==)" prevs))))))
	 ((member name (list "RatPlus" "IntPlus" "PosPlus" "NatPlus"
                             "RatMinus" "IntMinus" "PosMinus" "NatMinus"
			     "RatTimes" "IntTimes" "PosTimes" "NatTimes"
			     "RatDiv"
			     "RatExp" "IntExp" "PosExp" "NatExp"
			     "RatLe" "IntLe" "PosLe" "NatLe"
			     "RatLt" "IntLt" "PosLt" "NatLt"
			     "RatMax" "IntMax" "PosMax" "NatMax"
			     "RatMin" "IntMin" "PosMin" "NatMin"
			     "Quot" "Rem"
                             "AndConst" "OrConst")) ;binary functions
	  (let* ((op-name-both
		  (cond
		   ((member name (list "RatPlus" "IntPlus" "PosPlus" "NatPlus"))
		    '(+ . "+"))
		   ((member name
			    (list  "RatMinus" "IntMinus" "PosMinus" "NatMinus"))
		    '(- . "-"))
		   ((member name
			    (list "RatTimes" "IntTimes" "PosTimes" "NatTimes"))
		    '(* . "*"))
		   ((member name (list "IntExp" "PosExp" "NatExp"))
		    '(expt . "^"))
		   ((string=? name "RatExp")
		    '(expt . "^^"))
		   ((string=? name "RatDiv")
		    '(/ . "/"))
		   ((member name (list "RatLe" "IntLe" "PosLe" "NatLe"))
		    '(<= . "<="))
		   ((member name (list "RatLt" "IntLt" "PosLt" "NatLt"))
		    '(< . "<"))
		   ((member name (list "RatMax" "IntMax" "PosMax" "NatMax"))
		    '(max . "`max`"))
		   ((member name (list "RatMin" "IntMin" "PosMin" "NatMin"))
		    '(min . "`min`"))
		   ((string=? name "Quot")
		    '(quotient-safe . "`quot`"))
		   ((string=? name "Rem")
		    '(modulo-safe . "`rem`"))
                   ((string=? name "AndConst")
		    '(and . "&&"))
                   ((string=? name "OrConst")
		    '(or . "||"))
		   ))
		 (op-name (case lang
			    ((scheme) (car op-name-both))
			    ((haskell) (cdr op-name-both)))))
	    (if (= l 2)
		(case lang
		  ((scheme) (cons op-name prevs))
		  ((haskell) (string-append "(" (car prevs) " " op-name " "
					    (cadr prevs) ")")))
		(case lang
		  ((scheme)
		   (non-null-list-to-app-expr
		    lang (cons (string->symbol name) prevs)))
		  ((haskell)
		   (let* ((prefix-op (cond ((string=? op-name "`max`") "max")
					   ((string=? op-name "`min`") "min")
					   ((string=? op-name "`quot`") "quot")
					   ((string=? op-name "`rem`") "rem")
					   (else
					    (string-append "(" op-name ")")))))
		     (non-null-list-to-app-expr lang
						(cons prefix-op prevs))))))))
	 ((member name (list "S" "Succ" "IntS" "PosS"))
	  (case lang
	    ((scheme)
	     (if (= l 1) (list '+ (car prevs) 1) (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(" (car prevs) " + 1)")
		 "(+1)"))))
	 ((string=? name "IntPred")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list '- (car prevs) 1) (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(" (car prevs) " - 1)")
		 "pred"))))
	 ((string=? name "SZero")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list '* (car prevs) 2) (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(" (car prevs) " * 2)")
		 "(*2)"))))
	 ((string=? name "SOne")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list '+ (list '* (car prevs) 2) 1)
		 (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(" (car prevs) " * 2 + 1)")
		 "((+1) . (*2))"))))
	 ((string=? name "cId")
	  (cond ((and (term-in-abst-form? (car args)) (= l 2))
		 (let* ((var (term-in-abst-form-to-var (car args)))
			(kernel (term-in-abst-form-to-kernel (car args)))
			(kernel-expr
			 (apply term-to-external-expr kernel lang module-name
				opt-name-arity-alist)))
		   (case lang
		     ((scheme)
		      (list 'let
			    (list (list (string->symbol
					 (rename-parentheses-and-spaces
					  (var-to-string var)))
					(cadr prevs)))
			    kernel-expr))
		     ((haskell)
		      (let* ((var-name (var-to-string var))
			     (haskell-friendly-var (haskellify-var var))
			     (haskell-friendly-kernel
			      (string-replace-substring
			       kernel-expr var-name haskell-friendly-var))
			     (haskell-friendly-prevs
			      (string-replace-substring
			       (cadr prevs) var-name haskell-friendly-var)))
			(string-append "\n (let " haskell-friendly-var
				       " = " haskell-friendly-prevs
				       " in " haskell-friendly-kernel ")"))))))
		((= l 1) (car prevs))
		(else (case lang
			((scheme) (string->symbol name))
			((haskell) name)))))
	 ((string=? name "IntNeg")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list '- (car prevs))
		 (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(-" (car prevs) ")")
		 "negate"))))
	 ((string=? name "NegConst")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list 'not (car prevs))
		 (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(not " (car prevs) ")")
		 "not"))))
	 ((string=? name "ImpConst")
	  (case lang
	    ((scheme)
	     (if (= l 2) (list 'or (list 'not (car prevs)) (cadr prevs))
		 (string->symbol name)))
	    ((haskell)
	     (if (= l 2)
		 (string-append "((not " (car prevs) ") || " (cadr prevs) ")")
		 "(<=)")))) ;abusing that False < True
	 ((or (string=? name "IntPos") (string=? name "PosToNat"))
	  (if (= l 1) (car prevs)
	      (case lang
		((scheme) (string->symbol name))
		((haskell) "id"))))
         ;; "Zero" "IntZero" "One"
         ;; are taken care of by the is-numeric-term-wrt-... check.
         ;; Note that this is not the case for constructors of arity > 0,
         ;; as for instance "Succ x" is not a numeric term (x a variable)
	 ((string=? name "RatConstr") ;ensure (elsewhere) only for building
	  (case lang                  ;values.  Can't be used for pat. matching
	    ((scheme) (if (= l 1) (cons 'cons prevs)))
	    ((haskell)
	     (if (= l 2)
		 (string-append "(" (car prevs) " % " (cadr prevs) ")")
		 (non-null-list-to-app-expr lang (cons "(%)" prevs))))))
	 ((string=? name "False")
	  (case lang
	    ((scheme) #f)
	    ((haskell) "False")))
	 ((string=? name "True")
	  (case lang
	    ((scheme) #t)
	    ((haskell) "True")))
	 ((string=? name "Dummy")
	  (case lang
	    ((scheme) 'Dummy)
	    ((haskell) "()")))
	 ((string=? name "PairConstr")
	  (case lang
	    ((scheme) (if (= l 2) (cons 'cons prevs)))
	    ((haskell)
	     (if (= l 2)
		 (string-append "(" (car prevs) " , " (cadr prevs) ")")
		 (non-null-list-to-app-expr lang (cons "(,)" prevs))))))
	 ((string=? name "PairOne")
	  (case lang
	    ((scheme) (if (= l 1) (cons 'car prevs)))
	    ((haskell) (non-null-list-to-app-expr lang (cons "fst" prevs)))))
	 ((string=? name "PairTwo")
	  (case lang
	    ((scheme) (if (= l 1) (cons 'cdr prevs)))
	    ((haskell) (non-null-list-to-app-expr lang (cons "snd" prevs)))))
	 ((string=? name "InL")
	  (case lang
	    ((scheme) (if (= l 1) (cons 'InL prevs)))
	    ((haskell) (non-null-list-to-app-expr lang (cons "Left" prevs)))))
	 ((string=? name "InR")
	  (case lang
	    ((scheme) (if (= l 1) (cons 'InR prevs)))
	    ((haskell) (non-null-list-to-app-expr lang (cons "Right" prevs)))))
	 ((member name (list "DummyL" "DummyR"))
	  (case lang
	    ((scheme) (string->symbol name))
	    ((haskell) "Nothing")))
	 ((member name (list "InlYsumu" "InrUysum"))
	  (case lang
	    ((scheme) (if (= l 1) (cons (string->symbol name) prevs)))
	    ((haskell) (non-null-list-to-app-expr lang (cons "Just" prevs)))))
	 ((string=? name "Nil")
	  (case lang
	    ((scheme)  (list 'quote '()))
	    ((haskell) "[]")))
	 ((string=? name "Cons")
	  (case lang
	    ((scheme)
	     (if (= l 2)
		 (cons 'cons prevs)
		 (non-null-list-to-app-expr lang (cons 'cons-curried prevs))))
	    ((haskell)
	     (if (= l 2)
		 (string-append "(" (car prevs) " : " (cadr prevs) ")")
		 (apply string-append-with-sep " " (cons "(:)" prevs))))))
	 ((member name (list "ListAppend" "ListAppd"))
	  (case lang
	    ((scheme)
	     (cons 'append prevs))
	    ((haskell)
	     (if (= l 2)
		 (string-append "(" (car prevs) " ++ " (cadr prevs) ")")
		 (apply string-append-with-sep " " (cons "(++)" prevs))))))
	 ((string=? name "ListLength")
	  (case lang
	    ((scheme) (if (= l 1) (cons 'length prevs)))
	    ((haskell)
	     (if (= l 1) (string-append "(genericLength " (car prevs) ")")
		 (non-null-list-to-app-expr lang
					    (cons "genericLength" prevs))))))
	 ((string=? name "ListProj")
	  (case lang
	    ((scheme)
	     (list 'list-ref (cadr prevs) (car prevs)))
	    ((haskell)
	     (if (= l 2)
		 (string-append "(" (cadr prevs) " !! " (car prevs) ")")
		 (apply string-append-with-sep
			" " "genericIndex" prevs)))))
	 ((string=? name "ListMap")
	  (case lang
	    ((scheme)
	     (cons 'map prevs))
	    ((haskell)
	     (if (= l 2)
		 (string-append "(map " (car prevs) (cadr prevs) ")")
		 ;; (string-append "(map" (car prevs) (cadr prevs) ")")
		 ;; Changes 2018-10-01
		 (apply string-append-with-sep " " (cons "map" prevs))))))
	 ((string=? name "Inhab")
	  (let* ((inhab-name
		  (case lang
		    ((scheme) 'inhab)
		    ((haskell) (string-append "(inhab::"
					      (type-to-haskell-type
					       (const-to-type const)
                                               module-name)
					      ")")))))
	    (non-null-list-to-app-expr lang (cons inhab-name prevs))))
	 ;; special pconsts used by the translation
	 ((string=? name "TranslationDenominator")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list 'car (cadr prevs) 1) (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(denominator " (car prevs) ")")
		 "denominator"))))
	 ((string=? name "TranslationNumerator")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list 'car (car prevs) 1) (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(numerator " (car prevs) ")")
		 "numerator"))))
	 ((string=? name "TranslationPosHalfEven")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list '/ (car prevs) 2) (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(" (car prevs) " `quot` 2)")))))
	 ((string=? name "TranslationPosNegForInt")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list '- (car prevs)) (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(-" (car prevs) ")")))))
	 ((string=? name "TranslationPosAsInt")
	  (case lang
	    ((scheme)
	     (if (= l 1) (car prevs) (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (car prevs) ))))
	 ((string=? name "TranslationNatMinusPosDiff")
	  (case lang
	    ((scheme)
	     (if (= l 2) (list '- (car prevs) (cadr prevs))))
	    ((haskell)
	     (if (= l 2) (string-append "(" (car prevs) " - "
					(cadr prevs) ")")))))
	 ((string=? name "TranslationPosPredNonOne")
	  (case lang
	    ((scheme)
	     (if (= l 1) (list '- (car prevs) 1) (string->symbol name)))
	    ((haskell)
	     (if (= l 1) (string-append "(" (car prevs) " - 1)")))))
	 ;; ordinary constants
	 ((string=? name "Rec")
	  (let* ((uninst-arrow-types (rec-const-to-uninst-arrow-types const))
		 (alg (arrow-form-to-arg-type (car uninst-arrow-types)))
		 (type-name (alg-form-to-name alg))
                 (all-simalg-names (alg-name-to-simalg-names type-name))
                 (simp? (< (length uninst-arrow-types)
                           (length all-simalg-names)))
                 (relalg-names (apply string-append "_"
                                      (intersection ;to normalise order of algs
                                       (map (compose haskellify-string
                                                     type-to-string
                                                     arrow-form-to-arg-type)
                                            uninst-arrow-types)
                                       all-simalg-names)))
		 (rec-name
                  (string-append
		   type-name "Rec"
		   (if simp?
		       (string-append "Simp"
				      (if (> (length all-simalg-names) 2)
					  relalg-names ""))
		       "")))
		 (rec-symbol
		  (case lang
		    ((scheme) (if (= 1 (length uninst-arrow-types))
				  (string->symbol rec-name)
				  (myerror "term-to-external-expr"
					   "unknown recursion" term)))
		    ((haskell) (string-downcase-first rec-name)))))
	    (non-null-list-to-app-expr lang (cons rec-symbol prevs))))
	 ((string=? name "Map")
	  (case lang
	    ((scheme)
	     (myerror "term-to-external-expr" "unsupported feature" term))
	    ((haskell) (let* ((f (cadr prevs))
			      (x (car prevs))
			      (rest (if (> l 2)
					(cddr prevs)
					'())))
			 (non-null-list-to-app-expr
			  lang
			  (append (list "fmap" f x) rest))))))
	 ((string=? name "Destr")
	  (let* ((alg (destr-const-to-alg const))
		 (type-name (alg-form-to-name alg))
		 (destr-name (string-append type-name "Destr"))
		 (destr-symbol
		  (case lang
		    ((scheme) (string->symbol destr-name))
		    ((haskell) (string-downcase-first destr-name)))))
	    (non-null-list-to-app-expr lang (cons destr-symbol prevs))))
	 ((string=? name "CoRec")
	  (let* ((uninst-alg-or-arrow-types 
		  (corec-const-to-uninst-alg-or-arrow-types const))
                 (uninst-arrow-types 
		  (list-transform-positive uninst-alg-or-arrow-types
		    arrow-form?))
		 ;; (filter arrow-form? uninst-alg-or-arrow-types))
		 (alg (arrow-form-to-final-val-type (const-to-type const)))
		 (type-name (alg-form-to-name alg))
                 (all-simalg-names (alg-name-to-simalg-names type-name))
                 (simp? (< (length uninst-arrow-types)
			   (length all-simalg-names)))
                 (relalg-names (apply string-append "_"
                                      (map (compose haskellify-string
                                                    type-to-string
                                                    arrow-form-to-arg-type)
                                           uninst-arrow-types)))
                 (corec-name
                  (string-append
		   type-name "CoRec"
		   (if simp?
		       (string-append "Simp"
				      (if (> (length all-simalg-names) 2)
					  relalg-names ""))
		       "")))
		 (corec-symbol
		  (case lang
		    ((scheme) (if (= 1 (length uninst-arrow-types))
				  (string->symbol corec-name)
				  (myerror "term-to-external-expr"
					   "unknown corecursion"
					   term)))
		    ((haskell) (string-downcase-first corec-name)))))
	    (non-null-list-to-app-expr lang (cons corec-symbol prevs))))
	 ((string=? name "GRecGuard")
	  (let* ((type (const-to-type const))
	  	 (measure-type (arrow-form-to-arg-type type))
	  	 (arg-types (arrow-form-to-arg-types measure-type))
                 (prevs-fix ;remove measure and bool if needed
                  (if (or (eq? lang 'scheme) HASKELL-GREC-MEASURE-FLAG)
		      prevs
                      ;; measure is the first arg, find which argument is
                      ;; the boolean: grecguard has type
                      ;; (rhos=>nat)=>rhos=>(rhos=>(rhos=>tau)=>tau)=>boole=>tau
                      ;; and bool-arg below is the number of args in rhos + tau
                      ;; the position after removing the measure arg should
                      ;; hence be bool-arg - 1 + 1 = bool-arg
                      (let* ((bool-arg
                              (length
                               (grecguard-const-to-uninst-type-info const))))
			(if (<= (length prevs) bool-arg)
			    prevs
			    (remove-nth (cdr prevs) bool-arg)))))
	  	 (grec-name (apply string-append
	  			   (append (map (compose haskellify-string
                                                         type-to-string)
                                                arg-types)
	  				   (list "GrecGuard"))))
	  	 (grecguard-symbol
		  (case lang
		    ((scheme)  (string->symbol grec-name))
		    ((haskell) (string-downcase-first grec-name)))))
	    (non-null-list-to-app-expr lang (cons grecguard-symbol prevs-fix))))
	 ((term-in-cons-form? term)
	  (let* ((left (term-in-cons-form-to-left term))
		 (right (term-in-cons-form-to-right term))
		 (left-expr (apply term-to-external-expr left lang
                                   module-name opt-name-arity-alist))
		 (right-expr (apply term-to-external-expr right lang
                                    module-name opt-name-arity-alist)))
	    (case lang
	      ((scheme) (list 'cons left-expr right-expr))
	      ((haskell) (string-append "(" left-expr ", " right-expr ")")))))
         (else
	  (let* ((const-name
                  (case lang
                    ((scheme) (string->symbol name))
                    ((haskell)
                     (let* ((actual-name
                             (cond
                              ((pconst-name? name)
                               (string-downcase-first name))
                              ((constr-name? name)
                               (string-capitalize-first name))
                              (else name)))
                            (prefix
                             (if (member actual-name RESERVED-HASKELL-NAMES)
                                 (string-append module-name ".") "")))
                       (string-append prefix actual-name))))))
	    (non-null-list-to-app-expr lang (cons const-name prevs)))))))
     ((term-in-app-form? term)
      (let* ((op (term-in-app-form-to-op term))
	     (arg (term-in-app-form-to-arg term))
	     (op-expr (apply term-to-external-expr op lang module-name
                             opt-name-arity-alist))
	     (arg-expr (apply term-to-external-expr arg lang module-name
                              opt-name-arity-alist)))
	(case lang
	  ((scheme) (list op-expr arg-expr))
	  ((haskell) (string-append "(" op-expr " "arg-expr ")")))))
     ((term-in-abst-form? term)
      (let* ((var (term-in-abst-form-to-var term))
	     (var-string (var-to-string var))
	     (kernel-expr (apply term-to-external-expr
				 (term-in-abst-form-to-kernel term)
				 lang module-name opt-name-arity-alist)))
	(case lang
	  ((scheme)
	   (list 'lambda (list (string->symbol
				(rename-parentheses-and-spaces
				 var-string))) kernel-expr))
	  ((haskell)
	   (let* ((haskell-friendly-var (haskellify-var var))
		  (haskell-friendly-kernel
		   (string-replace-substring kernel-expr
					     var-string haskell-friendly-var)))
	     (string-append "(\\ " haskell-friendly-var " -> "
			    haskell-friendly-kernel ")"))))))
     ((term-in-pair-form? term)
      (let* ((left (term-in-pair-form-to-left term))
	     (right (term-in-pair-form-to-right term))
	     (left-expr (apply term-to-external-expr left lang module-name
			       opt-name-arity-alist))
	     (right-expr (apply term-to-external-expr right lang module-name
				opt-name-arity-alist)))
	(case lang
	  ((scheme) (list 'cons left-expr right-expr))
	  ((haskell) (string-append "(" left-expr ", " right-expr ")")))))
     ((term-in-lcomp-form? term)
      (let ((expr (apply term-to-external-expr
			 (term-in-lcomp-form-to-kernel term)
			 lang module-name opt-name-arity-alist)))
	(case lang
	  ((scheme) (list 'car expr))
	  ((haskell) (string-append "(fst " expr ")")))))
     ((term-in-rcomp-form? term)
      (let ((expr (apply term-to-external-expr
			 (term-in-rcomp-form-to-kernel term)
			 lang module-name opt-name-arity-alist)))
	(case lang
	  ((scheme) (list 'cdr expr))
	  ((haskell) (string-append "(snd " expr ")")))))
     ((term-in-if-form? term)
      (let* ((test (term-in-if-form-to-test term))
	     (alts (term-in-if-form-to-alts term))
	     (type (term-to-type test))
	     (test-expr (apply term-to-external-expr
			       (term-to-beta-eta-nf test) lang module-name
			       opt-name-arity-alist))
	     (alt-exprs (map (lambda (term)
			       (apply
				term-to-external-expr
				(term-to-beta-eta-nf term) lang module-name
				opt-name-arity-alist))
			     alts)))
	(cond
	 ((and (alg-form? type) (string=? (alg-form-to-name type) "boole"))
	  (case lang
	    ((scheme) (append (list 'if test-expr) alt-exprs))
	    ((haskell) (string-append "(if " test-expr
				      " then " (car alt-exprs)
				      " else " (cadr alt-exprs) ")"))))
	 ((and (alg-form? type) (string=? (alg-form-to-name type) "pos"))
	  (case lang
	    ((scheme)
	     (list 'cond
		   (list (list '= '1 test-expr) (car alt-exprs))
		   (list (list 'even? test-expr)
			 (remove-vacuous-beta-redex
			  (list (cadr alt-exprs)
				(list 'quotient test-expr 2))))
		   (list (list 'odd? test-expr)
			 (remove-vacuous-beta-redex
			  (list (caddr alt-exprs)
				(list 'quotient test-expr 2))))))
	    ((haskell)
	     (string-append
	      "(if (1 == " test-expr ") then " (car alt-exprs) ;wrong!
	      " else if (even " test-expr ") then ("
	      (cadr alt-exprs)
	      "`quot` 2) else if (odd " test-expr ") then ("
	      (caddr alt-exprs) "`quot` 2)"))))
	 ((and (alg-form? type) (string=? (alg-form-to-name type) "rat"))
	  (case lang
	    ((scheme)
	     (myerror "term-to-external-expr" "unknown if (rat)" term))
	    ((haskell)
             (apply term-to-haskell-expr
                    (term-to-beta-eta-nf
                     (mk-term-in-app-form
		      (car alts)
		      (make-term-in-app-form
		       (make-term-in-const-form
			(pconst-name-to-pconst
			 "TranslationNumerator"))
		       test)
		      (make-term-in-app-form
		       (make-term-in-const-form
			(pconst-name-to-pconst
			 "TranslationDenominator"))
		       test)))
                    (list module-name)))))
	 ((and (alg-form? type) (string=? (alg-form-to-name type) "int"))
	  (case lang
	    ((scheme)
	     (list 'cond
		   (list (list 'positive? test-expr)
			 (remove-vacuous-beta-redex
			  (list (car alt-exprs) test-expr)))
		   (list (list 'zero? test-expr)
			 (remove-vacuous-beta-redex
			  (cadr alt-exprs)))
		   (list (list 'negative? test-expr)
			 (remove-vacuous-beta-redex
			  (list (caddr alt-exprs) (list '- test-expr))))))
	    ((haskell)
	     (string-append "(if (" test-expr " > 0) then "
                            (non-null-list-to-app-expr
			     'haskell
			     (list (car alt-exprs) test-expr))
			    " else if (" test-expr " == 0) then ("
			    (cadr alt-exprs)
			    ") else ("
                            (non-null-list-to-app-expr
			     'haskell
			     (list (caddr alt-exprs)
				   (string-append "(-" test-expr "))")))
                            ")"))))
	 ((and (alg-form? type) (string=? (alg-form-to-name type) "nat"))
	  (case lang
	    ((scheme)
	     (list 'cond
		   (list (list 'zero? test-expr)
			 (remove-vacuous-beta-redex
			  (car alt-exprs)))
		   (list (list 'positive? test-expr)
			 (remove-vacuous-beta-redex
			  (list (cadr alt-exprs) (list '- test-expr 1))))))
	    ((haskell)
	     (string-append
	      "(if (" test-expr " == 0) then " (car alt-exprs)
	      " else (" ;test-expr > 0
	      (apply term-to-haskell-expr
		     (term-to-beta-eta-nf
		      (mk-term-in-app-form
                       (cadr alts)
                       (mk-term-in-app-form
                        (make-term-in-const-form
                         (pconst-name-to-pconst
                          "TranslationNatMinusPosDiff"))
                        test
                        (pt "Succ Zero"))))
		     (list module-name))
	      "))"))))
	 ((and (alg-form? type) (string=? (alg-form-to-name type) "list"))
	  (case lang
	    ((scheme)
	     (let* ((car-of-test-expr (if (pair? test-expr)
					  (car test-expr)
					  (list 'car test-expr)))
		    (cdr-of-test-expr (if (pair? test-expr)
					  (cdr test-expr)
					  (list 'cdr test-expr))))
	       (list 'if (list 'null? test-expr) (car alt-exprs)
		     (remove-vacuous-beta-redex
		      (list (remove-vacuous-beta-redex
			     (list (cadr alt-exprs) car-of-test-expr))
			    cdr-of-test-expr)))))
	    ((haskell)
	     (let* ((head-test-expr (if (pair? test-expr)
					(car test-expr)
					(string-append "(head " test-expr ")")))
		    (tail-test-expr (if
				     (pair? test-expr)
				     (cdr test-expr)
				     (string-append "(tail " test-expr ")"))))
	       (string-append "(if (null " test-expr ") then "
			      (car alt-exprs)
			      " else "
			      (non-null-list-to-app-expr
			       'haskell
			       (list (cadr alt-exprs)
				     head-test-expr
				     tail-test-expr))
			      ")")))))
	 ((and (alg-form? type) (string=? (alg-form-to-name type) "ysum")
	       (eq? lang 'scheme))
	  (list 'let (list (list 'testsum (list 'quote test-expr)))
		(list 'if (list 'eq? (list 'quote 'InL) (list 'car 'testsum))
		      (list (car alt-exprs) (list 'cadr 'testsum))
		      (list (cadr alt-exprs) (list 'cadr 'testsum)))))
	 ((and (alg-form? type) (string=? (alg-form-to-name type) "yprod")
	       (eq? lang 'scheme))
	  (if (term-in-var-form? test)
	      (list (list (car alt-exprs) (list 'car test-expr))
		    (list 'cdr test-expr))
	      (list 'let (list (list 'testprod test-expr))
		    (list (list (car alt-exprs) (list 'car 'testprod))
			  (list 'cdr 'testprod)))))
	 ((alg-form? type)
	  (case lang
	    ((scheme) (myerror "term-to-external-expr" "unknown if (alg)" term))
	    ((haskell)
	     (let* ((constr (alg-name-to-typed-constr-names
			     (alg-form-to-name type)))
		    (foreach-constr
		     (lambda (constr alt)
		       (let* ((constr-name
			       (typed-constr-name-to-name constr))
			      (constr-name-expr
			       (apply term-to-haskell-expr
				      (make-term-in-const-form
				       (constr-name-to-constr constr-name))
				      (list module-name)))
			      (patargs-types (list-head
                                              (arrow-form-to-arg-types
                                               (term-to-type alt))
                                              (length
                                               (arrow-form-to-arg-types
						(term-to-type constr)))))
			      (patargs
			       (map (compose make-term-in-var-form
					     type-to-new-var) patargs-types))
			      (lhs (string-remove-outer-parens
                                    (non-null-list-to-app-expr
				     'haskell
				     (cons constr-name-expr
					   (map (lambda (x)
						  (apply term-to-haskell-expr x
							 (list module-name)))
						patargs)))))
			      (rhs-term (term-to-beta-eta-nf
                                         (apply mk-term-in-app-form
						alt patargs)))
			      (rhs (apply term-to-haskell-expr rhs-term
                                          (list module-name))))
			 (string-append lhs " -> " rhs ))))
		    (clauses (map foreach-constr constr alts)))

	       (string-append "(case " test-expr " of\n      { "
			      (apply string-append-with-sep " ;\n " clauses)
			      " })")))))
	 (else (myerror "term-to-external-expr" "unknown if" term)))))
     (else (myerror "term-to-external-expr" "unknown tag" (tag term))))))

(define (term-to-scheme-expr term . opt-name-arity-alist)
  (apply term-to-external-expr term 'scheme "Main" opt-name-arity-alist))

(define (term-to-haskell-expr term . opt-module-name-and-name-arity-alist)
  (if (null? opt-module-name-and-name-arity-alist)
      (term-to-external-expr term 'haskell "Main")
      (apply term-to-external-expr term 'haskell
             (car opt-module-name-and-name-arity-alist)
             (cdr opt-module-name-and-name-arity-alist))))

;; For backwards compatibility, we define
(define term-to-expr term-to-scheme-expr)

(define (type-to-haskell-type type module-name)
  (cond ((tconst-form? type) (string-capitalize-first (tconst-to-name type)))
	((tvar-form? type) (tvar-to-string type))
	((alg-form? type)
	 (let* ((name (alg-form-to-name type))
		(tvars (alg-form-to-types type))
		(tvar-names (apply string-append-with-sep " "
				   (map (lambda (x)
                                          (type-to-haskell-type x module-name))
                                        tvars))))
           (cond
	    ((string=? name "boole") "Bool")
	    ((string=? name "nat") "Nat")
	    ((string=? name "int") "Integer")
	    ((string=? name "pos") "Pos")
	    ((string=? name "rat") "Rational")
	    ;; (no special treatment for real and complex numbers)
	    ((string=? name "list")
	     (string-append "[" tvar-names "]"))
	    ((string=? name "yprod")
	     (string-append "("
			    (type-to-haskell-type (car tvars) module-name)
			    ", "
			    (type-to-haskell-type (cadr tvars) module-name)
			    ")"))
	    ((string=? name "ysum")
	     (string-append "(Either " tvar-names ")"))
	    ((or (string=? name "uysum") (string=? name "ysumu"))
	     (string-append "(Maybe " tvar-names ")"))
	    ((string=? name "unit") "()")
	    (else
	     (let* ((haskell-actual-type
		     (string-capitalize-first name))
		    (haskell-qualified-type
		     ;; Avoid clashes with the Haskell Prelude
		     (if (member name (list "Bool" "Char" "Double" "Either"
					    "FilePath" "Float" "Int"
					    "Integer" "IO" "IOError" "Maybe"
					    "Ordering" "ReadS"
					    "ShowS" "String" "Bounded"
					    "Enum" "Eq" "Floating"
					    "Fractional" "Functor"
					    "Integral" "Monad" "Num" "Ord"
					    "Read" "Real" "RealFloat"
					    "RealFrac" "Show" "Rational"
					    "EQ" "False" "GT" "Just" "Left"
					    "LT" "Nothing" "Right" "True"))
			 (string-append module-name "." haskell-actual-type)
			 haskell-actual-type)))
	       (if (null? tvars)
		   haskell-qualified-type
		   (string-append "(" haskell-qualified-type
				  " " tvar-names ")")))))))
	((arrow-form? type)
	 (let* ((arg (type-to-haskell-type (arrow-form-to-arg-type type)
                                           module-name))
		(val (type-to-haskell-type (arrow-form-to-val-type type)
                                           module-name)))
	   (string-append "(" arg " -> " val ")")))
	((star-form? type)
	 (let* ((left (type-to-haskell-type (star-form-to-left-type type)
                                            module-name))
		(right (type-to-haskell-type (star-form-to-right-type type)
                                             module-name)))
	   (string-append "(" left ", " right ")")))))

(define (pconst-name-to-haskell-function name module-name)
  ;; takes a term n and returns a triple (m subst guard), where
  ;; m is a term (in var form), subst is a substitution "n |-> n - k"
  ;; and guard is a string "m > (k - 1)"
  ;; used to turn
  ;;    f (suc (suc n)) = ... n ...
  ;; into
  ;;    f m | m > 1     = ... (n - 2) ...
  (define (fix-succ arg)
    (do ((curr-arg arg (term-in-app-form-to-arg curr-arg))
	 (count 0 (+ count 1)))
	((not (term-in-app-form? curr-arg))
	 (if (term-in-var-form? curr-arg)
	     (let* ((subst
		     (make-subst (term-in-var-form-to-var curr-arg)
				 (nt
				  (make-term-in-app-form
				   (make-term-in-app-form
				    (make-term-in-const-form
				     (pconst-name-to-pconst
				      "TranslationNatMinusPosDiff"))
				    curr-arg)
				   (make-numeric-term-wrt-nat
				    count))))))
	       (list curr-arg subst (string-append
				     (term-to-haskell-expr curr-arg)
				     " > " (number->string (- count 1)))))
	     (list arg empty-subst "")))))

  ;; Similar to fix-succ but for (arbitrary) positive numbers
  (define (fix-pos pos)
    (define (fix-pos-aux arg)
      (cond
       ((term-in-const-form? arg)
	(list #f arg '()))
       ((term-in-var-form? arg)
	(list arg arg '()))
       ((term-in-app-form? arg)
	(let* ((op (term-in-app-form-to-op arg))
	       (pat (term-in-app-form-to-arg arg))
	       (name (const-to-name (term-in-const-form-to-const op))))
	  (cond
	   ((string=? name "SOne")
	    (let* ((fixed-arg (fix-pos-aux pat))
		   (pat-var (car fixed-arg))
		   (pat-val (cadr fixed-arg))
		   (new-val (make-term-in-app-form
			     (make-term-in-const-form
			      (pconst-name-to-pconst "TranslationPosHalfEven"))
			     (make-term-in-app-form
			      (make-term-in-const-form
			       (pconst-name-to-pconst
				"TranslationPosPredNonOne"))
			      pat-val)))
		   (pat-guards (caddr fixed-arg)))
	      (list pat-var new-val
		    (cons (string-append "odd "
					 (term-to-haskell-expr pat-val))
			  pat-guards))))
	   ((string=? name "SZero")
	    (let* ((fixed-arg (fix-pos-aux pat))
		   (pat-var (car fixed-arg))
		   (pat-val (cadr fixed-arg))
		   (new-val (make-term-in-app-form
			     (make-term-in-const-form
			      (pconst-name-to-pconst "TranslationPosHalfEven"))
			     pat-val))
		   (pat-guards (caddr fixed-arg)))
	      (list pat-var new-val
		    (cons (string-append "even "
					 (term-to-haskell-expr pat-val))
			  pat-guards)))))))
       (else (myerror "pconst-name-to-haskell-function"
		      "constructor pattern expected" arg))))
    (let* ((fixed-pat (fix-pos-aux pos))
	   (var (car fixed-pat))
	   (new-pat (if var var pos))
	   (subst (if var (make-subst (term-in-var-form-to-var var)
				      (cadr fixed-pat)) empty-subst))
	   (guards (if var (apply string-append-with-sep " && "
				  (caddr fixed-pat)) "")))
      (list new-pat subst guards)))

  ;; Similar to fix-succ but for integers
  (define (fix-int arg)
    (cond
     ;; numeric patterns can (and should) be left as-is
     ((is-int-numeric-term? arg) (list arg empty-subst ""))
     ((term-in-app-form? arg)
      (let* ((intpos (string=? (const-to-name
				(term-in-const-form-to-const
				 (term-in-app-form-to-final-op arg)))
			       "IntPos"))
	     (fixed-arg (fix-pos (term-in-app-form-to-arg arg)))
	     (new-pat (make-term-in-app-form
		       (make-term-in-const-form
			(constr-name-to-constr "IntPos"))
		       (car fixed-arg)))
	     (new-subst
	      (if intpos (cadr fixed-arg)
		  (let* ((var (term-in-var-form-to-var (car fixed-arg)))
			 (old-subst (assoc var (cadr fixed-arg))))
		    (if old-subst
			(make-subst var (make-term-in-app-form
					 (make-term-in-const-form
					  (pconst-name-to-pconst
					   "TranslationPosNegForInt"))
					 (cadr old-subst)))
			empty-subst))))
	     (add-guard (if (substitution-equal? empty-subst new-subst)
			    ""
			    (string-append (term-to-haskell-expr new-pat)
					   (if intpos " > 0" " < 0"))))
	     (new-guard (if (string=? (caddr fixed-arg) "") add-guard
			    (string-append
			     add-guard " && " (caddr fixed-arg)))))
	(list new-pat new-subst new-guard)))
     ((or (term-in-const-form? arg) (term-in-var-form? arg))
      (list arg empty-subst ""))))

  (define (foreach-arg pat)
    (cond
     ((term-in-var-form? pat)
      (list pat empty-subst ""))
     ((or (term-in-app-form? pat) (term-in-const-form? pat))
      (let* ((const (term-in-const-form-to-const
		     (term-in-app-form-to-final-op pat)))
	     (name (const-to-name const)))
	(cond
	 ((string=? name "Succ")
	  (fix-succ pat)) ;(term-in-app-form-to-arg pat)))
	 ((member name (list "SZero" "SOne"))
	  (fix-pos pat))
	 ((member name (list "IntPos" "IntNeg"))
	  (fix-int pat))
	 ((string=? name "RatConstr")
	  (let* ((args (term-in-app-form-to-args pat))
		 (fixed-num (fix-int (car args)))
		 (fixed-denom (fix-pos (cadr args)))
		 (num-guard (caddr fixed-num))
		 (denom-guard (caddr fixed-denom))
		 (num-subst (cadr fixed-num))
		 (denom-subst (cadr fixed-denom))
		 (new-var (type-to-new-var (py "rat")))
		 (new-pat (make-term-in-var-form new-var))
		 (num-constant (null? (term-to-free (car args))))
		 (denom-constant (null? (term-to-free (cadr args))))
		 (num-var (if (null? num-subst)
			      (if num-constant (type-to-new-var (py "int"))
				  (car (type-to-tvars (car args))))
			      (caar num-subst)))
		 (denom-var (if (null? denom-subst)
				(if denom-constant (type-to-new-var (py "pos"))
				    (car (type-to-tvars (cadr args))))
				(caar denom-subst)))
		 (num-translation-term
		  (if (equal? (var-to-type num-var) (py "pos"))
		      (make-term-in-app-form
		       (make-term-in-const-form
			(pconst-name-to-pconst "TranslationPosAsInt"))
		       (make-term-in-app-form
			(make-term-in-const-form
			 (pconst-name-to-pconst "TranslationNumerator"))
			new-pat))
		      (make-term-in-app-form
		       (make-term-in-const-form
			(pconst-name-to-pconst "TranslationNumerator"))
		       new-pat)))
		 (new-num (make-subst num-var num-translation-term))
		 (new-denom (make-subst
			     denom-var
			     (make-term-in-app-form
			      (make-term-in-const-form
			       (pconst-name-to-pconst "TranslationDenominator"))
			      new-pat)))
		 (new-subst (compose-substitutions
			     new-denom (compose-substitutions
					new-num (compose-substitutions
						 num-subst denom-subst))))
		 (new-guards
		  (let* ((num-string (term-to-haskell-expr
				      (make-term-in-var-form num-var)))
			 (denom-string (term-to-haskell-expr
					(make-term-in-var-form
                                         denom-var)))
			 (new-num-string
                          (string-append "(numerator "
                                         (term-to-haskell-expr new-pat)
                                         ")"))
			 (new-denom-string
                          (string-append "(denominator "
                                         (term-to-haskell-expr new-pat)
                                         ")"))
			 (num-const-guard
			  (if num-constant
			      (string-append
			       num-string
			       " == "
			       (term-to-haskell-expr (car fixed-num)))
			      ""))
			 (denom-const-guard
			  (if denom-constant
			      (string-append
			       denom-string
			       " == "
			       (term-to-haskell-expr (car fixed-denom)))
			      ""))
			 (strings (if (> (string-length num-string)
					 (string-length denom-string))
				      (list num-string denom-string)
				      (list denom-string num-string)))
			 (new-strings
                          (if (> (string-length num-string)
                                 (string-length denom-string))
                              (list new-num-string new-denom-string)
                              (list new-denom-string new-num-string))))
		    (string-replace-substring
		     (string-replace-substring
		      (apply string-append-with-sep " && "
			     (list-transform-positive
				 (list num-guard num-const-guard
				       denom-guard denom-const-guard)
			       (lambda (x) (not (string=? x "")))))
		      (car strings)
		      (car new-strings))
		     (cadr strings)
		     (cadr new-strings)))))
	    (list new-pat new-subst new-guards)))
	 (else (list pat empty-subst "")))))
     (else (myerror "pconst-name-to-haskell-function"
		    "constructor pattern expected" pat))))

  ;; Uses fix-succ, fix-pos etc to turn a lhs pattern matching on
  ;; naturals, positive numbers, integers or rationals
  ;; into a non-pattern-matching lhs with guards
  (define (fix-lhs-nat-pos-int-rat lhs)
    (let* ((op (term-in-app-form-to-final-op lhs))
	   (args (term-in-app-form-to-args lhs))
	   (processed-args (map foreach-arg args))
	   (new-args (map car processed-args))
	   (subst (foldr compose-substitutions empty-subst
			 (map cadr processed-args)))
	   (guards (apply string-append-with-sep " && "
			  (list-transform-positive
			      (map caddr processed-args)
			    (lambda (x) (not (string=? x "")))))))
      (list (apply mk-term-in-app-form op new-args) subst guards)))

  (define (foreach-rule rule)
    (let* ((lhs-fixed (fix-lhs-nat-pos-int-rat (rule-to-lhs rule)))
	   (fixed-term (car lhs-fixed))
	   (fixed-subst (cadr lhs-fixed))
	   (fixed-guards (caddr lhs-fixed))
	   (lhs-with-possible-prefix
            (string-remove-outer-parens
             (apply term-to-haskell-expr fixed-term (list module-name))))
           (lhs (if (string-prefix? (string-append module-name ".")
                                    lhs-with-possible-prefix)
                    (substring lhs-with-possible-prefix
                               (+ (string-length module-name) 1)
			       (string-length lhs-with-possible-prefix))
                    lhs-with-possible-prefix))
	   (rhs (apply term-to-haskell-expr
		       (term-substitute (rule-to-rhs rule) fixed-subst)
		       (list module-name)))
	   (guards (if (string=? fixed-guards "")
		       ""
		       (string-append " | " fixed-guards))))
      (string-append lhs guards " = " rhs)))

  ;; Body of pconst-name-to-haskell-function
  (begin
    (reset-haskell-default-var)
    (let* ((comp-rules (pconst-name-to-comprules name))
           (pconst (pconst-name-to-pconst name))
           (inhab-constraints (pconst-name-to-inhab-constraints name))
           (type (type-to-haskell-type (const-to-type pconst) module-name))
           (constraints
	    (if (null? inhab-constraints) ""
		(string-append
		 "forall "
		 (apply string-append-with-sep " "
			(map (lambda (x)
			       (type-to-haskell-type x module-name))
			     (type-to-tvars (const-to-type pconst))))
		 " . "
		 (if (> (length inhab-constraints) 1) "(" "")
		 (apply string-append-with-sep ", "
			(map (lambda (x)
			       (string-append "Inhabited "
					      (type-to-haskell-type
					       x module-name)))
			     inhab-constraints))
		 (if (> (length inhab-constraints) 1) ")" "")
		 " => "))))
      (string-append
       (string-downcase-first name) " :: " constraints type "\n"
       (if (null? comp-rules)
	   (let* ((animate-advice
		   (if (and (char=? (string-ref name 0)
				    #\c)
			    (assoc (substring name 1
					      (string-length name))
				   THEOREMS))
		       (string-append
			" [try (animate \""
			(substring name 1
				   (string-length name))
			"\") ]")
		       "")))
	     (begin
	       (comment "warning: program constant " name
			" has no computation rules"
			animate-advice)
	       (string-append (string-downcase-first name)
			      " = undefined")))
	   (apply string-append-with-sep "\n"
		  (map foreach-rule comp-rules)))))))

(define (alg-and-rel-simalgs-to-haskell-rec-or-destr-const
	 alg-name rel-simalg-names kind module-name)
  (begin
    (reset-haskell-default-var)
    (let* ((all-simalg-names (alg-name-to-simalg-names alg-name))
           (constrs (alg-name-to-typed-constr-names alg-name))
           (uninst-alg (arrow-form-to-final-val-type
                        (typed-constr-name-to-type (car constrs))))
           (simalg-forms
            (map (compose arrow-form-to-final-val-type
			  typed-constr-name-to-type
			  car
			  alg-name-to-typed-constr-names)
                 (cons alg-name
                       (remove alg-name rel-simalg-names)))) ;put alg first
           (simp? (< (length rel-simalg-names) (length all-simalg-names)))
           (const (case kind
                    ((rec)
                     (apply arrow-types-to-rec-const
			    (map (lambda (x) (make-arrow x (new-tvar)))
				 simalg-forms)))
                    ((destr)
                     (alg-to-destr-const uninst-alg))))
           (relalg-names (apply string-append "_"
                                (map haskellify-string rel-simalg-names)))
           (name-postfix
            (case kind
              ((rec) (string-append
                      "Rec"
                      (if simp?
                          (string-append "Simp"
                                         (if (> (length all-simalg-names) 2)
                                             relalg-names ""))
                          "")))
              ((destr) "Destr")))
           (type (const-to-type const))
           (name (string-append (string-downcase-first alg-name) name-postfix))
           (common-args-list
            (map (compose make-term-in-var-form type-to-new-var)
                 (arrow-form-to-arg-types
                  (arrow-form-to-val-type type))))
           (foreach-constr
            (lambda (constr)
              (let* ((constr-name (typed-constr-name-to-name constr))
                     (patargs (map
                               (compose make-term-in-var-form
                                        type-to-new-var)
                               (arrow-form-to-arg-types
                                (typed-constr-name-to-type constr))))
                     (patvar (apply mk-term-in-app-form
                                    (make-term-in-const-form
                                     (constr-name-to-constr constr-name))
                                    patargs))
                     (lhs-term (apply mk-term-in-app-form
                                      (make-term-in-const-form const)
                                      (cons patvar common-args-list)))
                     (lhs (apply term-to-haskell-expr lhs-term
                                 (list module-name)))
                     (lhs-no-paren (string-remove-outer-parens lhs))
                     (rhs (apply term-to-haskell-expr (nt lhs-term)
                                 (list module-name))))
                (string-append lhs-no-paren " = " rhs)))))
      (string-append name " :: " (type-to-haskell-type type module-name) "\n"
                     (apply string-append-with-sep "\n"
                            (map foreach-constr constrs))))))

(define (alg-and-rel-simalgs-to-haskell-rec-const alg rel-simalgs module-name)
  (cond ((string=? alg "nat")
	 "natRec :: Nat -> a -> (Nat -> a -> a) -> a
natRec 0 g h = g
natRec n g h | n > 0 = h (n - 1) (natRec (n - 1) g h)")
	((string=? alg "rat")
	 "ratRec :: Rational -> (Rational -> Rational -> a) -> a
ratRec x g = g (numerator x) (denominator x)")
	((string=? alg "pos")
	 "posRec :: Pos -> a -> (Pos -> a -> a) -> (Pos -> a -> a) -> a
posRec x f g h | x == 1 = f
               | even x = g (x `quot` 2) (posRec (x `quot` 2) f g h)
               | odd x  = h ((x - 1) `quot` 2) (posRec ((x - 1) `quot` 2) f g h)")
	((string=? alg "int")
	 "intRec :: Integer -> (Integer -> a) -> a -> (Integer -> a) -> a
intRec n f g h | n > 0  = f n
               | n == 0 = g
               | n < 0 = h (-n)")
        (else (alg-and-rel-simalgs-to-haskell-rec-or-destr-const
	       alg rel-simalgs 'rec module-name))))

(define (alg-to-haskell-destr-const alg module-name)
  (cond ((string=? alg "nat")
	 "natDestr :: Nat -> Maybe Nat
natDestr 0 = Nothing
natDestr n | n > 0 = Just (n - 1)")
	((string=? alg "rat")
	 "ratDestr :: Rational -> (Integer , Pos)
ratDestr x = ((numerator x) , (denominator x))")
	((string=? alg "pos")
	 "posDestr :: Pos -> Maybe (Either Pos Pos)
posDestr 1 = Nothing
posDestr n | even n = Just (Left (n `quot` 2))
           | odd n  = Just (Right ((n - 1) `quot` 2))")
	((string=? alg "int")
	 "intDestr :: Integer -> (Either Pos (Maybe Pos)))
intDestr n | n > 0  = Left n
           | n == 0 = Right Nothing
           | n < 0  = Right (Just (-n))")
	(else
         (alg-and-rel-simalgs-to-haskell-rec-or-destr-const
	  alg '() 'destr module-name))))

(define (alg-and-rel-simalgs-to-haskell-corec-const
	 alg-name rel-simalg-names module-name)
  (begin
    (reset-haskell-default-var)
    (let* ((all-simalg-names (alg-name-to-simalg-names alg-name))
           (constrs (alg-name-to-typed-constr-names alg-name))
           (uninst-alg (arrow-form-to-final-val-type
                        (typed-constr-name-to-type (car constrs))))
           (alg-or-arrow
	    ((lambda (x) (if (member alg-name rel-simalg-names)
			     (make-arrow (new-tvar) x) x))
	     (arrow-form-to-final-val-type
	      (typed-constr-name-to-type
	       (car 
		(alg-name-to-typed-constr-names
		 alg-name))))))
           (rel-simalg-arrows (map (compose
				    (lambda (x) (make-arrow (new-tvar) x))
				    arrow-form-to-final-val-type
				    typed-constr-name-to-type
				    car
				    alg-name-to-typed-constr-names)
				   (remove alg-name rel-simalg-names)))
           (corec-const (apply alg-or-arrow-types-to-corec-const
			       (cons alg-or-arrow rel-simalg-arrows)))
           (simp? (< (length rel-simalg-names) (length all-simalg-names)))
           (type (const-to-type corec-const))
           (relalg-names (apply string-append "_"
                                (map haskellify-string rel-simalg-names)))
           (name (string-append
                  (string-downcase-first alg-name)
                  "CoRec"
                  (if simp? (string-append "Simp"
                                           (if (> (length all-simalg-names) 2)
                                               relalg-names ""))
		      "")))
           (args (map (compose make-term-in-var-form type-to-new-var)
		      (arrow-form-to-arg-types type)))
           (lhs-term (apply mk-term-in-app-form
                            (make-term-in-const-form corec-const)
                            args))
           (lhs (apply term-to-haskell-expr lhs-term (list module-name)))
           (lhs-no-paren (string-remove-outer-parens lhs))
           (rhs (apply term-to-haskell-expr
                       (nt (undelay-delayed-corec lhs-term 1))
                       (list module-name)))
           (equation (string-append lhs-no-paren " = " rhs)))
      (string-append name " :: " (type-to-haskell-type type module-name)
                     "\n" equation))))

(define (types-to-haskell-grec-const rhos module-name)
  (begin
    (reset-haskell-default-var)
    (let* ((fresh-var (new-tvar))
           (grec-const (type-info-to-grecguard-const (append rhos
                                                             (list fresh-var))))
           (type (const-to-type grec-const))
           (arg-types (arrow-form-to-arg-types type))
           (arg-types-without-bool (remove-last arg-types))
           (type-fix (if HASKELL-GREC-MEASURE-FLAG
                         type
                         (apply mk-arrow (cadr arg-types) ;remove measure
                                (append (cddr arg-types-without-bool)
                                        (list (arrow-form-to-final-val-type
                                               type))))))
           (name (string-downcase-first
                  (apply string-append (append (map (compose haskellify-string
                                                             type-to-string)
                                                    rhos)
                                               (list "GrecGuard")))))
           (arg-terms (map (compose make-term-in-var-form
                                    type-to-new-var)
                           arg-types-without-bool))
           (lhs-true (apply mk-term-in-app-form
                            (make-term-in-const-form grec-const)
                            (append arg-terms
                                    (list (make-term-in-const-form
                                           (constr-name-to-constr "True"))))))
           (lhs-false (apply mk-term-in-app-form
                             (make-term-in-const-form grec-const)
                             (append arg-terms
                                     (list (make-term-in-const-form
                                            (constr-name-to-constr "False"))))))
           (lhs-true-no-paren
            (string-remove-outer-parens
             (apply term-to-haskell-expr lhs-true (list module-name))))
           (lhs-false-no-paren
            (if HASKELL-GREC-MEASURE-FLAG
                (string-remove-outer-parens
                 (apply term-to-haskell-expr lhs-false (list module-name)))
                ""))
           (rhs-false (if HASKELL-GREC-MEASURE-FLAG
                          (apply term-to-haskell-expr (nt lhs-false)
                                 (list module-name))
                          ""))
           (rhs-true (apply term-to-haskell-expr (nt lhs-true)
                            (list module-name)))
           (goal-var-expr  (type-to-haskell-type fresh-var module-name)))
      (apply string-append name " :: "
             (append (if HASKELL-GREC-MEASURE-FLAG
                         (list "forall " goal-var-expr " . Inhabited "
                               goal-var-expr " => ")
                         '())
                     (list (type-to-haskell-type type-fix module-name) "\n")
                     (if HASKELL-GREC-MEASURE-FLAG
                         (list lhs-false-no-paren " = " rhs-false "\n")
                         '())
                     (list lhs-true-no-paren " = " rhs-true "\n"))))))

(define (type-to-haskell-inhab type module-name)
  (cond
   ((alg-form? type)
    (let* ((inhab (type-to-canonical-inhabitant type))
	   (inhab-expr (apply term-to-haskell-expr inhab
			      (list module-name)))
	   (constraints (term-to-inhab-constraints inhab))
	   (number-constraints (length constraints))
	   (constraints-expr
	    (if (null? constraints) ""
		(string-append
		 (if (> number-constraints 1) "(" "")
		 (apply string-append-with-sep ", "
			(map (lambda (x)
			       (string-append
				"Inhabited "
				(type-to-haskell-type x module-name)))
			     constraints))
		 (if (> number-constraints 1) ") => " " => "))))
	   (type-expr (type-to-haskell-type type module-name)))
      (string-append "instance " constraints-expr "Inhabited " type-expr
		     "\n  where inhab = " inhab-expr)))
   ((arrow-form? type) ;instance for b elsewhere, if needed
    "instance Inhabited b => Inhabited (a -> b)\n   where inhab =  \\ _ -> inhab")
   (else (myerror "type-to-haskell-inhab" "unexpected type" type))))

(define HASKELL-PCONST-INHAB-CONSTRAINTS '())
(define HASKELL-PCONST-INHAB-CHANGED '())

(define (adjoin-inhab-info type inhab-info)
  ;; Since we identify certain types when translating to haskell,
  ;; we have to identify their Inhabited instances as well
  (cond
   ((alg-form? type)
    (let* ((name (alg-form-to-name type)))
      (cond ((or (string=? name "nat") (string=? name "pos"))
             (adjoin (py "int") inhab-info))
            ((string=? name "ysumu")
             (adjoin (make-uysum (car (alg-form-to-types type))) inhab-info))
            (else (adjoin type inhab-info)))))
   ((star-form? type)
    (adjoin (make-yprod  (star-form-to-left-type type)
                         (star-form-to-right-type type))
            inhab-info))
   (else (adjoin type inhab-info))))

(define (adjoin-inhab-infos types inhab-info)
  (if (null? types) inhab-info
      (adjoin-inhab-infos (cdr types)
			  (adjoin-inhab-info (car types) inhab-info))))

;; Instances can contain duplicate elements -- feed through
;; adjoin-inhab-infos to fix or use term-to-inhab-instances
(define (term-to-inhab-constraints-and-instances term)
  (begin
    ;; keep calculating the constraints and instances until no more change
    (set! HASKELL-PCONST-INHAB-CHANGED #f)
    (do ((res (term-to-inhab-constraints-aux term '())
              (term-to-inhab-constraints-aux term '())))
        ((not HASKELL-PCONST-INHAB-CHANGED) res)
      (set! HASKELL-PCONST-INHAB-CHANGED #f))))

(define (term-to-inhab-constraints term)
  (car (term-to-inhab-constraints-and-instances term)))

(define (term-to-inhab-instances term)
  (adjoin-inhab-infos
   (cadr (term-to-inhab-constraints-and-instances term))
   '()))

(define (pconst-name-to-inhab-constraints name)
   (car (term-to-inhab-constraints-and-instances
          (make-term-in-const-form (pconst-name-to-pconst name)))))

(define (pconst-name-to-inhab-instances name)
  (adjoin-inhab-infos
   (cadr (term-to-inhab-constraints-and-instances
          (make-term-in-const-form (pconst-name-to-pconst name))))
   '()))

(define (pconst-name-to-inhab-constraints-aux name . in-progress)
  (let* ((memo (assoc name HASKELL-PCONST-INHAB-CONSTRAINTS)))
    (cond
     ((and (member name in-progress)
	   memo)
      (cdr memo))
     ((and (member name in-progress)
	   (not memo))
      (list '() '()))
     (else ;; not in progress
      (let* ((comp-rules (pconst-name-to-comprules name))
	     (pconst (pconst-name-to-pconst name))
	     (before memo)
	     (recursive-call
	      (lambda (x) (term-to-inhab-constraints-aux
			   x (cons name in-progress))))
	     (rhs-constraints
	      (map (compose recursive-call rule-to-rhs) comp-rules))
	     (new-constraints (apply union (map car rhs-constraints)))
	     (new-instances (apply union (map cadr rhs-constraints)))
	     (new-data (list new-constraints new-instances)))
	(if (or (and before (not (equal? (cdr before) new-data)))
		(and (not before) new-constraints))
	    (begin
	      (set! HASKELL-PCONST-INHAB-CHANGED #t)
	      (set! HASKELL-PCONST-INHAB-CONSTRAINTS
		    (assoc-set! HASKELL-PCONST-INHAB-CONSTRAINTS name new-data))
	      new-data)
	    new-data))))))

(define (type-at-inhab-to-constraints-and-instances type)

  ;;helper function that expands star-types and arrow-types
  (define (normalise x)
    (cond ((star-form? x)
           (adjoin (make-star (py "alpha1") (py "alpha2"))
                   (union (normalise (star-form-to-left-type x))
                          (normalise (star-form-to-right-type x)))))
          ((arrow-form? x)
           (adjoin (make-arrow (py "alpha1") (py "alpha2"))
                   (normalise (arrow-form-to-final-val-type x))))
          (else (list x))))

  (cond
   ((tvar-form? type)
    (list (list type) '()))
   ((and (alg-form? type)
	 (null? (alg-form-to-types type)))
    (list '() (list type)))
   ((and (alg-form? type)
	 (not (null? (alg-form-to-types type))))
    (let* ((args (alg-form-to-types type))
	   (uninst-alg
	    (arrow-form-to-final-val-type
	     (typed-constr-name-to-type
	      (car (alg-name-to-typed-constr-names
		    (alg-form-to-name type))))))
	   (subst-fun
	    (lambda (x)
	      (type-substitute x (make-substitution
				  (alg-form-to-types uninst-alg) args))))
	   (canonical-inhab (type-to-canonical-inhabitant uninst-alg))
	   (inhab-instances
	    (apply union (map (compose normalise subst-fun)
			      (term-to-inhab-instances canonical-inhab))))
	   (inhab-constraints
	    (apply union (map (compose normalise subst-fun)
			      (term-to-inhab-constraints canonical-inhab))))
	   (prevs (map type-at-inhab-to-constraints-and-instances args))
	   (constraints (intersection inhab-constraints
				      (apply union (map car prevs))))
	   (instances (adjoin uninst-alg
			      (intersection inhab-constraints
					    (apply union (map cadr prevs))))))
      (list constraints instances)))
   ((arrow-form? type)
    (let* ((prev (type-at-inhab-to-constraints-and-instances
		  (arrow-form-to-final-val-type type))))
      (list (car prev) (adjoin (make-arrow (py "alpha1") (py "alpha2"))
			       (cadr prev)))))
   ((star-form? type)
    (let* ((left-prev (type-at-inhab-to-constraints-and-instances
		       (star-form-to-left-type type)))
	   (right-prev (type-at-inhab-to-constraints-and-instances
			(star-form-to-right-type type))))
      (list (union (car left-prev) (car right-prev))
	    (adjoin (make-star (py "alpha1") (py "alpha2"))
		    (union (cadr left-prev) (cadr right-prev))))))
   (else
    (list '() '()))))

(define (term-to-inhab-constraints-aux term in-progress)
  (cond
   ((term-in-var-form? term)
    (list '() '()))
   ((term-in-const-form? term)
    (let* ((const (term-in-const-form-to-const term))
	   (name (const-to-name const))
	   (kind (const-to-kind const))
	   (type (const-to-type const)))
      (cond
       ((equal? kind 'pconst)
	(if (string=? name "Inhab")
	    (type-at-inhab-to-constraints-and-instances type)
	    (let* ((tvars (const-to-tvars const))
		   (tsubst (const-to-tsubst const))
		   (prev (apply pconst-name-to-inhab-constraints-aux name
				in-progress))
		   (prev-constraints (car prev))
		   (prev-instances (cadr prev))
		   (instantiated-tvars
		    (map (lambda (x) (type-substitute x tsubst))
			 prev-constraints))
		   (constraints (list-transform-positive
				    instantiated-tvars tvar-form?))
		   (instances (list-transform-positive instantiated-tvars
				(compose not tvar-form?))))
	      (list constraints
		    (union instances prev-instances)))))
       ((string=? name "GRecGuard")
	(if HASKELL-GREC-MEASURE-FLAG
	    (type-at-inhab-to-constraints-and-instances
	     (arrow-form-to-final-val-type type))
	    (list '() '())))
       (else (list '() '())))))
   ((term-in-app-form? term)
    (let* ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term))
	   (op-prev (term-to-inhab-constraints-aux op in-progress))
	   (arg-prev (term-to-inhab-constraints-aux arg in-progress)))
      (list (union  (car op-prev)  (car arg-prev))
	    (adjoin-inhab-infos (cadr op-prev) (cadr arg-prev)))))

   ((term-in-abst-form? term)
    (term-to-inhab-constraints-aux (term-in-abst-form-to-kernel term)
				   in-progress))
   ((term-in-pair-form? term)
    (let* ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term))
	   (left-prev (term-to-inhab-constraints-aux left in-progress))
	   (right-prev (term-to-inhab-constraints-aux right in-progress)))
      (list (union  (car left-prev)   (car right-prev))
	    (adjoin-inhab-infos (cadr left-prev) (cadr right-prev)))))
   ((term-in-lcomp-form? term)
    (term-to-inhab-constraints-aux (term-in-lcomp-form-to-kernel term)
				   in-progress))
   ((term-in-rcomp-form? term)
    (term-to-inhab-constraints-aux (term-in-rcomp-form-to-kernel term)
				   in-progress))
   ((term-in-if-form? term)
    (let* ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term))
	   (test-prev (term-to-inhab-constraints-aux test in-progress))
	   (alts-prev (map (lambda (x)
			     (term-to-inhab-constraints-aux x in-progress))
			   alts))
	   (alts-constraints (union (map car alts-prev)))
	   (alts-instances (union (map cadr alts-prev))))
      (list (apply union (car test-prev) alts-constraints)
	    (apply union (cadr test-prev) alts-instances))))
   (else (myerror "term-to-inhab-constraints" "unknown tag"
		  (tag term)))))

(define (terms-to-haskell-program
	 filename terms-and-function-names . opt-module-name)

  (define (foreach-fixed-rule info module-name)
    (let* ((name (car info))
	   (alg (cadr info))
           (simalgs (caddr info)))
      (cond
       ((string=? name "Rec")
	(alg-and-rel-simalgs-to-haskell-rec-const alg simalgs module-name))
       ((string=? name "CoRec")
	(alg-and-rel-simalgs-to-haskell-corec-const alg simalgs module-name))
       ((string=? name "Destr")
	(alg-to-haskell-destr-const alg module-name))
       ((string=? name "GRecGuard")
        (let* ((algs (if (type? alg) (list alg) alg)))
          (types-to-haskell-grec-const algs module-name)))
       (else (myerror "term-to-haskell-program"
		      "unknown fixed rule" name)))))

  (define (foreach-term term-and-function-name inhab-constraints module-name)
    (let* ((term (car term-and-function-name))
	   (function-name (cadr term-and-function-name))
	   (free-vars
	    (apply string-append-with-sep " "
		   (map (compose term-to-haskell-expr make-term-in-var-form)
			(term-to-free term))))
	   (term-expr (apply term-to-haskell-expr term (list module-name)))
	   (type-expr (if (and
                           (not HASKELL-GREC-MEASURE-FLAG)
                           (term-in-const-form? term)
                           (string=? (const-to-name
                                      (term-in-const-form-to-const term))
                                     "GRecGuard"))
                          "remove measure + bool" ;todo
                          (type-to-haskell-type (term-to-type
                                        ;take free variables into account
                                                 (abstraction-closure term))
                                                module-name)))
	   (number-constraints (length inhab-constraints))
           (constraints-expr
	    (if (null? inhab-constraints) ""
		(string-append
		 "forall "
		 (apply string-append-with-sep " "
			(map (lambda (x)
			       (type-to-haskell-type x module-name))
			     (type-to-tvars (term-to-type term))))
		 " . "
		 (if (> number-constraints 1) "(" "")
		 (apply string-append-with-sep ", "
			(map (lambda (x)
			       (string-append
				"Inhabited "
				(type-to-haskell-type x module-name)))
			     inhab-constraints))
		 (if (> number-constraints 1) ") => " " => ")))))
      (string-append function-name " :: " constraints-expr type-expr "\n"
		     function-name (if (string=? free-vars "") "" " ")
		     free-vars " = " term-expr)))

  ;; Main body of terms-to-haskell-program
  (begin
    (set! HASKELL-PCONST-INHAB-CONSTRAINTS '())
    (let* ((terms (map car terms-and-function-names))
           (module-name (if (null? opt-module-name) "Main"
                            (car opt-module-name)))
	   (info (map term-to-extraction-info terms))
	   (pconsts-info (apply union (map car info)))
	   (fixed-rules-info (apply union (map cadr info)))
	   (algebras-info (apply union (map caddr info)))
	   (inhab-constraints-and-instances
            (map term-to-inhab-constraints-and-instances terms))
           (inhab-constraints  (map car inhab-constraints-and-instances))
	   (inhabs-info-possible-clashes
            (apply union (map cadr inhab-constraints-and-instances)))
           (inhabs-info (adjoin-inhab-infos inhabs-info-possible-clashes '()))
           (preamble
            (generate-haskell-preamble algebras-info
                                       (or (not (null? inhabs-info))
                                           (check-all (compose not null?)
                                                      inhab-constraints))
                                       module-name))
	   (algebras (algebras-to-haskell-data algebras-info module-name))
           (inhabs (apply string-append-with-sep "\n\n"
                          (list-transform-positive
                              (map (lambda (x)
                                     (type-to-haskell-inhab x module-name))
				   inhabs-info)
                            (lambda (x) (not (string=? x ""))))))
	   (pconsts
	    (apply string-append-with-sep "\n\n"
		   (map (lambda (x)
			  (pconst-name-to-haskell-function x module-name))
			(set-minus pconsts-info BUILTIN-HASKELL-PCONSTS))))
	   (recops (apply string-append-with-sep "\n\n"
			  (map (lambda (x)
                                 (foreach-fixed-rule x module-name))
			       fixed-rules-info)))
	   (fun-decls (apply string-append-with-sep "\n\n"
			     (map (lambda (x y)
                                    (foreach-term x y module-name))
                                  terms-and-function-names
                                  inhab-constraints))))
      (begin
        (with-output-to-file filename
          (lambda ()
            (display (string-append
                      preamble
                      "\n\n----- Algebras ------------------\n\n"
                      algebras
                      (if (string=? inhabs "") "" "\n\n\n")
                      inhabs
                      "\n\n----- Recursion operators -------\n\n"
                      recops
                      "\n\n----- Program constants ---------\n\n"
                      pconsts
                      "\n\n---------------------------------\n\n"
                      fun-decls
                      (if (string=? module-name "Main")
                          "\n\n---------------------------------\n\nmain :: IO ()\nmain = putStrLn \"\""
                          "")))) 'replace)
                          ;; "")))))
        (comment "ok, output written to file " filename)))))

(define (term-to-haskell-program filename term function-name . opt-module-name)
  (apply terms-to-haskell-program filename
	 (list (list term function-name))
	 opt-module-name))

(define (terms-to-haskell-program-with-lemmas 
	 filename terms-and-function-names . opt-module-name)

  (define (animate-missing-pconsts terms) 
    ;; Takes list of terms and tries to animate all present pconsts without 
    ;; computation rules recursively. Returns list of newly animated pconsts 
    (let* ((info (map term-to-extraction-info terms))
	   (pconsts-info (apply union (map car info)))
	   (relevant-pconsts (set-minus pconsts-info BUILTIN-HASKELL-PCONSTS))
	   (missing-pconsts
	    (filter (lambda (x) 
		      (null? (pconst-name-to-comprules x))) relevant-pconsts)))
      (if (null? missing-pconsts)
	  '()
	  (begin
	    (map (lambda (x) (animate (substring x 1 (string-length x)))) 
		 missing-pconsts)
	    (append missing-pconsts (animate-missing-pconsts terms))))) )

  (let* ((terms (map car terms-and-function-names))
	 (animated-pconsts (animate-missing-pconsts terms)))
    (begin (apply terms-to-haskell-program
		  (cons filename 
			(cons terms-and-function-names opt-module-name)))
	   (map (lambda (x) (deanimate (substring x 1 (string-length x)))) 
		animated-pconsts)
	   *the-non-printing-object*)))

(define (modulo-safe x y)
  (if (= y 0)
      0
      (modulo x y)))

(define (quotient-safe x y)
  (if (= y 0)
      0
      (quotient x y)))

(define (is-numeric-term-wrt-pos? term)
  (or
   (and (term-in-const-form? term)
	(string=? "IntZero"
		  (const-to-name (term-in-const-form-to-const term))))
   (and (term-in-const-form? term)
	(string=? "One" (const-to-name (term-in-const-form-to-const term)))
        (string=? "pos" (type-to-string
                         (const-to-type (term-in-const-form-to-const term)))))
   (and (term-in-app-form? term)
	(let ((op (term-in-app-form-to-op term))
	      (arg (term-in-app-form-to-arg term)))
	  (and (term-in-const-form? op)
               (string=? "pos=>pos" (type-to-string
                                     (const-to-type
                                      (term-in-const-form-to-const op))))
               (let ((name (const-to-name (term-in-const-form-to-const op))))
		 (or (and (string=? "SZero" name)
			  (is-numeric-term-wrt-pos? arg))
		     (and (string=? "SOne" name)
			  (is-numeric-term-wrt-pos? arg)))))))))

(define (numeric-term-wrt-pos-to-number term)
  (cond
   ((and (term-in-const-form? term)
	 (string=? "IntZero" (const-to-name
			      (term-in-const-form-to-const term))))
    0)
   ((and (term-in-const-form? term)
	 (string=? "One" (const-to-name
			  (term-in-const-form-to-const term))))
    1)
   ((term-in-app-form? term)
    (let ((op (term-in-app-form-to-op term))
	  (arg (term-in-app-form-to-arg term)))
      (if
       (term-in-const-form? op)
       (let ((name (const-to-name (term-in-const-form-to-const op))))
	 (cond
	  ((string=? "SZero" name)
	   (* 2 (numeric-term-wrt-pos-to-number arg)))
	  ((string=? "SOne" name)
	   (+ 1 (* 2 (numeric-term-wrt-pos-to-number arg))))
	  (else (myerror "numeric-term-wrt-pos-to-number" "unexpected term"
			 term))))
       (myerror "numeric-term-wrt-pos-to-number" "unexpected term" term))))
   (else (myerror "numeric-term-wrt-pos-to-number" "unexpected term" term))))

(define (is-numeric-term-wrt-nat? term)
  (or
   (and (term-in-const-form? term)
	(string=? "Zero" (const-to-name (term-in-const-form-to-const term)))
        (string=? "nat" (type-to-string
                         (const-to-type (term-in-const-form-to-const term)))))
   (and (term-in-app-form? term)
	(let ((op (term-in-app-form-to-op term)))
	  (and (term-in-const-form? op)
	       (string=? "Succ" (const-to-name
				 (term-in-const-form-to-const op)))
               (string=? "nat=>nat" (type-to-string
                                     (const-to-type
                                      (term-in-const-form-to-const op))))
	       (is-numeric-term-wrt-nat? (term-in-app-form-to-arg term)))))))

(define (numeric-term-wrt-nat-to-number term)
  (if (equal? term (pt "Zero"))
      0
      (+ 1 (numeric-term-wrt-nat-to-number (term-in-app-form-to-arg term)))))

(define (is-int-numeric-term? term)
  (or
   (and
    (term-in-const-form? term)
    (string=? "int" (type-to-string
                     (const-to-type (term-in-const-form-to-const term))))
    (string=? "IntZero" (const-to-name
			 (term-in-const-form-to-const term))))
   (and
    (term-in-app-form? term)
    (let ((op (term-in-app-form-to-op term))
	  (arg (term-in-app-form-to-arg term)))
      (and (term-in-const-form? op)
           (string=? "pos=>int" (type-to-string
                                 (const-to-type
                                  (term-in-const-form-to-const op))))
	   (let ((name (const-to-name (term-in-const-form-to-const op))))
	     (or (and (string=? name "IntPos")
		      (is-numeric-term-wrt-pos? arg))
		 (and (string=? name "IntNeg")
		      (is-numeric-term-wrt-pos? arg)))))))))

(define (int-numeric-term-to-number term)
  (cond
   ((and (term-in-const-form? term)
	 (string=? "IntZero" (const-to-name
			      (term-in-const-form-to-const term))))
    0)
   ((term-in-app-form? term)
    (let ((op (term-in-app-form-to-op term))
	  (arg (term-in-app-form-to-arg term)))
      (if (term-in-const-form? op)
	  (let ((name (const-to-name (term-in-const-form-to-const op))))
	    (cond
	     ((string=? name "IntPos") (numeric-term-to-number arg))
	     ((string=? name "IntNeg") (- (numeric-term-to-number arg)))
	     (else (myerror "int-numeric-term-to-number"
			    "int numeric term expected"
			    term))))
	  (myerror "int-numeric-term-to-number" "int numeric term expected"
		   term))))
   (else (myerror "int-numeric-term-to-number" "int numeric term expected"
		  term))))

(define (is-rat-numeric-term? term)
  (and (term-in-app-form? term)
       (let ((op (term-in-app-form-to-final-op term))
	     (args (term-in-app-form-to-args term)))
	 (and (term-in-const-form? op)
              (string=? "int=>pos=>rat" (type-to-string
                                         (const-to-type
                                          (term-in-const-form-to-const op))))
	      (string=? "RatConstr"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args))
	      (let ((arg1 (car args))
		    (arg2 (cadr args)))
		(and (is-int-numeric-term? arg1)
		     (is-numeric-term-wrt-pos? arg2)))))))

(define (rat-numeric-term-to-number term)
  (let* ((args (term-in-app-form-to-args term))
	 (k (numeric-term-to-number (cadr args)))
	 (i (int-numeric-term-to-number (car args))))
    (/ i k)))

(define (remove-vacuous-beta-redex expr)
  (if (and (pair? expr)
	   (pair? (car expr))
	   (eq? 'lambda (caar expr))
	   (pair? (cadr (car expr)))
	   (not (member (car (cadr (car expr)))
			(expr-to-free (caddr (car expr))))))
      (caddr (car expr))
      expr))

(define (expr-to-free expr)
  (cond
   ((number? expr) '())
   ((boolean? expr) '())
   ((symbol? expr) (if (memq expr '(+ - * / <= <)) '() (list expr)))
   ((pair? expr)
    (case (car expr)
      ((lambda) (let ((var (caadr expr))
		      (kernel (caddr expr)))
		  (remove-wrt eq? var (expr-to-free kernel))))
      ((cons) (union (expr-to-free (cadr expr)) (expr-to-free (caddr expr))))
      ((car cdr) (expr-to-free (cadr expr)))
      ((if) (union (expr-to-free (cadr expr)) (expr-to-free (caddr expr))
		   (expr-to-free (cadddr expr))))
      ((let) (let* ((alist (cadr expr))
		    (kernel (caddr expr))
		    (bound-vars (map car alist))
		    (assigned-exprs (map cadr alist)))
	       (apply union (cons (set-minus (expr-to-free kernel) bound-vars)
				  (map expr-to-free assigned-exprs)))))
      ((cond) (let* ((conds (map car (cdr expr)))
		     (clauses (map cadr (cdr expr))))
		(apply union (map expr-to-free (append conds clauses)))))
      ((quote) '())
      (else (apply union (map expr-to-free expr)))))
   (else (myerror "expr-to-free" "unknown expr" expr))))

;; Here we assume that the keywords are among lambda cons car cdr if
;; let cond

(define |cId| (lambda (x) x))

;; The following have been moved to term.scm
;; (define |AndConst| (lambda (p) (lambda (q) (and p q))))
;; (define |ImpConst| (lambda (p) (lambda (q) (or (not p) q))))
(define |OrConst| (lambda (p) (lambda (q) (or p q))))
(define |NegConst| (lambda (p) (not p)))

(define |NatPlus| (lambda (x) (lambda (y) (+ x y))))
(define |PosPlus| (lambda (x) (lambda (y) (+ x y))))
(define |IntPlus| (lambda (x) (lambda (y) (+ x y))))
(define |RatPlus| (lambda (x) (lambda (y) (+ x y))))

(define |NatMinus| (lambda (x) (lambda (y) (- x y))))
(define |PosMinus| (lambda (x) (lambda (y) (- x y))))
(define |IntMinus| (lambda (x) (lambda (y) (- x y))))
(define |RatMinus| (lambda (x) (lambda (y) (- x y))))

(define |NatTimes| (lambda (x) (lambda (y) (* x y))))
(define |PosTimes| (lambda (x) (lambda (y) (* x y))))
(define |IntTimes| (lambda (x) (lambda (y) (* x y))))
(define |RatTimes| (lambda (x) (lambda (y) (* x y))))

(define |RatDiv| (lambda (x) (lambda (y) (/ x y))))

(define |NatLe| (lambda (x) (lambda (y) (<= x y))))
(define |PosLe| (lambda (x) (lambda (y) (<= x y))))
(define |IntLe| (lambda (x) (lambda (y) (<= x y))))
(define |RatLe| (lambda (x) (lambda (y) (<= x y))))

(define |NatLt| (lambda (x) (lambda (y) (< x y))))
(define |PosLt| (lambda (x) (lambda (y) (< x y))))
(define |IntLt| (lambda (x) (lambda (y) (< x y))))
(define |RatLt| (lambda (x) (lambda (y) (< x y))))

(define |S| (lambda (x) (+ x 1)))
(define |Succ| (lambda (x) (+ x 1)))
(define |IntS| (lambda (x) (+ x 1)))

(define |SZero| (lambda (x) (* x 2)))
(define |SOne| (lambda (x) (+ (* x 2) 1)))

(define |IntNeg| (lambda (x) (- x)))
(define |IntPos| (lambda (x) x))

(define |IntToNat| (lambda (x) (if (negative? x) (- x) x)))

(define |PosPred| (lambda (x) (if (= 1 x) 1 (- x 1))))

(define |cDC|
  (lambda (init)
    (lambda (step)
      (lambda (n)
	(if (= 1 n)
	    init
	    ((step n) (((|cDC| init) step) (- n 1))))))))

(define (posRec n)
  (lambda (init)
    (lambda (step0)
      (lambda (step1)
	(if (= 1 n)
	    init
	    (if (even? n)
		((step0 (/ n 2))
		 ((((posRec (/ n 2)) init) step0) step1))
		((step1 (/ (- n 1) 2))
		 ((((posRec (/ (- n 1) 2)) init) step0) step1))))))))

(define (natRec n)
  (lambda (init)
    (lambda (step)
      (if (= 0 n)
	  init
	  ((step (- n 1)) (((natRec (- n 1)) init) step))))))

(define (natGrecGuard h)
  (lambda (x)
    (lambda (G)
      (lambda (p)
	(if (equal? #t p)
	    ((G x) (lambda (y)
		     ((((natGrecGuard h) y) G) (< (h y) (h x)))))
	    0)))))

(define (natnatGrecGuard h)
  (lambda (x1)
    (lambda (x2)
      (lambda (G)
	(lambda (p)
	  (if (equal? #t p)
	      (((G x1) x2)
	       (lambda (y1)
		 (lambda (y2)
		   (((((natnatGrecGuard h) y1) y2) G)
		    (< ((h y1) y2) ((h x1) x2))))))
	      0))))))

(define |ListLength| (lambda (l) (length l)))

(define (listRec l)
  (lambda (init)
    (lambda (step)
      (if (null? l)
	  init
	  (let ((h (car l))
		(t (cdr l)))
	    (((step h) t) (((listRec t) init) step)))))))

(define (display-term term) (display (term-to-string term)))
(define dt display-term)

(define (composed? term)
  (and
   (not (is-numeric-term? term))
   (or
    (term-in-abst-form? term)
    (term-in-pair-form? term)
    (term-in-lcomp-form? term)
    (term-in-rcomp-form? term)
    (and
     (term-in-app-form? term)
     (let ((op (term-in-app-form-to-final-op term))
	   (args (term-in-app-form-to-args term)))
       (not (and (term-in-const-form? op)
		 (string=? "RealConstr"
			   (const-to-name (term-in-const-form-to-const op)))
		 (= 2 (length args))
		 (term-in-abst-form? (car args))
		 (not (member (term-in-abst-form-to-var (car args))
			      (term-to-free
			       (term-in-abst-form-to-kernel (car args)))))
		 (not (composed?
		       (term-in-abst-form-to-kernel (car args)))))))))))

(define (term-list-to-string term-list)
  (if (null? term-list)
      "()"
      (do ((l (cdr term-list) (cdr l))
	   (res (term-to-string (car term-list))
		(string-append res ", " (term-to-string (car l)))))
	  ((null? l) (string-append "(" res ")")))))

(define (term-to-name-tree term)
  (cond
   ((is-numeric-term? term)
    (numeric-term-to-number term))
   ((term-in-var-form? term)
    (let ((string (term-in-var-form-to-string term)))
      (if (member #\( (string->list string))
	  string
	  (string->symbol string))))
   ((term-in-const-form? term)
    (let ((string (term-in-const-form-to-string term)))
      (if (member #\( (string->list string))
	  string
	  (string->symbol string))))
   ((term-in-abst-form? term)
    (list
     'lambda
     (let ((string (var-to-string (term-in-abst-form-to-var term))))
       (if (member #\( (string->list string))
	   string
	   (string->symbol string)))
     (term-to-name-tree (term-in-abst-form-to-kernel term))))
   ((term-in-app-form? term)
    (let* ((op (term-in-app-form-to-final-op term))
	   (args (term-in-app-form-to-args term)))
      (if (= 2 (length args))
	  (list (term-to-name-tree (car args))
		(term-to-name-tree op)
		(term-to-name-tree (cadr args)))
	  (cons (term-to-name-tree op)
		(map term-to-name-tree args)))))
   ((term-in-pair-form? term)
    (list (term-to-name-tree (term-in-pair-form-to-left term))
	  '@
	  (term-to-name-tree (term-in-pair-form-to-right term))))
   ((term-in-lcomp-form? term)
    (list 'left (term-to-name-tree (term-in-lcomp-form-to-kernel term))))
   ((term-in-rcomp-form? term)
    (list 'right (term-to-name-tree (term-in-rcomp-form-to-kernel term))))
   ((term-in-if-form? term)
    (let* ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term))
	   (alg (term-to-type test))
	   (alg-name (alg-form-to-name alg)))
      (if
       (and CASE-DISPLAY (not (nested-alg-name? alg-name)))
       (let* ((typed-constr-names (alg-name-to-typed-constr-names alg-name))
	      (constr-names (map typed-constr-name-to-name typed-constr-names))
	      (constr-types (map typed-constr-name-to-type typed-constr-names))
	      (alg-tvars (alg-name-to-tvars alg-name))
	      (tparams (alg-form-to-types alg))
	      (tsubst (make-substitution alg-tvars tparams))
	      (constrs (map (lambda (constr-name)
			      (const-substitute
			       (constr-name-to-constr constr-name)
			       tsubst #t))
			    constr-names))
	      (lengths-of-arg-types
	       (map (lambda (x) (length (arrow-form-to-arg-types x)))
		    constr-types))
	      (expanded-alts
	       (map (lambda (alt l)
		      (term-to-simple-outer-eta-expansion alt l))
		    alts lengths-of-arg-types))
	      (alt-vars-list (map (lambda (alt l)
				    (term-in-abst-form-to-vars alt l))
				  expanded-alts lengths-of-arg-types))
	      (patterns
	       (map (lambda (constr vars)
		      (apply mk-term-in-app-form
			     (make-term-in-const-form constr)
			     (map make-term-in-var-form vars)))
		    constrs alt-vars-list))
	      (alt-kernels (map (lambda (alt l)
				  (term-in-abst-form-to-final-kernel alt l))
				expanded-alts lengths-of-arg-types)))
	 (apply list "case"
		(term-to-name-tree test)
		(map (lambda (pattern alt-kernel)
		       (list (term-to-name-tree pattern)
			     '->
			     (term-to-name-tree alt-kernel)))
		     patterns alt-kernels)))
       (apply list 'if
	      (term-to-name-tree (term-in-if-form-to-test term))
	      (map term-to-name-tree
		   (term-in-if-form-to-alts term))))))
    (else (myerror "term-to-name-tree" "term expected" term))))

;; 6-4. Normalization by evaluation
;; ================================

;; An object consists of a semantical value and a type.

(define (nbe-make-object type value) (list 'obj type value))
(define nbe-object-to-type cadr)
(define nbe-object-to-value caddr)
(define (nbe-object? x) (and (list? x) (not (null? x)) (eq? 'obj (car x))))

;; To work with objects, we need

(define (nbe-object-apply function-obj arg-obj)
  ((nbe-object-to-value function-obj) arg-obj))

(define (nbe-object-app function-obj . arg-objs)
  (if (null? arg-objs)
      function-obj
      (apply nbe-object-app
	     (nbe-object-apply function-obj (car arg-objs))
	     (cdr arg-objs))))

(define (nbe-object-compose obj1 obj2)
  (let* ((type1 (nbe-object-to-type obj1))
	 (type2 (nbe-object-to-type obj2))
	 (valtype1 (arrow-form-to-val-type type1))
	 (argtypes2 (arrow-form-to-arg-types type2))
	 (l (length argtypes2))
	 (type (apply mk-arrow (append argtypes2 (list valtype1)))))
    (if (zero? l)
	(nbe-object-app obj1 obj2)
	(nbe-make-object
	 type
	 (nbe-curry
	  (lambda arg-objs
	    (nbe-object-app
	     obj1
	     (apply (nbe-uncurry (nbe-object-to-value obj2) l) arg-objs)))
	  type
	  l)))))

(define (nbe-mk-prod-obj obj . objs)
  (if (null? objs)
      obj
      (let* ((prev (apply nbe-mk-prod-obj objs))
	     (type (make-star (nbe-object-to-type obj)
			      (nbe-object-to-type prev))))
	(nbe-make-object type (cons obj prev)))))

(define (nbe-object-car pair-object)
  (car (nbe-object-to-value pair-object)))

(define (nbe-object-cdr pair-object)
  (cdr (nbe-object-to-value pair-object)))

;; For ground type values we need constructors, accessors and tests:

;; To make constructors `self-evaluating', a constructor value has the form
;; ('constr-value name objs delayed-constr), where delayed-constr is a
;; procedure of zero arguments which evaluates to this very same constructor.
;; This is necessary to avoid having a cycle (for nullary constructors, and
;; only for those).

(define (nbe-make-constr-value name objs . delayed-constr)
  ;; delayed-constr is either present - in which case it is reproduced -
  ;; or not present - in which case it is computed (only once, thanks to
  ;; eval-once), via (constr-name-to-constr name).
  (let ((new-delayed-constr (if (null? delayed-constr)
				(eval-once
				 (lambda () (constr-name-to-constr name)))
				(car delayed-constr))))
    (list 'constr-value name objs new-delayed-constr)))

(define nbe-constr-value-to-name cadr)
(define nbe-constr-value-to-args caddr)
(define (nbe-constr-value-to-constr x) ((cadddr x)))

(define (nbe-constr-value? value)
  (and (pair? value) (eq? 'constr-value (car value))))

;; One might define nbe-constr-value-to-name here as follows.  However,
;; for systematic reasons this is better done locally.

;; (define (nbe-constr-value-to-name constr-value)
;;   (const-to-name (nbe-constr-value-to-constr constr-value)))

(define (nbe-fam-value? x)
  (and (pair? x) (eq? 'termfam (tag x))))

;; To work with term families we need

(define (nbe-make-termfam type proc)
  (list 'termfam type proc))

(define nbe-termfam-to-type cadr)
(define nbe-termfam-to-proc caddr)

(define (nbe-fam-apply termfam k)
  ((nbe-termfam-to-proc termfam) k))

(define (nbe-term-to-termfam term)
  (case (tag term)
    ((term-in-var-form term-in-const-form)
     (nbe-make-termfam (term-to-type term) (lambda (k) term)))
    ((term-in-abst-form)
     (let* ((var (term-in-abst-form-to-var term))
	    (type (var-to-type var))
	    (kernel (term-in-abst-form-to-kernel term)))
       (nbe-make-termfam
	(term-to-type term)
	(lambda (k)
	  (let ((var-k (make-var type k (var-to-t-deg var) (var-to-name var))))
	    (make-term-in-abst-form
	     var-k
	     (nbe-fam-apply
	      (nbe-term-to-termfam
	       (term-subst kernel var (make-term-in-var-form var-k)))
	      (+ 1 k))))))))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-final-op term))
	   (args (term-in-app-form-to-args term)))
       (nbe-make-termfam
	(term-to-type term)
	(lambda (k)
	  (apply mk-term-in-app-form
		 (map (lambda (x) (nbe-fam-apply (nbe-term-to-termfam x) k))
		      (cons op args)))))))
    ((term-in-pair-form)
     (nbe-make-termfam
      (term-to-type term)
      (lambda (k)
	(make-term-in-pair-form
	 (nbe-fam-apply
	  (nbe-term-to-termfam (term-in-pair-form-to-left term)) k)
	 (nbe-fam-apply
	  (nbe-term-to-termfam (term-in-pair-form-to-right term)) k)))))
    ((term-in-lcomp-form)
     (nbe-make-termfam
      (term-to-type term)
      (lambda (k)
	(make-term-in-lcomp-form
	 (nbe-fam-apply
	  (nbe-term-to-termfam (term-in-lcomp-form-to-kernel term)) k)))))
    ((term-in-rcomp-form)
     (nbe-make-termfam
      (term-to-type term)
      (lambda (k)
	(make-term-in-rcomp-form
	 (nbe-fam-apply
	  (nbe-term-to-termfam (term-in-rcomp-form-to-kernel term)) k)))))
    ((term-in-if-form)
     (let ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term))
	   (rest (term-in-if-form-to-rest term)))
       (nbe-make-termfam
	(term-to-type term)
	(lambda (k)
	  (apply
	   make-term-in-if-form
	   (nbe-fam-apply (nbe-term-to-termfam test) k)
	   (map (lambda (x) (nbe-fam-apply (nbe-term-to-termfam x) k))
		alts)
	   rest)))))
    (else (myerror "nbe-term-to-termfam" "unexpected term" term))))

;; nbe-reify takes an object and returns a term family

(define (nbe-reify obj)
  (let ((type (nbe-object-to-type obj))
	(value (nbe-object-to-value obj)))
    (case (tag type)
      ((alg)
       (cond
	((nbe-constr-value? value)
	 (let ((args (nbe-constr-value-to-args value)))
	   (nbe-make-termfam
	    type
	    (lambda (k)
	      (apply mk-term-in-app-form
		     (make-term-in-const-form
		      (nbe-constr-value-to-constr value))
		     (map (lambda (obj)
			    (nbe-fam-apply (nbe-reify obj) k))
			  args))))))
	((nbe-fam-value? value) value)
	(else (myerror "nbe-reify" "unexpected value" value
		       "for alg type" type))))
      ((tvar) (nbe-object-to-value obj))
      ((tconst)
       (if (string=? "existential" (tconst-to-name type))
	   (cond
	    ((nbe-constr-value? value)
	     (let ((args (nbe-constr-value-to-args value)))
	       (nbe-make-termfam
		type
		(lambda (k)
		  (apply mk-term-in-app-form
			 (make-term-in-const-form
			  (nbe-constr-value-to-constr value))
			 (map (lambda (obj)
				(nbe-fam-apply (nbe-reify obj) k))
			      args))))))
	    ((nbe-fam-value? value) value)
	    (else (myerror "nbe-reify" "unexpected value for type existential"
			   value)))
	   (nbe-object-to-value obj)))
      ((arrow)
       (let ((type1 (arrow-form-to-arg-type type)))
	 (nbe-make-termfam
	  type
	  (lambda (k)
	    (let ((var-k (make-var type1 k 1 (default-var-name type1))))
	      (make-term-in-abst-form
	       var-k (nbe-fam-apply
		      (nbe-reify
		       (nbe-object-apply
			obj
			(nbe-reflect (nbe-term-to-termfam
				      (make-term-in-var-form var-k)))))
		      (+ k 1))))))))
      ((star)
       (nbe-make-termfam
	type
	(lambda (k)
	  (make-term-in-pair-form
	   (nbe-fam-apply (nbe-reify (nbe-object-car obj)) k)
	   (nbe-fam-apply (nbe-reify (nbe-object-cdr obj)) k)))))
      (else (myerror "nbe-reify" "type expected" type)))))

;; nbe-reflect takes a term family and returns an object

(define (nbe-reflect termfam)
  (let ((type (nbe-termfam-to-type termfam)))
    (case (tag type)
      ((tvar tconst alg) (nbe-make-object type termfam))
      ((arrow)
       (nbe-make-object
	type
	(lambda (obj)
	  (nbe-reflect (nbe-make-termfam
			(arrow-form-to-val-type type)
			 (lambda (k)
			   (make-term-in-app-form
			    (nbe-fam-apply termfam k)
			    (nbe-fam-apply (nbe-reify obj) k))))))))
      ((star)
       (nbe-make-object
	type
	(cons (nbe-reflect
	       (nbe-make-termfam
		(star-form-to-left-type type)
		(lambda (k)
		  (make-term-in-lcomp-form (nbe-fam-apply termfam k)))))
	      (nbe-reflect
	       (nbe-make-termfam
		(star-form-to-right-type type)
		(lambda (k)
		  (make-term-in-rcomp-form (nbe-fam-apply termfam k))))))))
      (else (myerror "nbe-reflect" "type expected" type)))))

;; We now define nbe-term-to-object .  As a preparation we need some
;; procedures dealing with bindings, i.e. association lists associating
;; objects to variables.

(define (nbe-make-bindings vars objs)
  (map list vars objs))

(define (nbe-apply-bindings bindings var)
  (let ((info (assoc var bindings)))
    (if info
	(cadr info)
	(myerror "nbe-apply-bindings" "not bound in bindings" var))))

(define (nbe-extend-bindings bindings var obj) (cons (list var obj) bindings))

(define (nbe-term-to-object term bindings)
  (case (tag term)
    ((term-in-var-form)
     (let* ((var (term-in-var-form-to-var term))
	    (info (assoc var bindings)))
       (if info
	   (cadr info)
	   (nbe-reflect (nbe-term-to-termfam term)))))
    ((term-in-const-form)
     (let ((const (term-in-const-form-to-const term)))
       (case (const-to-kind const)
	 ((constr fixed-rules) (const-to-object-or-arity const))
	 ((pconst) (pconst-name-and-tsubst-to-object
		    (const-to-name const)
		    (const-to-tsubst const)))
	 (else (myerror "nbe-term-to-object" "kind expected"
			(const-to-kind const))))))
    ((term-in-abst-form)
     (let ((var (term-in-abst-form-to-var term))
	   (kernel (term-in-abst-form-to-kernel term))
	   (type (term-to-type term)))
       (nbe-make-object type (lambda (obj)
			       (nbe-term-to-object
				kernel
				(nbe-extend-bindings bindings var obj))))))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (nbe-object-app (nbe-term-to-object op bindings)
		       (nbe-term-to-object arg bindings))))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term))
	   (type (term-to-type term)))
       (nbe-make-object type (cons (nbe-term-to-object left bindings)
				   (nbe-term-to-object right bindings)))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (nbe-object-car (nbe-term-to-object kernel bindings))))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (nbe-object-cdr (nbe-term-to-object kernel bindings))))
    ((term-in-if-form)
     (let* ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term))
	    (rest (term-in-if-form-to-rest term))
	    (alg (term-to-type test))
	    (alg-name (alg-form-to-name alg))
	    (typed-constr-names (alg-name-to-typed-constr-names alg-name)))
       (cond
	((alts-from-constructors? alts typed-constr-names)
	 (nbe-term-to-object test bindings))
	((constant-alts? alts typed-constr-names)
	 (nbe-term-to-object
	  (constants-alts-to-const-term alts typed-constr-names)
	  bindings))
	(else
	 (let* ((testobj (nbe-term-to-object test bindings))
		(testval (nbe-object-to-value testobj)))
	   (if
	    (nbe-constr-value? testval)
	    (let* ((name (nbe-constr-value-to-name testval))
		   (args (nbe-constr-value-to-args testval))
		   (alg (term-to-type test))
		   (alg-name (alg-form-to-name alg))
		   (typed-constr-names
		    (alg-name-to-typed-constr-names alg-name))
		   (constr-names
		    (map typed-constr-name-to-name typed-constr-names))
		   (alt (do ((cs constr-names (cdr cs))
			     (as alts (cdr as))
			     (res #f (if (string=? (car cs) name)
					 (car as)
					 res)))
			    ((null? cs) res)))
		   (alt-obj (nbe-term-to-object alt bindings)))
	      (apply nbe-object-app alt-obj args))
	    (let* ((altobjs (map (lambda (x) (nbe-term-to-object x bindings))
				 alts))
		   (alt-termfams (map nbe-reify altobjs))
		   (norm-alts (map nbe-extract alt-termfams)))
	      (cond
	       ((alts-from-constructors? norm-alts typed-constr-names)
		(nbe-term-to-object test bindings))
	       ((constant-alts? norm-alts typed-constr-names)
		(nbe-term-to-object
		 (constants-alts-to-const-term alts typed-constr-names)
		 ;; (constants-alts-to-const-term norm-alts typed-constr-names)
		 bindings))
	       (else
		(nbe-reflect
		 (nbe-make-termfam
		  (term-to-type term)
		  (lambda (k)
		    (apply
		     make-term-in-if-form
		     (nbe-fam-apply (nbe-reify testobj) k)
		     (map (lambda (x) (nbe-fam-apply x k))
			  alt-termfams)
		     rest)))))))))))))
    (else (myerror "nbe-term-to-object" "unexpected term" term))))

(define (alts-from-constructors? alts typed-constr-names)
  (equal? (map typed-constr-name-to-name typed-constr-names)
	  (map (lambda (alt)
		 (let* ((kernel-and-vars
			 (term-in-abst-form-to-kernel-and-vars alt))
			(kernel (car kernel-and-vars))
			(vars (cdr kernel-and-vars))
			(op (term-in-app-form-to-final-op kernel))
			(args (term-in-app-form-to-args kernel)))
		   (if (and (apply and-op (map term-in-var-form? args))
			    (equal? vars (map term-in-var-form-to-var args))
			    (term-in-const-form? op))
		       (const-to-name (term-in-const-form-to-const op))
		       "")))
	       alts)))

(define (constant-alts? alts typed-constr-names)
  (let* ((constr-types (map typed-constr-name-to-type typed-constr-names))
	 (arg-types-list (map arrow-form-to-arg-types constr-types))
	 (alt-kernels-or-false
	  (do ((l1 alts (cdr l1))
	       (l2 arg-types-list (cdr l2))
	       (res '() (let* ((alt (car l1))
			       (arg-types (car l2))
			       (kernel-and-vars
				(term-in-abst-form-to-kernel-and-vars alt))
			       (kernel (car kernel-and-vars))
			       (vars (cdr kernel-and-vars)))
			  (if (and res
				   (= (length arg-types) (length vars))
				   (null? (intersection
					   vars (term-to-free kernel))))
			      (cons kernel res)
			      #f))))
	      ((or (not res) (null? l1)) res))))
    (and alt-kernels-or-false ;and all alt-kernels are equal
	 (do ((l alt-kernels-or-false (cdr l))
	      (l1 (cdr alt-kernels-or-false) (cdr l1))
	      (res #t (and res (term=? (car l) (car l1)))))
	     ((or (not res) (null? l1)) res)))))

(define (constants-alts-to-const-term alts typed-constr-names)
  (let* ((typed-constr-name (typed-constr-name-to-name typed-constr-names))
	 (constr-type (typed-constr-name-to-type typed-constr-name))
	 (arg-types (arrow-form-to-arg-types constr-type))
	 (alt (car alts))
	 (kernel-and-vars (term-in-abst-form-to-kernel-and-vars alt)))
    (car kernel-and-vars)))

(define (nbe-constructor-pattern? term)
  (or (term-in-var-form? term)
      (and (ground-type? (term-to-type term))
	   (or (and (term-in-const-form? term)
		    (eq? 'constr (const-to-kind
				  (term-in-const-form-to-const term))))
	       (and (term-in-app-form? term)
		    (let ((op (term-in-app-form-to-final-op term))
			  (args (term-in-app-form-to-args term)))
		      (and (term-in-const-form? op)
			   (eq? 'constr (const-to-kind
					 (term-in-const-form-to-const op)))
			   (apply and-op (map nbe-constructor-pattern?
					      args)))))))))

(define (nbe-inst? constr-pattern obj)
  (case (tag constr-pattern)
    ((term-in-var-form) #t)
    ((term-in-const-form)
     (let ((const (term-in-const-form-to-const constr-pattern)))
       (and
	(eq? 'constr (const-to-kind const))
	(let ((value (nbe-object-to-value obj)))
	  (cond ((nbe-constr-value? value)
		 (string=? (const-to-name const)
			   (const-to-name (nbe-constr-value-to-constr value))))
		((nbe-fam-value? value) #f)
		(else (myerror "nbe-inst?" "value expected" value)))))))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-final-op constr-pattern))
	   (args (term-in-app-form-to-args constr-pattern)))
       (case (tag op)
	 ((term-in-const-form)
	  (let ((const (term-in-const-form-to-const op)))
	    (and
	     (eq? 'constr (const-to-kind const))
	     (let* ((value (nbe-object-to-value obj)))
	       (cond ((nbe-constr-value? value)
		      (let ((vargs (nbe-constr-value-to-args value)))
			(and (string=? (const-to-name const)
				       (const-to-name
					(nbe-constr-value-to-constr value)))
			     (= (length args) (length vargs))
			     (apply and-op (map nbe-inst? args vargs)))))
		     ((nbe-fam-value? value) #f)
		     (else (myerror "nbe-inst?" "value expected" value)))))))
	 (else (myerror "nbe-inst?" "constructor expected" op)))))
    (else
     (myerror "nbe-inst?" "constructor pattern expected" constr-pattern))))

(define (nbe-genargs constr-pattern obj)
  (case (tag constr-pattern)
    ((term-in-var-form) (list obj))
    ((term-in-const-form) '()) ;then of ground type
    ((term-in-app-form)
     (let* ((op (term-in-app-form-to-final-op constr-pattern))
	    (args1 (term-in-app-form-to-args constr-pattern))
	    (value (nbe-object-to-value obj)))
       (cond
	((and (term-in-const-form? op)
	      (eq? 'constr (const-to-kind (term-in-const-form-to-const op)))
	      (nbe-constr-value? value))
	 (let* ((constr1 (term-in-const-form-to-const op))
		(name1 (const-to-name constr1))
		(constr2 (nbe-constr-value-to-constr value))
		(name2 (const-to-name (nbe-constr-value-to-constr value)))
		(args2 (nbe-constr-value-to-args value)))
	   (if
	    (and
	     (string=? name1 name2)
	     (or
	      (not (string=? "Ex-Intro" name1))
	      (and
	       (formula=? (const-to-uninst-type constr1)
			  (const-to-uninst-type constr2))
	       (let ((subst1 (const-to-tsubst constr1))
		     (subst2 (const-to-tsubst constr2)))
		 (and
		  (substitution-equal?
		   (restrict-substitution-wrt subst1 tvar-form?)
		   (restrict-substitution-wrt subst2 tvar-form?))
		  (substitution-equal-wrt?
		   equal? classical-cterm=?
		   (restrict-substitution-wrt subst1 pvar?)
		   (restrict-substitution-wrt subst2  pvar?))))))
	     (= (length args1) (length args2)))
	    (apply append (map nbe-genargs args1 args2))
	    (myerror "nbe-genargs" "matching object expected"
		     constr-pattern))))
	(else (myerror "nbe-genargs" "same constructor kinds expected"
		       op value)))))
    (else (myerror "nbe-genargs" "constructor pattern expected"
		   constr-pattern))))

(define (nbe-extract termfam)
  (let* ((term (nbe-fam-apply termfam 0))
	 (free (term-to-free term))
	 (bound (term-to-bound term))
	 (k (do ((l (append free bound) (cdr l))
		 (res 0 (if (default-var? (car l))
			    (max res (+ 1 (var-to-index (car l))))
			    res)))
		((null? l) res))))
    (nbe-fam-apply termfam k)))

(define (nbe-normalize-term-without-eta term)
  (let* ((free (term-to-free term))
	 (index (+ 1 (max-index free)))
	 (objs (map (lambda (x) (nbe-reflect
				 (nbe-term-to-termfam
				  (make-term-in-var-form x)))) free)))
    (nbe-fam-apply
     (nbe-reify (nbe-term-to-object term (nbe-make-bindings free objs)))
     index)))

;; 6-5.  Further normal forms
;; ==========================

(define (term-to-eta-nf term) ;term in long normal form
  (case (tag term)
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (make-term-in-app-form (term-to-eta-nf op) (term-to-eta-nf arg))))
    ((term-in-abst-form)
     (let* ((var (term-in-abst-form-to-var term))
	    (kernel (term-in-abst-form-to-kernel term))
	    (prev (term-to-eta-nf kernel)))
       (cond
	((and ;[x]rx -> r, if x not free in r
	  (term-in-app-form? prev)
	  (term=? (term-in-app-form-to-arg prev)
		  (make-term-in-var-form var))
	  (not (member var (term-to-free
			    (term-in-app-form-to-op prev)))))
	 (term-in-app-form-to-op prev))
	(else (make-term-in-abst-form var prev)))))
    ((term-in-pair-form)
     (let* ((left (term-in-pair-form-to-left term))
	    (right (term-in-pair-form-to-right term))
	    (prev-left (term-to-eta-nf left))
	    (prev-right (term-to-eta-nf right)))
       (cond
	((and ;(left r)@(right r) -> r
	  (term-in-lcomp-form? prev-left)
	  (term-in-rcomp-form? prev-right)
	  (term=? (term-in-lcomp-form-to-kernel prev-left)
		  (term-in-rcomp-form-to-kernel prev-right)))
	 (term-in-lcomp-form-to-kernel prev-left))
	((and ;[if t [ys,zs]r1 ..]@[if t [ys,zs]r2 ..] -> [if t [ys,zs]r1@r2..]
	  (term-in-if-form? prev-left)
	  (term-in-if-form? prev-right)
	  (term=? (term-in-if-form-to-test prev-left)
		  (term-in-if-form-to-test prev-right)))
	 (let* ((test (term-in-if-form-to-test prev-left))
		(alg (term-to-type test))
		(alg-name (alg-form-to-name alg))
		(typed-constr-names (alg-name-to-typed-constr-names alg-name))
		(constr-types
		 (map typed-constr-name-to-type typed-constr-names))
		(ls (map (lambda (x) (length (arrow-form-to-arg-types x)))
			 constr-types))
		(alts1 (term-in-if-form-to-alts prev-left))
		(rest1 (term-in-if-form-to-rest prev-left))
		(constr-arg-vars-list1
		 (map (lambda (alt l) (term-in-abst-form-to-vars alt l))
		      alts1 ls))
		(kernels1
		 (map (lambda (alt l)
			(term-in-abst-form-to-final-kernel alt l))
		      alts1 ls))
		(alts2 (term-in-if-form-to-alts prev-right))
		(rest2 (term-in-if-form-to-rest prev-right))
		(constr-arg-vars-list2
		 (map (lambda (alt l) (term-in-abst-form-to-vars alt l))
		      alts2 ls))
		(kernels2
		 (map (lambda (alt l)
			(term-in-abst-form-to-final-kernel alt l))
		      alts2 ls))
		(equal-constr-arg-vars?-list
		 (map (lambda (vars1 vars2) (equal? vars1 vars2))
		      constr-arg-vars-list1 constr-arg-vars-list2))
		(constr-arg-vars-list
		 (map (lambda (boole vars1 vars2)
			(if boole vars1 (map var-to-new-var vars2)))
		      equal-constr-arg-vars?-list
		      constr-arg-vars-list1 constr-arg-vars-list2))
		(pair-alts
		 (map (lambda (boole vars vars2 kernel1 kernel2)
			(apply
			 mk-term-in-abst-form
			 (append vars (list (make-term-in-pair-form
					     kernel1
					     (if boole
						 kernel2
						 (term-substitute
						  kernel2
						  (map (lambda (x y)
							 (list x y))
						       vars2 vars))))))))
		      equal-constr-arg-vars?-list
		      constr-arg-vars-list constr-arg-vars-list2
		      kernels1 kernels2))
		(pair-alts-nf (map term-to-eta-nf pair-alts)))
	   (make-term-in-if-form
	    test (map term-to-eta-nf pair-alts) (make-and rest1 rest2))))
	(else (make-term-in-pair-form prev-left prev-right)))))
    ((term-in-lcomp-form)
     (let ((prev (term-to-eta-nf (term-in-lcomp-form-to-kernel term))))
       (if (term-in-pair-form? prev)
	   (term-in-pair-form-to-left prev)
	   (make-term-in-lcomp-form prev))))
    ((term-in-rcomp-form)
     (let ((prev (term-to-eta-nf (term-in-rcomp-form-to-kernel term))))
       (if (term-in-pair-form? prev)
	   (term-in-pair-form-to-right prev)
	   (make-term-in-rcomp-form prev))))
    ((term-in-if-form)
     (let* ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term))
	    (rest (term-in-if-form-to-rest term))
	    (prev (term-to-eta-nf test))
	    (prevs (map term-to-eta-nf alts)))
       (apply make-term-in-if-form prev prevs rest)))
    (else term)))

;; Now: full normalization of terms including permutative conversions.
;; In a preprocessing step, eta expand the alternatives of if-terms.
;; The result contains if-terms with ground type alternatives only.
;; Example: "[if boole ((nat=>nat)_1) ((nat=>nat)_2)]" is rewritten
;; into "[n33][if boole ((nat=>nat)_1 n33) ((nat=>nat)_2 n33)]".

(define (term-to-term-with-eta-expanded-if-terms term)
  (case (tag term)
    ((term-in-var-form term-in-const-form)
     term)
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (make-term-in-app-form (term-to-term-with-eta-expanded-if-terms op)
			      (term-to-term-with-eta-expanded-if-terms arg))))
    ((term-in-abst-form)
     (let ((var (term-in-abst-form-to-var term))
	   (kernel (term-in-abst-form-to-kernel term)))
       (make-term-in-abst-form
	var (term-to-term-with-eta-expanded-if-terms kernel))))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term)))
       (make-term-in-pair-form
	(term-to-term-with-eta-expanded-if-terms left)
	(term-to-term-with-eta-expanded-if-terms right))))
    ((term-in-lcomp-form)
     (make-term-in-lcomp-form
      (term-to-term-with-eta-expanded-if-terms
       (term-in-lcomp-form-to-kernel term))))
    ((term-in-rcomp-form)
     (make-term-in-rcomp-form
      (term-to-term-with-eta-expanded-if-terms
       (term-in-rcomp-form-to-kernel term))))
    ((term-in-if-form)
     (if-term-to-eta-expansion term))
    (else (myerror "term-to-term-with-eta-expanded-if-terms" "term expected"
		   term))))

;; As an auxiliary function we have used:

(define (if-term-to-eta-expansion term)
  (let ((type (term-to-type term)))
    (case (tag type)
      ((arrow)
       (let* ((arg-types (arrow-form-to-arg-types type))
	      (arg-vars (map type-to-new-var arg-types))
	      (make-intro
	       (lambda (t) (apply mk-term-in-abst-form
				  (append arg-vars (list t)))))
	      (elim-args (map make-term-in-var-form arg-vars)))
	 (if-term-to-eta-expansion-aux term make-intro elim-args)))
      ((star)
       (if-term-to-eta-expansion-aux term
				     make-term-in-pair-form
				     (list 'left) (list 'right)))
      (else term))))

;; if-term-to-eta-expansion-aux is a generic helper function, which
;; does eta-expansion in an if term over a composite type (arrow or
;; star), where the introduction term constructor is make-intro and the
;; arguments for elimination are given in elim-args-list

(define (if-term-to-eta-expansion-aux term make-intro . elim-args-list)
  (let* ((test (term-in-if-form-to-test term))
	 (alts (term-in-if-form-to-alts term))
	 (rest (term-in-if-form-to-rest term))
	 (prev-test (term-to-term-with-eta-expanded-if-terms test))
	 (prev-alts (map term-to-term-with-eta-expanded-if-terms alts))
	 (alg (term-to-type test))
	 (alg-name (alg-form-to-name alg))
	 (typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (ls (map (lambda (x) (length (arrow-form-to-arg-types x)))
		  constr-types))
	 (constr-arg-types-list ;without arg-types
	  (map (lambda (l alt)
		 (arrow-form-to-arg-types (term-to-type alt) l))
	       ls alts))
	 (constr-arg-vars-list
	  (map (lambda (types) (map type-to-new-var types))
	       constr-arg-types-list))
	 (applied-alts-list
	  (map (lambda (elim-args)
		 (map (lambda (alt constr-arg-vars)
			(apply
			 mk-term-in-app-form
			 alt (append
			      (map make-term-in-var-form
				   (append constr-arg-vars))
			      elim-args)))
		      prev-alts constr-arg-vars-list))
	       elim-args-list))
	 (abstr-applied-alts-list
	  (map (lambda (applied-alts)
		 (map (lambda (constr-arg-vars applied-alt)
			(apply mk-term-in-abst-form
			       (append constr-arg-vars (list applied-alt))))
		      constr-arg-vars-list applied-alts))
	       applied-alts-list)))
    (apply make-intro
	   (map (lambda (abstr-applied-alt)
		  (if-term-to-eta-expansion
		   (make-term-in-if-form
		    prev-test abstr-applied-alt rest)))
		abstr-applied-alts-list))))

;; We now do permutative conversions for if-terms.  Notice that this is
;; not possible for recursion terms.  However we can (and do) simplify
;; (Rec arrow-types)param-args rec-arg step-args val-args into the term
;; [if rec-arg simplified-step-args]val-args.

;; As auxiliary function we have used rec-op-and-args-to-if-term.  We
;; assume that op is rec with sufficiently many arguments.

(define (normalize-term-pi-with-rec-to-if term)
  (let* ((op (term-in-app-form-to-final-op term))
	 (args (term-in-app-form-to-args term)))
    (if ;op is rec with sufficiently many args
     (and (term-in-const-form? op)
	  (let* ((const (term-in-const-form-to-const op))
		 (name (const-to-name const))
		 (uninst-type (const-to-uninst-type const))
		 (arg-types (arrow-form-to-arg-types uninst-type)))
	    (and (string=? "Rec" name)
		 (<= (length arg-types) (length args)))))
     (let* ((rec-or-if-term (rec-op-and-args-to-if-term op args))
	    (new-op (term-in-app-form-to-final-op rec-or-if-term))
	    (new-args (term-in-app-form-to-args rec-or-if-term)))
       (if ;term changed.  Then recursive call and beta-normalization
	(not (and (term-in-const-form? new-op)
		  (string=? "Rec" (const-to-name
				   (term-in-const-form-to-const new-op)))))
	(nbe-normalize-term-without-eta
	 (normalize-term-pi-with-rec-to-if rec-or-if-term))
					;else recursive call on new-args
	(apply mk-term-in-app-form
	       new-op (map normalize-term-pi-with-rec-to-if new-args))))
     (case (tag term)
       ((term-in-var-form term-in-const-form) term)
       ((term-in-abst-form)
	(let ((var (term-in-abst-form-to-var term))
	      (kernel (term-in-abst-form-to-kernel term)))
	  (make-term-in-abst-form
	   var (normalize-term-pi-with-rec-to-if kernel))))
       ((term-in-pair-form)
	(let ((left (term-in-pair-form-to-left term))
	      (right (term-in-pair-form-to-right term)))
	  (make-term-in-pair-form
	   (normalize-term-pi-with-rec-to-if left)
	   (normalize-term-pi-with-rec-to-if right))))
       ((term-in-app-form) ;f([if t [xs]r ..]s) := [if t [xs]f(r s) ..]
	(normalize-term-pi-with-rec-to-if-aux
	 make-term-in-app-form
	 (term-in-app-form-to-op term)
	 (term-in-app-form-to-arg term)))
       ((term-in-lcomp-form)
	(normalize-term-pi-with-rec-to-if-aux
	 make-term-in-lcomp-form
	 (term-in-lcomp-form-to-kernel term)))
       ((term-in-rcomp-form)
	(normalize-term-pi-with-rec-to-if-aux
	 make-term-in-rcomp-form
	 (term-in-rcomp-form-to-kernel term)))
       ((term-in-if-form)
	(normalize-term-pi-with-rec-to-if-aux
	 (lambda (test alts)
	   (make-term-in-if-form test alts (term-in-if-form-to-rest term)))
	 (term-in-if-form-to-test term)
	 (term-in-if-form-to-alts term)))
       (else (myerror "normalize-term-pi-with-rec-to-if"
		      "term expected" term))))))

;; normalize-term-pi-with-rec-to-if-aux permutes an elimination over
;; another one.

(define (normalize-term-pi-with-rec-to-if-aux make-term op . args)
  (let ((prev (normalize-term-pi-with-rec-to-if op)))
    (if
     (term-in-if-form? prev)
     (let* ((test (term-in-if-form-to-test prev))
	    (alts (term-in-if-form-to-alts prev))
	    (rest (term-in-if-form-to-rest prev))
	    (alg (term-to-type test))
	    (alg-name (alg-form-to-name alg))
	    (typed-constr-names (alg-name-to-typed-constr-names alg-name))
	    (constr-types (map typed-constr-name-to-type typed-constr-names))
	    (ls (map (lambda (x) (length (arrow-form-to-arg-types x)))
		     constr-types))
	    (vars-list (map (lambda (l alt)
			      (term-in-abst-form-to-vars alt l))
			    ls alts))
	    (kernels (map (lambda (l alt)
			    (term-in-abst-form-to-final-kernel alt l))
			  ls alts))
	    (prevs (map (lambda (x)
			  (normalize-term-pi-with-rec-to-if
			   (apply make-term x args)))
			kernels))
	    (new-alts (map (lambda (xs y)
			     (apply mk-term-in-abst-form
				    (append xs (list y))))
			   vars-list prevs)))
       (make-term-in-if-form test new-alts rest))
     (apply make-term
	    prev (map (lambda (arg)
			(if (term-form? arg)
			    (normalize-term-pi-with-rec-to-if arg)
			    (map normalize-term-pi-with-rec-to-if arg)))
		      args)))))

(define (rec-op-and-args-to-if-term op args)
  (define (split dup-indicator vars)
    ;; vars has two vars for every #t in dup-indicator and one var for
    ;; every #f.  The result is a list of one or two element lists.
    ;; (split '(#t #f #t) '(a1 a2 b c1 c2)) -> ((a1 a2) (b) (c1 c2))
    (if (null? dup-indicator)
	'()
	(if (car dup-indicator)
	    (cons (list (car vars) (cadr vars))
		  (split (cdr dup-indicator) (cddr vars)))
	    (cons (list (car vars))
		  (split (cdr dup-indicator) (cdr vars))))))
  (let* ((rec-const (term-in-const-form-to-const op))
	 (rec-arg (car args))
	 (rest-args (cdr args))
	 (uninst-type (const-to-uninst-type rec-const))
	 (alg-name (alg-form-to-name (arrow-form-to-arg-type uninst-type)))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (uninst-step-types
	  (arrow-form-to-arg-types (arrow-form-to-val-type uninst-type)))
	 (typed-constr-names
	  (apply append (map (lambda (alg-name)
			       (alg-name-to-typed-constr-names alg-name))
			     simalg-names)))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (tvars (alg-name-to-tvars alg-name))
	 (algs (map (lambda (name) (apply make-alg name tvars)) simalg-names))
	 (alg-tvars (map (lambda (x) (new-tvar)) simalg-names)) ;xis
	 (constr-types-with-alg-tvars
	  (map (lambda (type)
		 (type-gen-substitute type (map list algs alg-tvars)))
	       constr-types))
	 (val-tvars (map arrow-form-to-final-val-type uninst-step-types))
	 (val-tvar (arrow-form-to-final-val-type uninst-type))
	 (tsubst (const-to-tsubst rec-const))
	 (rel-step-args-and-constr-types-with-alg-tvars
	  (do ((l1 rest-args (cdr l1))
	       (l2 uninst-step-types (cdr l2))
	       (l3 constr-types-with-alg-tvars (cdr l3))
	       (res '() (if (equal? (arrow-form-to-final-val-type (car l2))
				    val-tvar)
			    (cons (list (car l1) (car l3)) res)
			    res)))
	      ((null? l2) (reverse res))))
	 (rel-step-args (map car rel-step-args-and-constr-types-with-alg-tvars))
	 (rel-constr-types-with-alg-tvars
	  (map cadr rel-step-args-and-constr-types-with-alg-tvars))
	 (arg-types-list ;the rho_{i nu} with nu<n_i
	  (map arrow-form-to-arg-types rel-constr-types-with-alg-tvars))
	 (dup-indicators ;#t for unnested recursive argument types
	  (map (lambda (arg-types)
		 (map (lambda (arg-type)
			(pair?
			 (member (arrow-form-to-final-val-type arg-type)
				 alg-tvars)))
		      arg-types))
	       arg-types-list))
	 (arg-vars-list (map term-in-abst-form-to-vars rel-step-args))
	 (arg-kernels (map term-in-abst-form-to-final-kernel rel-step-args))
	 (var-lists-list ;list of lists of one or two element lists
	  (map split dup-indicators arg-vars-list))
	 (argtype-vars-alists
	  (map (lambda (arg-types var-lists)
		 (map list arg-types var-lists))
	       arg-types-list var-lists-list))
	 ;; (algvars-list (map (lambda (argtype-vars-alist)
	 ;; 		      (map car (map cadr argtype-vars-alist)))
	 ;; 		    argtype-vars-alists))
	 (prev-arg-vars-list
	   (map (lambda (argtype-vars-alist)
		  (map cadr
		       (map cadr (list-transform-positive argtype-vars-alist
				   (lambda (x) (= 2 (length (cadr x))))))))
		argtype-vars-alists))
	 (k (length uninst-step-types))
	 (val-args (list-tail rest-args k)))
    (if (apply and-op
	       (not (nested-alg-name? alg-name))
	       (map (lambda (vs arg-kernel)
		      (null? (intersection vs (term-to-free arg-kernel))))
		    prev-arg-vars-list arg-kernels))
	(let* ((simplified-rel-step-args
		(map (lambda (vs ws arg-kernel)
		       (apply mk-term-in-abst-form
			      (append (set-minus ws vs) (list arg-kernel))))
		     prev-arg-vars-list arg-vars-list arg-kernels))
	       ;; (simplified-rel-step-args
	       ;; 	(map (lambda (algvars arg-kernel)
	       ;; 	       (apply mk-term-in-abst-form
	       ;; 		      (append algvars (list arg-kernel))))
	       ;; 	     algvars-list arg-kernels))
	       (if-term (apply mk-term-in-app-form
			       (make-term-in-if-form
				rec-arg simplified-rel-step-args)
			       val-args)))
	  (if (null? val-args)
	      if-term
	      (term-to-term-with-eta-expanded-if-terms if-term)))
	(apply mk-term-in-app-form op args))))

(define (term-in-if-normal-form? term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) #t)
    ((term-in-abst-form)
     (let ((kernel (term-in-abst-form-to-kernel term)))
       (term-in-if-normal-form? kernel)))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (and (term-in-if-normal-form? op)
	    (term-in-if-normal-form? arg))))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term)))
       (and (term-in-if-normal-form? left)
	    (term-in-if-normal-form? right))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (term-in-if-normal-form? kernel)))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-rcomp-form-to-kernel term)))
       (term-in-if-normal-form? kernel)))
    ((term-in-if-form)
     (let ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term)))
       (and (let ((op (term-in-app-form-to-final-op test)))
	      (not (and (term-in-const-form? op)
			(eq? 'constr (const-to-kind
				      (term-in-const-form-to-const op))))))
	    (term-in-if-normal-form? test)
	    (apply and-op (map term-in-if-normal-form? alts)))))))

;; We need to unfold simplified simrec-constants with sufficiently many
;; (eta expanded) arguments, for normalization.

(define (unfold-simplified-simrec-appterm term)
  (let*
      ((op (term-in-app-form-to-final-op term))
       (args (term-in-app-form-to-args term))
       (rec-const (if (and (term-in-const-form? op)
			   (string=? "Rec" (const-to-name
					    (term-in-const-form-to-const op))))
		      (term-in-const-form-to-const op)
		      (myerror "unfold-simplified-simrec-appterm"
			       "rec constant expected in" term)))
       (rec-arg (if (pair? args) (car args)
		    (myerror "unfold-simplified-simrec-appterm"
			     "rec argument expected in" term)))
       (step-args-and-rest-args (cdr args))
       (uninst-arrow-types (rec-const-to-uninst-arrow-types rec-const))
       (tsubst (const-to-tsubst rec-const)) ;for tparams and val-tvars
       (uninst-arrow-type (car uninst-arrow-types))
       (alg-name (alg-form-to-name (arrow-form-to-arg-type uninst-arrow-type)))
       (tvars (alg-name-to-tvars alg-name))
       (simalg-names (alg-name-to-simalg-names alg-name))
       (rel-alg-names ;relevant alg-names in the order prescribed by ALGEBRAS
	(list-transform-positive simalg-names
	  (lambda (x)
	    (member x (map (lambda (type)
			     (alg-form-to-name (arrow-form-to-arg-type type)))
			   uninst-arrow-types)))))
       (irrel-alg-names (set-minus simalg-names rel-alg-names))
       (rel-algs (map (lambda (x) (apply make-alg x tvars)) rel-alg-names))
       (rel-val-tvars (map arrow-form-to-val-type uninst-arrow-types))
       (rel-alg-names-to-val-tvars-alist
	(map (lambda (x)
	       (list (alg-form-to-name (arrow-form-to-arg-type x))
		     (arrow-form-to-val-type x)))
	     uninst-arrow-types))
       (alg-names-to-val-tvars-alist
	(map (lambda (name)
	       (let ((info (assoc name rel-alg-names-to-val-tvars-alist)))
		 (list name (if info
				(cadr info)
				(apply make-alg name tvars)))))
	     simalg-names))
       (constr-names (map typed-constr-name-to-name
			  (apply append (map alg-name-to-typed-constr-names
					     rel-alg-names))))
       (step-args (if (<= (length constr-names)
			  (length step-args-and-rest-args))
		      (list-head step-args-and-rest-args (length constr-names))
		      (myerror "unfold-simplified-simrec-appterm"
			       "more arguments expected in" term)))
       (rest-args (list-tail step-args-and-rest-args (length constr-names)))
       (constr-name-to-step-alist (map list constr-names step-args))
       (repro-data (const-to-repro-data rec-const))
       (extended-repro-data ;extended for irrel algs
	(cond
	 ((and (pair? repro-data) (imp-form? (car repro-data)))
	  (let* ((prems (map imp-form-to-premise repro-data))
		 (preds (map predicate-form-to-predicate prems))
		 (names (map idpredconst-to-name preds))
		 (name (car names))
		 (simidpc-names (idpredconst-name-to-simidpc-names name))
		 (added-names (set-minus simidpc-names names))
		 (types (idpredconst-to-types (car preds)))
		 (cterms (idpredconst-to-cterms (car preds)))
		 (added-idpcs (map (lambda (name)
				     (make-idpredconst name types cterms))
				   added-names))
		 (added-arities (map idpredconst-to-arity added-idpcs))
		 (added-type-lists (map arity-to-types added-arities))
		 (added-var-lists (map (lambda (types)
					 (map type-to-new-partial-var types))
				       added-type-lists))
		 (added-varterm-lists (map (lambda (vars)
					     (map make-term-in-var-form vars))
					   added-var-lists))
		 (added-imp-formulas
		  (map (lambda (pred varterms)
			 (let ((predicate-formula
				(apply make-predicate-formula pred varterms)))
			   (make-imp predicate-formula predicate-formula)))
		       added-idpcs added-varterm-lists)))
	    (append repro-data added-imp-formulas)))
	 ((and (pair? repro-data) (all-form? (car repro-data)))
	  repro-data)
	 ((null? repro-data)
	  (let ((inst-arrow-types
		 (map (lambda (x) (type-substitute x tsubst))
		      uninst-arrow-types))
		(added-arrow-types ;inst alg=>alg for irrel algs
		 (map (lambda (x)
			(let* ((tparams (map (lambda (x)
					       (type-substitute x tsubst))
					     tvars))
			       (alg (apply make-alg x tparams)))
			  (make-arrow alg alg)))
		      irrel-alg-names)))
	    (append inst-arrow-types added-arrow-types)))
	 (else (myerror "unfold-simplified-simrec-appterm"
			"unexpected repro data" repro-data))))
       (expanded-steps
	(apply
	 append
	 (map
	  (lambda (name)
	    (map
	     (lambda (constr-name)
	       (let ((uninst-constr-type
		      (const-to-uninst-type
		       (constr-name-to-constr constr-name))))
		 (if
		  (member name rel-alg-names)
		  (let*
		      ((step-type ;uninst
			(constructor-type-to-step-type
			 uninst-constr-type alg-names-to-val-tvars-alist))
		       (arg-types (arrow-form-to-arg-types step-type))
		       (step
			(cadr (assoc constr-name constr-name-to-step-alist)))
		       (step-vars (term-in-abst-form-to-vars step))
		       (step-kernel (term-in-abst-form-to-final-kernel step))
		       (irrel-arg-type?
			(lambda (type)
			  (pair? (intersection (type-to-alg-names type)
					       irrel-alg-names))))
		       (expanded-step-vars
			(do ((l arg-types (cdr l))
			     (i 0 (if (irrel-arg-type? (car l)) i (+ i 1)))
			     (res
			      '()
			      (if (irrel-arg-type? (car l))
				  (cons (type-to-new-var
					 (type-substitute (car l) tsubst))
					res)
				  (cons
				   (if (< i (length step-vars))
				       (list-ref step-vars i)
				       (myerror
					"unfold-simplified-simrec-appterm"
					"eta-expanded step expected" step))
				   res))))
			    ((null? l) (reverse res)))))
		    (apply mk-term-in-abst-form
			   (append expanded-step-vars (list step-kernel))))
					;else expanded constructor term
		  (let*
		      ((uninst-expanded-step-type
			(constructor-type-to-step-type
			 uninst-constr-type alg-names-to-val-tvars-alist))
		       (expanded-step-type
			(type-substitute uninst-expanded-step-type tsubst))
		       (arg-types (arrow-form-to-arg-types expanded-step-type))
		       (val-type (arrow-form-to-final-val-type
				  expanded-step-type))
		       (inhab-term (type-to-canonical-inhabitant val-type))
		       (new-vars (map type-to-new-var arg-types)))
		    (apply mk-term-in-abst-form
			   (append new-vars (list inhab-term)))))))
	     (map typed-constr-name-to-name
		  (alg-name-to-typed-constr-names name))))
	  simalg-names)))
       (expanded-rec-const
	(cond ((imp-form? (car extended-repro-data))
	       (apply imp-formulas-to-rec-const extended-repro-data))
	      ((all-form? (car extended-repro-data))
	       (apply all-formulas-to-rec-const extended-repro-data))
	      ((type-form? (car extended-repro-data))
	       (car (apply arrow-types-to-rec-consts extended-repro-data)))
	      (else (myerror "unfold-simplified-simrec-appterm"
			     "unexpected expanded-rec-const"
			     expanded-rec-const)))))
    (apply mk-term-in-app-form
	   (make-term-in-const-form expanded-rec-const)
	   rec-arg (append expanded-steps rest-args))))

;; We want to fold a simrec-appterm into its simplified form.

(define (simplify-simrec-appterm term)
  (let*
      ((op (term-in-app-form-to-final-op term))
       (args (term-in-app-form-to-args term))
       (rec-const (if (and (term-in-const-form? op)
			   (string=? "Rec" (const-to-name
					    (term-in-const-form-to-const op))))
		      (term-in-const-form-to-const op)
		      (myerror "simplify-simrec-appterm"
			       "rec constant expected in" term)))
       (rec-arg (if (pair? args) (car args)
		    (myerror "simplify-simrec-appterm"
			     "rec argument expected in" term)))
       (step-args-and-rest-args (cdr args))
       (uninst-arrow-types (rec-const-to-uninst-arrow-types rec-const))
       (tsubst (const-to-tsubst rec-const)) ;for tparams and val-tvars
       (uninst-arrow-type (car uninst-arrow-types))
       (alg-name (alg-form-to-name (arrow-form-to-arg-type uninst-arrow-type)))
       (tvars (alg-name-to-tvars alg-name))
       (simalg-names (alg-name-to-simalg-names alg-name))
       (alg-names-to-val-tvars-alist
	(map (lambda (x)
	       (list (alg-form-to-name (arrow-form-to-arg-type x))
		     (arrow-form-to-val-type x)))
	     uninst-arrow-types))
       (typed-constr-names (apply append (map alg-name-to-typed-constr-names
					      simalg-names)))
       (constr-names (map typed-constr-name-to-name typed-constr-names))
       (constr-types (map typed-constr-name-to-type typed-constr-names))
       (step-args (if (<= (length constr-names)
			  (length step-args-and-rest-args))
		      (list-head step-args-and-rest-args (length constr-names))
		      (myerror "simplify-simrec-appterm"
			       "more arguments expected in" term)))
       (alg-names-with-immed-pd-alg-names
	(map
	 (lambda (alg-name)
	   (do ((l1 step-args (cdr l1))
		(l2 constr-names (cdr l2))
		(l3 constr-types (cdr l3))
		(res
		 '()
		 (let* ((step-arg (car l1))
			(constr-name (car l2))
			(constr-type (car l3)))
		   (if
		    (string=? alg-name (alg-form-to-name
					(arrow-form-to-final-val-type
					 constr-type))) ;else no change in res
		    (let* ((step-type ;uninst
			    (constructor-type-to-step-type
			     constr-type alg-names-to-val-tvars-alist))
			   (arg-types (arrow-form-to-arg-types step-type))
			   (step-vars (term-in-abst-form-to-vars step-arg))
			   (step-kernel
			    (term-in-abst-form-to-final-kernel step-arg))
			   (new-vars (map type-to-new-var
					  (arrow-form-to-arg-types
					   (term-to-type step-kernel))))
			   (new-step-kernel
			    (apply mk-term-in-app-form
				   step-kernel
				   (map make-term-in-var-form new-vars)))
			   (crit-arg-types
			    (do ((x1 arg-types (cdr x1))
				 (x2 (append step-vars new-vars) (cdr x2))
				 (res1
				  '()
				  (if (member (car x2)
					      (term-to-free new-step-kernel))
				      (cons (car x1) res1)
				      res1)))
				((null? x1) (reverse res1))))
			   (pd-alg-names
			    (list-transform-positive simalg-names
			      (lambda (name)
				(or
				 (member name (apply
					       append (map type-to-alg-names
							   crit-arg-types)))
				 (let* ((info
					 (assoc name
						alg-names-to-val-tvars-alist))
					(tvar
					 (if info (cadr info)
					     (myerror
					      "simplify-simrec-appterm"
					      "val-tvar missing for alg-name"
					      name))))
				   (member
				    tvar (apply
					  append (map type-to-tvars
						      crit-arg-types)))))))))
		      (union (remove alg-name pd-alg-names) res))
		    res))))
	       ((null? l2) (cons alg-name (reverse res)))))
	 simalg-names))
       (alg-names-with-pd-alg-names
	(let ((closure-op
	       (lambda (names)
		 (apply
		  union
		  names
		  (map (lambda (name)
			 (let ((info (assoc
				      name alg-names-with-immed-pd-alg-names)))
			   (if info (cdr info) '())))
		       names)))))
	  (map (lambda (name) (cons name (set-closure (list name) closure-op)))
	       simalg-names)))
       (irrel-alg-names
	(set-minus simalg-names
		   (assoc alg-name alg-names-with-immed-pd-alg-names)))
       (shortened-step-args-and-constr-types ;those for relevant alg-names
	(do ((l1 step-args (cdr l1))
	     (l2 constr-types (cdr l2))
	     (res '() (if (member (alg-form-to-name
				   (arrow-form-to-final-val-type (car l2)))
				  irrel-alg-names)
			  res
			  (cons (list (car l1) (car l2)) res))))
	    ((null? l1) (reverse res))))
       (shortened-step-args (map car shortened-step-args-and-constr-types))
       (shortened-constr-types (map cadr shortened-step-args-and-constr-types))
       (irrel-val-tvars
	(map cadr (list-transform-positive alg-names-to-val-tvars-alist
		    (lambda (x) (member (car x) irrel-alg-names)))))
       (simplified-shortened-step-args  ;remove abstracted vars for
					;irrel-alg-names and irrel-val-tvars
	(map (lambda (step-arg constr-type)
	       (let* ((step-vars (term-in-abst-form-to-vars step-arg))
		      (step-kernel
		       (term-in-abst-form-to-final-kernel step-arg))
		      (uninst-step-arg-types
		       (arrow-form-to-arg-types
			(constructor-type-to-step-type
			 constr-type alg-names-to-val-tvars-alist)))
		      (vars-for-alg-name
		       (do ((l1 step-vars (cdr l1))
			    (l2 uninst-step-arg-types (cdr l2))
			    (res
			     '()
			     (let ((argvaltype
				    (arrow-form-to-final-val-type (car l2))))
			       (if
				(or (and (alg-form? argvaltype)
					 (member (alg-form-to-name argvaltype)
						 irrel-alg-names))
				    (and (tvar-form? argvaltype)
					 (member argvaltype irrel-val-tvars)))
				res
				(cons (car l1) res)))))
			   ((null? l1) (reverse res)))))
		 (apply mk-term-in-abst-form
			(append vars-for-alg-name (list step-kernel)))))
	     shortened-step-args shortened-constr-types))
       (rel-uninst-arrow-types
	(list-transform-positive uninst-arrow-types
	  (lambda (x)
	    (not (member (alg-form-to-name (arrow-form-to-arg-type x))
			 irrel-alg-names)))))
       (rel-arrow-types (map (lambda (x) (type-substitute x tsubst))
			     rel-uninst-arrow-types))
       (uninst-recop-types-and-new-tsubst
	(apply arrow-types-to-uninst-recop-types-and-tsubst
	       rel-arrow-types))
       (uninst-recop-type (caar uninst-recop-types-and-new-tsubst))
       (new-tsubst (cadr uninst-recop-types-and-new-tsubst))
       (repro-data (const-to-repro-data rec-const))
       (shortened-repro-data
	(cond
	 ((and (pair? repro-data) (imp-form? (car repro-data)))
	  (list-transform-positive repro-data
	    (lambda (x)
	      (let* ((prem (imp-form-to-premise x))
		     (pred (predicate-form-to-predicate prem))
		     (name (idpredconst-to-name pred))
		     (nbe-alg-name (idpredconst-name-to-nbe-alg-name
				    name)))
		(member nbe-alg-name rel-alg-names)))))
	 ((and (pair? repro-data) (all-form? (car repro-data))) repro-data)
	 ((null? repro-data) '())
	 (else (myerror "simplify-simrec-appterm"
			"unexpected repro data" repro-data))))
       (simplified-rec-const
	(apply
	 make-const
	 (append
	  (list (const-to-object-or-arity rec-const)
		"Rec" 'fixed-rules uninst-recop-type new-tsubst 1 'const)
	  shortened-repro-data))))
    (apply mk-term-in-app-form
	   (make-term-in-const-form simplified-rec-const)
	   rec-arg simplified-shortened-step-args)))

(define (term-to-outer-eta-expansion term)
  (let ((type (term-to-type term)))
    (if (arrow-form? type)
	(let* ((arg-type (arrow-form-to-arg-type type))
	       (val-type (arrow-form-to-val-type type))
	       (var (type-to-new-var arg-type)))
	  (make-term-in-abst-form
	   var (term-to-outer-eta-expansion
		(make-term-in-app-form
		 term (term-to-outer-eta-expansion
		       (make-term-in-var-form var))))))
	term)))

;; (pp (term-to-outer-eta-expansion (pt "(Rec tlist unit=>nat)")))

;; Assume term is in long normal form.

(define (term-to-eta-nf-with-simplified-simrec-appterms term)
  (case (tag term)
    ((term-in-app-form)
     (let* ((op (term-in-app-form-to-final-op term))
	    (args (term-in-app-form-to-args term))
	    (prev-args
	     (map term-to-eta-nf-with-simplified-simrec-appterms args)))
       (cond ;op is simrec-constant
	((and
	  (term-in-const-form? op)
	  (string=? "Rec" (const-to-name (term-in-const-form-to-const op)))
	  (let* ((const (term-in-const-form-to-const op))
		 (uninst-type (const-to-uninst-type const))
		 (arg-types (arrow-form-to-arg-types uninst-type))
		 (alg-type (car arg-types))
		 (alg-name (alg-form-to-name alg-type))
		 (simalg-names (alg-name-to-simalg-names alg-name)))
	    (< 1 (length simalg-names))))
	 (simplify-simrec-appterm
	  (apply mk-term-in-app-form op prev-args)))
	((and (term-in-const-form? op)
	      (= 2 (length args))
	      (string=? "PairConstr"
			(const-to-name (term-in-const-form-to-const op))))
	 (let ((prev-left (car prev-args))
	       (prev-right (cadr prev-args)))
	   (if
	    (and ;lft r pair rht r -> r, clft r pair crht r -> r
	     (term-in-app-form? prev-left)
	     (term-in-app-form? prev-right)
	     (let ((op1 (term-in-app-form-to-op prev-left))
		   (arg1 (term-in-app-form-to-arg prev-left))
		   (op2 (term-in-app-form-to-op prev-right))
		   (arg2 (term-in-app-form-to-arg prev-right)))
	       (and
		(term-in-const-form? op1)
		(term-in-const-form? op2)
		(term=? arg1 arg2)
		(t-deg-one? (term-to-t-deg arg1))
		(let ((name1 (const-to-name (term-in-const-form-to-const op1)))
		      (name2 (const-to-name (term-in-const-form-to-const op2))))
		  (or (and (string=? "PairOne" name1)
			   (string=? "PairTwo" name2))
		      (and (string=? "cLft" name1)
			   (string=? "cRht" name2)))))))
	    (term-in-app-form-to-arg prev-left)
	    (apply mk-term-in-app-form
		   (term-to-eta-nf-with-simplified-simrec-appterms op)
		   prev-args))))
	(else (apply mk-term-in-app-form
		     (term-to-eta-nf-with-simplified-simrec-appterms op)
		     prev-args)))))
    ((term-in-abst-form)
     (let* ((var (term-in-abst-form-to-var term))
	    (kernel (term-in-abst-form-to-kernel term))
	    (prev (term-to-eta-nf-with-simplified-simrec-appterms kernel)))
       (cond
	((and ;[x]rx -> r, if x not free in r
	  (term-in-app-form? prev)
	  (term=? (term-in-app-form-to-arg prev)
		  (make-term-in-var-form var))
	  (not (member var (term-to-free
			    (term-in-app-form-to-op prev)))))
	 (term-in-app-form-to-op prev))
	(else (make-term-in-abst-form var prev)))))
    ((term-in-pair-form)
     (let* ((left (term-in-pair-form-to-left term))
	    (right (term-in-pair-form-to-right term))
	    (prev-left (term-to-eta-nf-with-simplified-simrec-appterms left))
	    (prev-right
	     (term-to-eta-nf-with-simplified-simrec-appterms right)))
       (cond
	((and ;(left r)@(right r) -> r
	  (term-in-lcomp-form? prev-left)
	  (term-in-rcomp-form? prev-right)
	  (term=? (term-in-lcomp-form-to-kernel prev-left)
		  (term-in-rcomp-form-to-kernel prev-right)))
	 (term-in-lcomp-form-to-kernel prev-left))
	((and ;[if t [ys,zs]r1 ..]@[if t [ys,zs]r2 ..] -> [if t [ys,zs]r1@r2..]
	  (term-in-if-form? prev-left)
	  (term-in-if-form? prev-right)
	  (term=? (term-in-if-form-to-test prev-left)
		  (term-in-if-form-to-test prev-right)))
	 (let* ((test (term-in-if-form-to-test prev-left))
		(alg (term-to-type test))
		(alg-name (alg-form-to-name alg))
		(typed-constr-names (alg-name-to-typed-constr-names alg-name))
		(constr-types
		 (map typed-constr-name-to-type typed-constr-names))
		(ls (map (lambda (x) (length (arrow-form-to-arg-types x)))
			 constr-types))
		(alts1 (term-in-if-form-to-alts prev-left))
		(rest1 (term-in-if-form-to-rest prev-left))
		(exp-alts1 (map (lambda (alt l)
				  (term-to-simple-outer-eta-expansion
				   alt l))
				alts1 ls))
		(constr-arg-vars-list1
		 (map (lambda (alt l) (term-in-abst-form-to-vars alt l))
		      exp-alts1 ls))
		(kernels1
		 (map (lambda (alt l)
			(term-in-abst-form-to-final-kernel alt l))
		      exp-alts1 ls))
		(alts2 (term-in-if-form-to-alts prev-right))
		(rest2 (term-in-if-form-to-rest prev-right))
		(exp-alts2 (map (lambda (alt l)
				  (term-to-simple-outer-eta-expansion
				   alt l))
				alts2 ls))
		(constr-arg-vars-list2
		 (map (lambda (alt l) (term-in-abst-form-to-vars alt l))
		      exp-alts2 ls))
		(kernels2
		 (map (lambda (alt l)
			(term-in-abst-form-to-final-kernel alt l))
		      exp-alts2 ls))
		(equal-constr-arg-vars?-list
		 (map (lambda (vars1 vars2) (equal? vars1 vars2))
		      constr-arg-vars-list1 constr-arg-vars-list2))
		(constr-arg-vars-list
		 (map (lambda (boole vars1 vars2)
			(if boole vars1 (map var-to-new-var vars2)))
		      equal-constr-arg-vars?-list
		      constr-arg-vars-list1 constr-arg-vars-list2))
		(pair-alts
		 (map (lambda (boole vars vars2 kernel1 kernel2)
			(apply
			 mk-term-in-abst-form
			 (append
			  vars
			  (list (make-term-in-pair-form
				 kernel1
				 (if boole
				     kernel2
				     (term-substitute
				      kernel2
				      (map list
					   vars2
					   (map make-term-in-var-form
						vars)))))))))
		      equal-constr-arg-vars?-list
		      constr-arg-vars-list constr-arg-vars-list2
		      kernels1 kernels2))
		(pair-alts-nf
		 (map term-to-eta-nf-with-simplified-simrec-appterms
		      pair-alts)))
	   (make-term-in-if-form test pair-alts-nf (make-and rest1 rest2))))
	(else (make-term-in-pair-form prev-left prev-right)))))
    ((term-in-lcomp-form)
     (let ((prev (term-to-eta-nf-with-simplified-simrec-appterms
		  (term-in-lcomp-form-to-kernel term))))
       (if (term-in-pair-form? prev)
	   (term-in-pair-form-to-left prev)
	   (make-term-in-lcomp-form prev))))
    ((term-in-rcomp-form)
     (let ((prev (term-to-eta-nf-with-simplified-simrec-appterms
		  (term-in-rcomp-form-to-kernel term))))
       (if (term-in-pair-form? prev)
	   (term-in-pair-form-to-right prev)
	   (make-term-in-rcomp-form prev))))
    ((term-in-if-form)
     (let* ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term))
	    (rest (term-in-if-form-to-rest term))
	    (prev (term-to-eta-nf-with-simplified-simrec-appterms test))
	    (prevs (map term-to-eta-nf-with-simplified-simrec-appterms alts)))
       (apply make-term-in-if-form prev prevs rest)))
    (else term)))

(define (term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs term)
  (case (tag term)
    ((term-in-var-form) term)
    ((term-in-const-form)
     (let ((const (term-in-const-form-to-const term)))
       (if ;simplified simrec constant
	(and (string=? "Rec" (const-to-name const))
	     (let* ((uninst-type (const-to-uninst-type const))
		    (arg-types (arrow-form-to-arg-types uninst-type))
		    (step-types (cdr arg-types))
		    (alg-type (car arg-types))
		    (alg-name (alg-form-to-name alg-type))
		    (simalg-names (alg-name-to-simalg-names alg-name)))
	       (and (< 1 (length simalg-names))
		    (< (length step-types)
		       (length (apply append
				      (map alg-name-to-typed-constr-names
					   simalg-names)))))))
	(let* ((outer-eta-expansion (term-to-outer-eta-expansion term))
	       (kernel (term-in-abst-form-to-final-kernel outer-eta-expansion))
	       (vars (term-in-abst-form-to-vars outer-eta-expansion)))
	  (apply mk-term-in-abst-form
		 (append vars
			 (list (unfold-simplified-simrec-appterm kernel)))))
	term)))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (make-term-in-app-form
	(term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs op)
	(term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs arg))))
    ((term-in-abst-form)
     (let ((var (term-in-abst-form-to-var term))
	   (kernel (term-in-abst-form-to-kernel term)))
       (make-term-in-abst-form
	var (term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs
	     kernel))))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term)))
       (make-term-in-pair-form
	(term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs left)
	(term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs right))))
    ((term-in-lcomp-form)
     (make-term-in-lcomp-form
      (term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs
       (term-in-lcomp-form-to-kernel term))))
    ((term-in-rcomp-form)
     (make-term-in-rcomp-form
      (term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs
       (term-in-rcomp-form-to-kernel term))))
    ((term-in-if-form)
     (if-term-to-eta-expansion-and-unfolded-simrecs term))
    (else (myerror
	   "term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs"
	   "term expected"
	   term))))

(define (if-term-to-eta-expansion-and-unfolded-simrecs term)
  (let ((type (term-to-type term)))
    (case (tag type)
      ((arrow)
       (let* ((arg-types (arrow-form-to-arg-types type))
	      (arg-vars (map type-to-new-var arg-types))
	      (make-intro
	       (lambda (t) (apply mk-term-in-abst-form
				  (append arg-vars (list t)))))
	      (elim-args (map make-term-in-var-form arg-vars)))
	 (if-term-to-eta-expansion-and-unfolded-simrecs-aux
	  term make-intro elim-args)))
      ((star)
       (if-term-to-eta-expansion-and-unfolded-simrecs-aux
	term make-term-in-pair-form (list 'left) (list 'right)))
      (else term))))

;; if-term-to-eta-expansion-and-unfolded-simrecs-aux is a generic
;; helper function, which does eta-expansion in an if term over a
;; composite type (arrow or star), where the introduction term
;; constructor is make-intro and the arguments for elimination are
;; given in elim-args-list

(define (if-term-to-eta-expansion-and-unfolded-simrecs-aux
	 term make-intro . elim-args-list)
  (let* ((test (term-in-if-form-to-test term))
	 (alts (term-in-if-form-to-alts term))
	 (rest (term-in-if-form-to-rest term))
	 (prev-test
	  (term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs test))
	 (prev-alts
	  (map term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs
	       alts))
	 (alg (term-to-type test))
	 (alg-name (alg-form-to-name alg))
	 (typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (ls (map (lambda (x) (length (arrow-form-to-arg-types x)))
		  constr-types))
	 (constr-arg-types-list ;without arg-types
	  (map (lambda (l alt)
		 (arrow-form-to-arg-types (term-to-type alt) l))
	       ls alts))
	 (constr-arg-vars-list
	  (map (lambda (types) (map type-to-new-var types))
	       constr-arg-types-list))
	 (applied-alts-list
	  (map (lambda (elim-args)
		 (map (lambda (alt constr-arg-vars)
			(apply
			 mk-term-in-app-form
			 alt (append
			      (map make-term-in-var-form
				   (append constr-arg-vars))
			      elim-args)))
		      prev-alts constr-arg-vars-list))
	       elim-args-list))
	 (abstr-applied-alts-list
	  (map (lambda (applied-alts)
		 (map (lambda (constr-arg-vars applied-alt)
			(apply mk-term-in-abst-form
			       (append constr-arg-vars (list applied-alt))))
		      constr-arg-vars-list applied-alts))
	       applied-alts-list)))
    (apply make-intro
	   (map (lambda (abstr-applied-alt)
		  (if-term-to-eta-expansion-and-unfolded-simrecs
		   (make-term-in-if-form
		    prev-test abstr-applied-alt rest)))
		abstr-applied-alts-list))))

(define (nbe-normalize-term term)
  (let ((init (normalize-term-pi-with-rec-to-if
	       (nbe-normalize-term-without-eta
		(term-to-term-with-eta-expanded-if-terms-and-unfolded-simrecs
		 term)))))
    (do ((t init (normalize-term-pi-with-rec-to-if
		  (nbe-normalize-term-without-eta t))))
	((and (term-in-beta-normal-form? t) (term-in-if-normal-form? t))
	 ;; Change 2019-08-16: (term-in-if-normal-form? t) added
	 (term-to-eta-nf-with-simplified-simrec-appterms t)))))

(define nt nbe-normalize-term)

;; term-to-term-without-predecided-ifs simplifies all if-terms whose
;; branch is known because we are in a branch of an outer if-term with
;; the same test term.  tests is an alist assigning to a term of an
;; algebra type the number of a constructor it is assumed to be built
;; with.

(define (term-to-term-without-predecided-ifs term)
  (term-to-term-without-predecided-ifs-aux term '()))

(define (term-to-term-without-predecided-ifs-aux term tests)
  (case (tag term)
    ((term-in-var-form term-in-const-form) term)
    ((term-in-abst-form)
     (let ((var (term-in-abst-form-to-var term))
	   (kernel (term-in-abst-form-to-kernel term)))
       (make-term-in-abst-form
	var (term-to-term-without-predecided-ifs-aux
	     kernel
	     (list-transform-positive tests
	       (lambda (test)
		 (not (member var (term-to-free (car test))))))))))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (make-term-in-app-form
	(term-to-term-without-predecided-ifs-aux op tests)
	(term-to-term-without-predecided-ifs-aux arg tests))))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term)))
       (make-term-in-pair-form
	(term-to-term-without-predecided-ifs-aux left tests)
	(term-to-term-without-predecided-ifs-aux right tests))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (make-term-in-lcomp-form
	(term-to-term-without-predecided-ifs-aux kernel tests))))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-rcomp-form-to-kernel term)))
       (make-term-in-rcomp-form
	(term-to-term-without-predecided-ifs-aux kernel tests))))
    ((term-in-if-form)
     (let* ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term))
	    (rest (term-in-if-form-to-rest term))
	    (info (assoc test tests)))
       (if info
	   (term-to-term-without-predecided-ifs-aux
	    (list-ref alts (cadr info))
	    tests)
	   (apply
	    make-term-in-if-form
	    (append
	     (list (term-to-term-without-predecided-ifs-aux test tests)
		   (do ((l alts (cdr l))
			(i 0 (+ 1 i))
			(res '() (cons (term-to-term-without-predecided-ifs-aux
					(car l)
					(cons (list test i) tests))
				       res)))
		       ((null? l) (reverse res))))
	     rest)))))
    (else (myerror "term-to-term-without-predecided-ifs-aux"
		   "term expected" term))))

;; Alternative to nbe, if no rewrite rules are applicable.

(define (term-to-one-step-beta-reduct term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) term)
    ((term-in-abst-form)
     (make-term-in-abst-form
      (term-in-abst-form-to-var term)
      (term-to-one-step-beta-reduct (term-in-abst-form-to-kernel term))))
    ((term-in-app-form)
     (let* ((op (term-in-app-form-to-op term))
	    (arg (term-in-app-form-to-arg term)))
       (if (term-in-abst-form? op)
	   (term-subst (term-in-abst-form-to-kernel op)
		       (term-in-abst-form-to-var op)
		       arg)
	   (make-term-in-app-form
	    (term-to-one-step-beta-reduct op)
	    (term-to-one-step-beta-reduct arg)))))
    ((term-in-pair-form)
     (make-term-in-pair-form
      (term-to-one-step-beta-reduct (term-in-pair-form-to-left term))
      (term-to-one-step-beta-reduct (term-in-pair-form-to-right term))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (if (term-in-pair-form? kernel)
	   (term-in-pair-form-to-left kernel)
	   (make-term-in-lcomp-form
	    (term-to-one-step-beta-reduct kernel)))))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-rcomp-form-to-kernel term)))
       (if (term-in-pair-form? kernel)
	   (term-in-pair-form-to-right kernel)
	   (make-term-in-rcomp-form
	    (term-to-one-step-beta-reduct kernel)))))
    ((term-in-if-form)
     (let ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term)))
       (make-term-in-if-form
	(term-to-one-step-beta-reduct test)
	(map term-to-one-step-beta-reduct alts))))
    (else (myerror "term-to-one-step-beta-reduct" "unexpected term"
		   term))))

(define (term-in-beta-normal-form? term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) #t)
    ((term-in-abst-form)
     (let ((kernel (term-in-abst-form-to-kernel term)))
       (term-in-beta-normal-form? kernel)))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (and (not (term-in-abst-form? op))
	    (term-in-beta-normal-form? op)
	    (term-in-beta-normal-form? arg))))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term)))
       (and (term-in-beta-normal-form? left)
	    (term-in-beta-normal-form? right))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (and (not (term-in-pair-form? kernel))
	    (term-in-beta-normal-form? kernel))))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-rcomp-form-to-kernel term)))
       (and (not (term-in-pair-form? kernel))
	    (term-in-beta-normal-form? kernel))))
    ((term-in-if-form)
     (let ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term)))
       (and (term-in-beta-normal-form? test)
	    (apply and-op (map term-in-beta-normal-form? alts)))))
    (else (myerror "term-in-beta-normal-form?" "term tag expected"
		   (tag term)))))

(define (term-to-beta-nf term)
  (if (term-in-beta-normal-form? term)
      term
      (term-to-beta-nf (term-to-one-step-beta-reduct term))))

(define (term-to-beta-eta-nf term)
  (term-to-eta-nf (term-to-beta-nf term)))

(define (term-to-beta-pi-eta-nf term)
  (let ((init (normalize-term-pi-with-rec-to-if
	       (term-to-beta-nf
		(term-to-term-with-eta-expanded-if-terms term)))))
    (do ((t init (normalize-term-pi-with-rec-to-if
		  (term-to-beta-nf t))))
	((term-in-if-normal-form? t)
	 (term-to-eta-nf t)))))

(define bpe-nt term-to-beta-pi-eta-nf)

;; In term-in-rec-normal-form? we assume that term is not one of those
;; appearing during proof normalization.  This means that all recursion
;; constants are without repro data.

(define (term-in-rec-normal-form? term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) #t)
    ((term-in-abst-form)
     (let ((kernel (term-in-abst-form-to-kernel term)))
       (term-in-rec-normal-form? kernel)))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (and
	(term-in-rec-normal-form? op)
	(term-in-rec-normal-form? arg)
	(not (and
	      (term-in-const-form? op)
	      (equal? "Rec" (const-to-name
			     (term-in-const-form-to-const op)))
	      (let ((op1 (term-in-app-form-to-final-op arg))
		    (args1 (term-in-app-form-to-args arg)))
		(and (term-in-const-form? op1)
		     (eq? 'constr (const-to-kind
				   (term-in-const-form-to-const op1))))))))))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term)))
       (and (term-in-rec-normal-form? left)
	    (term-in-rec-normal-form? right))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (term-in-rec-normal-form? kernel)))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-rcomp-form-to-kernel term)))
       (term-in-rec-normal-form? kernel)))
    ((term-in-if-form)
     (let ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term)))
       (apply and-op (term-in-rec-normal-form? test)
	      (map term-in-rec-normal-form? alts))))
    (else (myerror "term-in-rec-normal-form?" "term tag expected"
		   (tag term)))))

(define (term-to-rec-nf term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) term)
    ((term-in-abst-form)
     (let ((var (term-in-abst-form-to-var term))
	   (kernel (term-in-abst-form-to-kernel term)))
       (make-term-in-abst-form
	var (term-to-rec-nf kernel))))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (if
	(and (term-in-const-form? op)
	     (equal? "Rec" (const-to-name
			    (term-in-const-form-to-const op)))
	     (let ((op1 (term-in-app-form-to-final-op arg))
		   (args1 (term-in-app-form-to-args arg)))
	       (and (term-in-const-form? op1)
		    (eq? 'constr (const-to-kind
				  (term-in-const-form-to-const op1))))))
	(nbe-normalize-term-without-eta term)
	(make-term-in-app-form
	 (term-to-rec-nf op)
	 (term-to-rec-nf arg)))))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term)))
       (make-term-in-pair-form
	(term-to-rec-nf left)
	(term-to-rec-nf right))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (make-term-in-lcomp-form (term-to-rec-nf kernel))))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-rcomp-form-to-kernel term)))
       (make-term-in-rcomp-form (term-to-rec-nf kernel))))
    ((term-in-if-form)
     (let ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term)))
       (make-term-in-if-form (term-to-rec-nf test)
			     (map term-to-rec-nf alts))))
    (else (myerror "term-to-rec-nf" "term tag expected"
		   (tag term)))))

(define (term-to-length term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) 1)
    ((term-in-abst-form)
     (+ 1 (term-to-length (term-in-abst-form-to-kernel term))))
    ((term-in-app-form)
     (let* ((op (term-in-app-form-to-op term))
	    (arg (term-in-app-form-to-arg term)))
       (+ 1 (term-to-length op) (term-to-length arg))))
    ((term-in-pair-form)
     (+ 1
	(term-to-length (term-in-pair-form-to-left term))
	(term-to-length (term-in-pair-form-to-right term))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (+ 1 (term-to-length kernel))))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-rcomp-form-to-kernel term)))
       (+ 1 (term-to-length kernel))))
    ((term-in-if-form)
     (let ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term)))
       (+ 1 (term-to-length test)
	  (apply + (map term-to-length alts)))))
    (else (myerror "term-to-length" "unexpected term, tag:"
		   (tag term)))))

(define (term-to-consts-with-repetitions term)
  (case (tag term)
    ((term-in-var-form) '())
    ((term-in-const-form) (list (term-in-const-form-to-const term)))
    ((term-in-app-form)
     (let ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term)))
       (append (term-to-consts-with-repetitions op)
	       (term-to-consts-with-repetitions arg))))
    ((term-in-abst-form)
     (let ((kernel (term-in-abst-form-to-kernel term)))
       (term-to-consts-with-repetitions kernel)))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term)))
       (append (term-to-consts-with-repetitions left)
	       (term-to-consts-with-repetitions right))))
    ((term-in-lcomp-form)
     (let ((kernel (term-in-lcomp-form-to-kernel term)))
       (term-to-consts-with-repetitions kernel)))
    ((term-in-rcomp-form)
     (let ((kernel (term-in-rcomp-form-to-kernel term)))
       (term-to-consts-with-repetitions kernel)))
    ((term-in-if-form)
     (let ((test (term-in-if-form-to-test term))
	   (alts (term-in-if-form-to-alts term)))
       (apply append (map term-to-consts-with-repetitions (cons test alts)))))
    (else (myerror "term-to-consts-with-repetitions" "term tag expected"
		   (tag term)))))

(define (term-to-consts term)
  (remove-duplicates-wrt const=? (term-to-consts-with-repetitions term)))

;; For tests it might generally be useful to have a level-wise
;; decomposition of terms into subterms: one level transforms a term
;; N@lambda us.v Ms into the list [N v M1 ... Mn]

(define (term-in-intro-form-to-final-kernels term)
  (cond
   ((term-in-abst-form? term)
    (term-in-intro-form-to-final-kernels
     (term-in-abst-form-to-kernel term)))
   ((term-in-pair-form? term)
    (append (term-in-intro-form-to-final-kernels
	     (term-in-pair-form-to-left term))
	    (term-in-intro-form-to-final-kernels
	     (term-in-pair-form-to-right term))))
   (else (list term))))

(define (term-in-elim-form-to-final-op-and-args term)
  (case (tag term)
    ((term-in-app-form)
     (append (term-in-elim-form-to-final-op-and-args
	      (term-in-app-form-to-op term))
	     (list (term-in-app-form-to-arg term))))
    ((term-in-lcomp-form)
     (append (term-in-elim-form-to-final-op-and-args
	      (term-in-lcomp-form-to-kernel term))
	     (list 'left)))
    ((term-in-rcomp-form)
     (append (term-in-elim-form-to-final-op-and-args
	      (term-in-rcomp-form-to-kernel term))
	     (list 'right)))
    (else (list term))))

(define (term-in-app-form-to-final-op-and-args term)
  (do ((x term (term-in-app-form-to-op x))
       (res '() (cons (term-in-app-form-to-op x)
		      (cons (term-in-app-form-to-arg x)
			    (if (null? res) '() (cdr res))))))
      ((not (term-in-app-form? x)) res)))

(define (term-to-parts-of-level-one term)
  (if
   (term-in-if-form? term)
   (cons (term-in-if-form-to-test term)
	 (term-in-if-form-to-alts term))
   (let* ((final-kernels (term-in-intro-form-to-final-kernels term))
	  (lists (map term-in-elim-form-to-final-op-and-args final-kernels)))
     (apply append lists))))

(define (term-to-subterms term . opt-level)
  (if
   (null? opt-level)
   (term-to-subterms term 1)
   (let ((l (car opt-level)))
     (if (and (integer? l) (not (negative? l)))
	 (if (zero? l)
	     (list term)
	     (let* ((parts (term-to-parts-of-level-one term))
		    (terms (list-transform-positive parts term-form?)))
	       (apply append (map (lambda (x) (term-to-subterms x (- l 1)))
				  terms))))
	 (myerror "term-to-subterms" "non-negative integer expected" l)))))

;; term-to-term-with-let hand optimizes a term by searching for its
;; longest duplicate subterm, and taking that subterm out via a let.

(define (term-to-let-candidates term)
  (let ((terms
	 (case (tag term)
	   ((term-in-var-form term-in-const-form) '())
	   ((term-in-abst-form)
	    (let* ((var (term-in-abst-form-to-var term))
		   (kernel (term-in-abst-form-to-kernel term))
		   (prev (term-to-let-candidates kernel)))
	      (list-transform-positive prev
		(lambda (s) (not (member var (term-to-free s)))))))
	   ((term-in-app-form)
	    (let ((prev1 (term-to-let-candidates
			  (term-in-app-form-to-op term)))
		  (prev2 (term-to-let-candidates
			  (term-in-app-form-to-arg term))))
	      (append prev1 prev2)))
	   ((term-in-pair-form)
	    (append (term-to-let-candidates
		     (term-in-pair-form-to-left term))
		    (term-to-let-candidates
		     (term-in-pair-form-to-right term))))
	   ((term-in-lcomp-form)
	    (term-to-let-candidates (term-in-lcomp-form-to-kernel term)))
	   ((term-in-rcomp-form)
	    (term-to-let-candidates (term-in-rcomp-form-to-kernel term)))
	   ((term-in-if-form)
	    (apply append (map term-to-let-candidates
			       (cons (term-in-if-form-to-test term)
				     (term-in-if-form-to-alts term)))))
	   (else (myerror "term-to-let-candidates" "term expected" term)))))
    (if (or (term-in-var-form? term)
	    (and (null? (term-to-free term))
		 (term=? (nt term) term))
	    (member-wrt term=? term terms))
	terms
	(cons term terms))))

(define (term-to-term-with-let term)
  (if (term-in-abst-form? term)
      (let* ((vars (term-in-abst-form-to-vars term))
	     (kernel (term-in-abst-form-to-final-kernel term))
	     (prev (term-to-term-with-let kernel)))
	(apply mk-term-in-abst-form (append vars (list prev))))
      (let* ((let-candidates (term-to-let-candidates term))
	     (longest-duplicate
	      (if (pair? let-candidates)
		  (apply terms-to-longest-duplicate let-candidates)
		  #f)))
	(if longest-duplicate
	    (let* ((type (term-to-type longest-duplicate))
		   (var (type-to-new-var type))
		   (pattern
		    (term-gen-subst
		     term longest-duplicate (make-term-in-var-form var)))
		   (cId-const (pconst-name-to-pconst "cId"))
		   (cId-term
		    (make-term-in-const-form
		     (let* ((tvars (const-to-tvars cId-const))
			    (subst (make-substitution
				    tvars (list (make-arrow
						 type
						 (term-to-type term))))))
		       (const-substitute cId-const subst #f)))))
	      (mk-term-in-app-form ;let via cId
	       cId-term
	       (make-term-in-abst-form
		var (term-to-term-with-let-aux pattern))
	       longest-duplicate))
	    (term-to-term-with-let-aux term)))))

;; (pp (term-to-term-with-let (pt "(([m]n+m)7)*(([m]n+m)7)")))

(define (term-to-term-with-let-aux term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) term)
    ((term-in-abst-form)
     (term-to-term-with-let term))
    ((term-in-app-form)
     (make-term-in-app-form
      (term-to-term-with-let-aux (term-in-app-form-to-op term))
      (term-to-term-with-let-aux (term-in-app-form-to-arg term))))
    ((term-in-pair-form)
     (make-term-in-pair-form
      (term-to-term-with-let-aux (term-in-pair-form-to-left term))
      (term-to-term-with-let-aux (term-in-pair-form-to-right term))))
    ((term-in-lcomp-form)
     (make-term-in-lcomp-form
      (term-to-term-with-let-aux (term-in-lcomp-form-to-kernel term))))
    ((term-in-rcomp-form)
     (make-term-in-rcomp-form
      (term-to-term-with-let-aux (term-in-rcomp-form-to-kernel term))))
    ((term-in-if-form)
     (make-term-in-if-form
      (term-to-term-with-let-aux (term-in-if-form-to-test term))
      (map term-to-term-with-let-aux (term-in-if-form-to-alts term))))
    (else (myerror "term-to-term-with-let-aux" "term expected" term))))

(define (terms-to-longest-duplicate term . terms)
  (if (null? terms)
      #f
      (let ((prev (apply terms-to-longest-duplicate terms)))
	(if (member-wrt term=? term terms)
	    (if prev
		(if (> (term-to-length term) (term-to-length prev))
		    term
		    prev)
		term)
	    prev))))

;; (pp (terms-to-longest-duplicate (pt "n") (pt "n+m")  (pt "n+m")))

(define (term-to-depth term)
  (case (tag term)
    ((term-in-var-form term-in-const-form) 0)
    ((term-in-if-form)
     (+ 1 (apply max (term-to-depth (term-in-if-form-to-test term))
		 (term-to-depth (term-in-if-form-to-alts term)))))
    (else (+ 1 (apply max (map term-to-depth (term-to-subterms term 1)))))))

(define (max-index varlist)
  (do ((l varlist (cdr l))
       (res -1 (max res (let ((x (car l)))
			  (case (tag x)
			    ((var) (var-to-index x))
			    ((avar) (avar-to-index x))
			    (else (myerror "max-index" "var or avar expected"
					   x)))))))
      ((null? l) res)))

;; 6-6. Check
;; ==========

;; check-term is a test function for terms.  If the argument is not a
;; term, an error is returned.

(define (check-term x)
  (if (not (pair? x)) (myerror "check-term" "term expected"))
  (cond
   ((term-in-var-form? x)
    (let ((var (term-in-var-form-to-var x)))
      (if (not (var? var))
	  (myerror "check term" "variable expected" var))
      (if (not (equal? (term-to-type x) (var-to-type var)))
	  (myerror "check-term" "equal types expected"
		   (term-to-type x) (var-to-type var))))
    #t)
   ((term-in-const-form? x)
    (let ((const (term-in-const-form-to-const x)))
      (if (not (const? const))
	  (myerror "check-term" "constant expected" const))
      (if (not (equal? (term-to-type x) (const-to-type const)))
	  (myerror "check-term" "equal types expected"
		   (term-to-type x) (const-to-type const))))
    #t)
   ((term-in-abst-form? x)
    (let ((var (term-in-abst-form-to-var x))
	  (kernel (term-in-abst-form-to-kernel x)))
      (if (not (var? var))
	  (myerror "check-term" "variable expected" var))
      (check-term kernel)
      (let ((var-type (var-to-type var))
	    (kernel-type (term-to-type kernel)))
	(if (not (equal? (make-arrow var-type kernel-type)
			 (term-to-type x)))
	    (myerror "check-term" "equal types expected"
		     (make-arrow var-type kernel-type)
		     (term-to-type x)))))
    #t)
   ((term-in-app-form? x)
    (let ((op (term-in-app-form-to-op x))
	  (arg (term-in-app-form-to-arg x)))
      (check-term op)
      (check-term arg)
      (let ((op-type (term-to-type op))
	    (arg-type (term-to-type arg)))
	(if (not (arrow-form? op-type))
	    (myerror "check-term" "arrow type expected" op-type))
	(if (not (equal? (arrow-form-to-arg-type op-type) arg-type))
	    (myerror "check-term" "equal types expected"
		     (arrow-form-to-arg-type op-type)
		     arg-type))
	(if (not (equal? (term-to-type x)
			 (arrow-form-to-val-type op-type)))
	    (myerror "check-term" "equal types expected"
		     (term-to-type x)
		     (arrow-form-to-val-type op-type)))))
    #t)
   ((term-in-pair-form? x)
    (let ((left (term-in-pair-form-to-left x))
	  (right (term-in-pair-form-to-right x)))
      (check-term left)
      (check-term right)
      (let ((left-type (term-to-type left))
	    (right-type (term-to-type right)))
	(if (not (equal? (term-to-type x)
			 (make-star left-type right-type)))
	    (myerror "check-term" "equal types expected"
		     (term-to-type x)
		     (make-star left-type right-type)))))
    #t)
   ((term-in-lcomp-form? x)
    (let ((kernel (term-in-lcomp-form-to-kernel x)))
      (check-term kernel)
      (let ((kernel-type (term-to-type kernel)))
	(if (not (star-form? kernel-type))
	    (myerror "check-term" "star form expected" kernel-type))
	(if (not (equal? (term-to-type x)
			 (star-form-to-left-type kernel-type)))
	    (myerror "check-term" "equal types expected"
		     (term-to-type x)
		     (star-form-to-left-type kernel-type)))))
    #t)
   ((term-in-rcomp-form? x)
    (let ((kernel (term-in-rcomp-form-to-kernel x)))
      (check-term kernel)
      (let ((kernel-type (term-to-type kernel)))
	(if (not (star-form? kernel-type))
	    (myerror "check-term" "star form expected" kernel-type))
	(if (not (equal? (term-to-type x)
			 (star-form-to-right-type kernel-type)))
	    (myerror "check-term" "equal types expected"
		     (term-to-type x)
		     (star-form-to-right-type kernel-type)))))
    #t)
   ((term-in-if-form? x)
    (let ((test (term-in-if-form-to-test x))
	  (alts (term-in-if-form-to-alts x))
	  (rest (term-in-if-form-to-rest x)))
      (check-term test)
      (map check-term alts)
      (let ((test-type (term-to-type test)))
	(if (not (alg-form? test-type))
	    (myerror "check-term" "algebra form expected" test-type))
	(let* ((alg-name (alg-form-to-name test-type))
	       (typed-constr-names (alg-name-to-typed-constr-names alg-name))
	       (constr-types (map typed-constr-name-to-type typed-constr-names))
	       (types (alg-form-to-types test-type))
	       (tvars (alg-name-to-tvars alg-name))
	       (tsubst (map list tvars types))
	       (tsubst-constr-types
		(map (lambda (x) (type-substitute x tsubst)) constr-types))
	       (tsubst-constr-argtypes-list
		(map (lambda (tsubst-constr-type)
		       (arrow-form-to-arg-types tsubst-constr-type))
		     tsubst-constr-types))
	       (alt-types (map term-to-type alts))
	       (val-type (term-to-type x))
	       (expected-alt-types (map (lambda (tsubst-constr-argtypes)
					  (apply mk-arrow
						 (append tsubst-constr-argtypes
							 (list val-type))))
					tsubst-constr-argtypes-list)))
	  (if (not (equal? alt-types expected-alt-types))
	      (apply myerror "check-term" "equal types expected" "alt-types:"
		     (append alt-types (list "and expected-alt-types:")
			     expected-alt-types)))
	  #t))))
   (else (myerror "check-term" "term expected" x))))

;; Code discarded 2020-07-10
;; (define (check-term x . excluded-vars)
;;   (if (not (pair? x)) (myerror "check-term" "term expected"))
;;   (cond
;;    ((term-in-var-form? x)
;;     (if (member (term-in-var-form-to-var x) excluded-vars) #t
;; 	(let ((var (term-in-var-form-to-var x)))
;; 	  (if (not (var? var))
;; 	      (myerror "check term" "variable expected" var))
;; 	  (if (t-deg-one? (var-to-t-deg var))
;; 	      (check-restricted-var var))
;; 	  (if (not (equal? (term-to-type x) (var-to-type var)))
;; 	      (myerror "check-term" "equal types expected"
;; 		       (term-to-type x) (var-to-type var)))
;; 	  #t)))
;;    ((term-in-const-form? x)
;;     (let ((const (term-in-const-form-to-const x)))
;;       (if (not (const? const))
;; 	  (myerror "check-term" "constant expected" const))
;;       (if (not (equal? (term-to-type x) (const-to-type const)))
;; 	  (myerror "check-term" "equal types expected"
;; 		   (term-to-type x) (const-to-type const))))
;;     #t)
;;    ((term-in-abst-form? x)
;;     (let ((var (term-in-abst-form-to-var x))
;; 	  (kernel (term-in-abst-form-to-kernel x)))
;;       (if (not (var? var))
;; 	  (myerror "check-term" "variable expected" var))
;;       (if (t-deg-zero? (var-to-t-deg var))
;; 	  (apply check-term kernel excluded-vars)
;; 	  (let* ((new-var (var-to-new-partial-var var))
;; 		 (new-kernel (term-subst
;; 			      kernel var (make-term-in-var-form new-var))))
;; 	    (apply check-term new-kernel new-var excluded-vars)))
;;       (let ((var-type (var-to-type var))
;; 	    (kernel-type (term-to-type kernel)))
;; 	(if (not (equal? (make-arrow var-type kernel-type)
;; 			 (term-to-type x)))
;; 	    (myerror "check-term" "equal types expected"
;; 		     (make-arrow var-type kernel-type)
;; 		     (term-to-type x))))
;;       #t))
;;    ((term-in-app-form? x)
;;     (let ((op (term-in-app-form-to-op x))
;; 	  (arg (term-in-app-form-to-arg x)))
;;       (apply check-term op excluded-vars)
;;       (apply check-term arg excluded-vars)
;;       (let ((op-type (term-to-type op))
;; 	    (arg-type (term-to-type arg)))
;; 	(if (not (arrow-form? op-type))
;; 	    (myerror "check-term" "arrow type expected" op-type))
;; 	(if (not (equal? (arrow-form-to-arg-type op-type) arg-type))
;; 	    (myerror "check-term" "equal types expected"
;; 		     (arrow-form-to-arg-type op-type)
;; 		     arg-type))
;; 	(if (not (equal? (term-to-type x)
;; 			 (arrow-form-to-val-type op-type)))
;; 	    (myerror "check-term" "equal types expected"
;; 		     (term-to-type x)
;; 		     (arrow-form-to-val-type op-type)))))
;;     #t)
;;    ((term-in-pair-form? x)
;;     (let ((left (term-in-pair-form-to-left x))
;; 	  (right (term-in-pair-form-to-right x)))
;;       (apply check-term left excluded-vars)
;;       (apply check-term right excluded-vars)
;;       (let ((left-type (term-to-type left))
;; 	    (right-type (term-to-type right)))
;; 	(if (not (equal? (term-to-type x)
;; 			 (make-star left-type right-type)))
;; 	    (myerror "check-term" "equal types expected"
;; 		     (term-to-type x)
;; 		     (make-star left-type right-type))))
;;       #t))
;;    ((term-in-lcomp-form? x)
;;     (let ((kernel (term-in-lcomp-form-to-kernel x)))
;;       (apply check-term kernel excluded-vars)
;;       (let ((kernel-type (term-to-type kernel)))
;; 	(if (not (star-form? kernel-type))
;; 	    (myerror "check-term" "star form expected" kernel-type))
;; 	(if (not (equal? (term-to-type x)
;; 			 (star-form-to-left-type kernel-type)))
;; 	    (myerror "check-term" "equal types expected"
;; 		     (term-to-type x)
;; 		     (star-form-to-left-type kernel-type)))))
;;     #t)
;;    ((term-in-rcomp-form? x)
;;     (let ((kernel (term-in-rcomp-form-to-kernel x)))
;;       (apply check-term kernel excluded-vars)
;;       (let ((kernel-type (term-to-type kernel)))
;; 	(if (not (star-form? kernel-type))
;; 	    (myerror "check-term" "star form expected" kernel-type))
;; 	(if (not (equal? (term-to-type x)
;; 			 (star-form-to-right-type kernel-type)))
;; 	    (myerror "check-term" "equal types expected"
;; 		     (term-to-type x)
;; 		     (star-form-to-right-type kernel-type)))))
;;     #t)
;;    ((term-in-if-form? x)
;;     (let ((test (term-in-if-form-to-test x))
;; 	  (alts (term-in-if-form-to-alts x))
;; 	  (rest (term-in-if-form-to-rest x)))
;;       (apply check-term test excluded-vars)
;;       (map (lambda (x) (apply check-term x excluded-vars)) alts)
;;       (let ((test-type (term-to-type test)))
;; 	(if (not (alg-form? test-type))
;; 	    (myerror "check-term" "algebra form expected" test-type))
;; 	(let* ((alg-name (alg-form-to-name test-type))
;; 	       (typed-constr-names (alg-name-to-typed-constr-names alg-name))
;; 	       (constr-types (map typed-constr-name-to-type typed-constr-names))
;; 	       (types (alg-form-to-types test-type))
;; 	       (tvars (alg-name-to-tvars alg-name))
;; 	       (tsubst (map list tvars types))
;; 	       (tsubst-constr-types
;; 		(map (lambda (x) (type-substitute x tsubst)) constr-types))
;; 	       (tsubst-constr-argtypes-list
;; 		(map (lambda (tsubst-constr-type)
;; 		       (arrow-form-to-arg-types tsubst-constr-type))
;; 		     tsubst-constr-types))
;; 	       (alt-types (map term-to-type alts))
;; 	       (val-type (term-to-type x))
;; 	       (expected-alt-types (map (lambda (tsubst-constr-argtypes)
;; 					  (apply mk-arrow
;; 						 (append tsubst-constr-argtypes
;; 							 (list val-type))))
;; 					tsubst-constr-argtypes-list)))
;; 	  (if (not (equal? alt-types expected-alt-types))
;; 	      (apply myerror "check-term" "equal types expected" "alt-types:"
;; 		     (append alt-types (list "and expected-alt-types:")
;; 			     expected-alt-types)))
;; 	  #t))))
;;    (else (myerror "check-term" "term expected" x))))

;; term? is a complete test for terms.  Returns true or false.

(define (term? x)
  (if
   (not (pair? x))
   #f
   (cond
    ((term-in-var-form? x)
     (let ((var (term-in-var-form-to-var x)))
       (and (var? var)
	    (equal? (term-to-type x) (var-to-type var)))))
    ((term-in-const-form? x)
     (let ((const (term-in-const-form-to-const x)))
       (and (const? const)
	    (equal? (term-to-type x) (const-to-type const)))))
    ((term-in-abst-form? x)
     (let ((var (term-in-abst-form-to-var x))
	   (kernel (term-in-abst-form-to-kernel x)))
       (and (var? var)
	    (term? kernel)
	    (let ((var-type (var-to-type var))
		  (kernel-type (term-to-type kernel)))
	      (equal? (make-arrow var-type kernel-type)
		      (term-to-type x))))))
    ((term-in-app-form? x)
     (let ((op (term-in-app-form-to-op x))
	   (arg (term-in-app-form-to-arg x)))
       (and (term? op)
	    (term? arg)
	    (let ((op-type (term-to-type op))
		  (arg-type (term-to-type arg)))
	      (and (arrow-form? op-type)
		   (equal? (arrow-form-to-arg-type op-type)
			   arg-type)
		   (equal? (term-to-type x)
			   (arrow-form-to-val-type op-type)))))))
    ((term-in-pair-form? x)
     (let ((left (term-in-pair-form-to-left x))
	   (right (term-in-pair-form-to-right x)))
       (and (term? left)
	    (term? right)
	    (let ((left-type (term-to-type left))
		  (right-type (term-to-type right)))
	      (equal? (term-to-type x)
		      (make-star left-type right-type))))))
    ((term-in-lcomp-form? x)
     (let ((kernel (term-in-lcomp-form-to-kernel x)))
       (and (term? kernel)
	    (let ((kernel-type (term-to-type kernel)))
	      (and (star-form? kernel-type)
		   (equal? (term-to-type x)
			   (star-form-to-left-type kernel-type)))))))
    ((term-in-rcomp-form? x)
     (let ((kernel (term-in-rcomp-form-to-kernel x)))
       (and (term? kernel)
	    (let ((kernel-type (term-to-type kernel)))
	      (and (star-form? kernel-type)
		   (equal? (term-to-type x)
			   (star-form-to-right-type kernel-type)))))))
    ((term-in-if-form? x)
     (let ((test (term-in-if-form-to-test x))
	   (alts (term-in-if-form-to-alts x))
	   (rest (term-in-if-form-to-rest x)))
       (and (term? test)
	    (map term? alts)
	    (let ((test-type (term-to-type test))
		  (alts-types (map term-to-type alts)))
	      (and (alg-form? test-type)
		   (let* ((alg-name (alg-form-to-name test-type))
			  (typed-constr-names
			   (alg-name-to-typed-constr-names alg-name))
			  (constr-types
			   (map typed-constr-name-to-type
				typed-constr-names))
			  (lengths-of-arg-types
			   (map (lambda (x)
				  (length (arrow-form-to-arg-types x)))
				constr-types))
			  (types (map (lambda (alt l)
					(arrow-form-to-final-val-type
					 (term-to-type alt) l))
				      alts lengths-of-arg-types)))
		     (and (apply and-op (map (lambda (x)
					       (equal? x (car types)))
					     types))
			  (equal? (term-to-type x) (car types)))))))))
    (else #f))))

(define ct check-term)

;; 6-7. Substitution
;; =================

;; We define simultaneous substitution for type and object variables in
;; a term.  It is allowed that the substitution affects varisbles whose
;; type is changed by the substitution.  The substitution must be
;; admissible for the free variables in the term.

(define (var-term-equal? var term)
  (and (term-in-var-form? term)
       (equal? var (term-in-var-form-to-var term))))

(define (term-subst term arg val)
  (let ((equality?
	 (cond
	  ((and (tvar? arg) (type? val)) equal?)
	  ((and (var-form? arg) (term-form? val)) var-term-equal?)
	  (else (myerror "term-subst" "unexpected arg" arg "and val" val)))))
    (term-substitute term (make-subst-wrt equality? arg val))))

(define (term-substitute term tosubst)
  (let ((tsubst (list-transform-positive tosubst
		  (lambda (x) (tvar-form? (car x))))))
    (case (tag term)
      ((term-in-var-form)
       (let* ((var (term-in-var-form-to-var term))
	      (info (assoc var tosubst)))
	 (if info
	     (cadr info)
	     (make-term-in-var-form var))))
      ((term-in-const-form)
       (make-term-in-const-form
	(const-substitute (term-in-const-form-to-const term) tsubst #t)))
      ((term-in-abst-form)
       (let* ((var (term-in-abst-form-to-var term))
	      (kernel (term-in-abst-form-to-kernel term))
	      (type (var-to-type var))
	      (tovars (map car tosubst))
	      (active-vars (intersection tovars (term-to-free term)))
	      (active-subst (list-transform-positive tosubst
			      (lambda (x) (member (car x) active-vars))))
	      (active-terms (map cadr active-subst))
	      (new-var
	       (if ;type is not changed
		(null? (intersection (type-to-tvars type) (map car tsubst)))
		(if ;there is no clash
		 (not (member var (apply union
					 (map term-to-free active-terms))))
		 var
		 (var-to-new-var var))
		(type-to-new-var (type-substitute type tsubst))))
	      (new-subst (if (equal? var new-var)
			     active-subst
			     (cons (list var (make-term-in-var-form new-var))
				   active-subst))))
	 (make-term-in-abst-form
	  new-var (term-substitute kernel (append tsubst new-subst)))))
      ((term-in-app-form)
       (make-term-in-app-form
	(term-substitute (term-in-app-form-to-op term) tosubst)
	(term-substitute (term-in-app-form-to-arg term) tosubst)))
      ((term-in-pair-form)
       (make-term-in-pair-form
	(term-substitute (term-in-pair-form-to-left term) tosubst)
	(term-substitute (term-in-pair-form-to-right term) tosubst)))
      ((term-in-lcomp-form)
       (make-term-in-lcomp-form
	(term-substitute (term-in-lcomp-form-to-kernel term) tosubst)))
      ((term-in-rcomp-form)
       (make-term-in-rcomp-form
	(term-substitute (term-in-rcomp-form-to-kernel term) tosubst)))
      ((term-in-if-form)
       (apply
	make-term-in-if-form
	(term-substitute (term-in-if-form-to-test term) tosubst)
	(map (lambda (x) (term-substitute x tosubst))
	     (term-in-if-form-to-alts term))
	(term-in-if-form-to-rest term)))
      (else (myerror "term-substitute" "term expected" term)))))

;; Display functions for substitutions:

(define (display-substitution subst)
  (display-comment "Substitution:") (newline)
  (for-each (lambda (x)
	      (let* ((var (car x))
		     (term (cadr x)))
		(if (var? var)
		    (begin (display-comment)
			   (display (var-to-string var)))
		    (myerror "display-substitution" "variable expected" var))
		(display tab)
		(display "->")
		(display tab)
		(if (term-form? term)
		    (display (term-to-string term))
		    (myerror "display-substitution" "term expected" term))
		(newline)))
	    subst))

;; (term-gen-substitute term gen-subst) substitutes simultaneously the
;; left hand sides of the alist gen-subst at all occurrences in term with
;; no free variables captured by the corresponding right hand sides.
;; gen-subst is an alist associating terms to terms.  Renaming takes
;; place if and only if a free variable would become bound.

(define (term-gen-substitute term gen-subst)
  (car (term-gen-substitute-and-newfreeoccs term gen-subst)))

(define (term-gen-substitute-and-newfreeoccs term gen-subst)
  (let ((info (assoc-wrt term=? term gen-subst)))
    (cond
     ((null? gen-subst) (list term '()))
     (info (list (cadr info) (term-to-free (cadr info))))
     (else
      (case (tag term)
	((term-in-const-form) (list term '()))
	((term-in-abst-form)
	 (let* ((var (term-in-abst-form-to-var term))
		(kernel (term-in-abst-form-to-kernel term))
                ;substitute only those lhss without var
		(new-subst (do ((s gen-subst (cdr s))
				(res '() (if (member var
						     (term-to-free (caar s)))
					     res
					     (cons (car s) res))))
			       ((null? s) (reverse res))))
		(pair (term-gen-substitute-and-newfreeoccs kernel new-subst))
		(new-kernel (car pair))
		(new-free-occs (cadr pair)))
	   (if (member var new-free-occs)
	       (let* ((new-var (var-to-new-var var))
		      (pair1 (term-gen-substitute-and-newfreeoccs
			      kernel
			      (cons (list var new-var) new-subst)))
		      (new-kernel1 (car pair1))
		      (new-free-occs1 (cadr pair1)))
		 (list (make-term-in-abst-form new-var new-kernel1)
		       (remove new-var new-free-occs1)))
	       (list (make-term-in-abst-form var new-kernel)
		     new-free-occs))))
	((term-in-app-form)
	 (let* ((pair1 (term-gen-substitute-and-newfreeoccs
			(term-in-app-form-to-op term) gen-subst))
		(pair2 (term-gen-substitute-and-newfreeoccs
			(term-in-app-form-to-arg term) gen-subst))
		(new-op (car pair1))
		(new-arg (car pair2))
		(new-free-occs (union (cadr pair1) (cadr pair2))))
	   (list (make-term-in-app-form new-op new-arg) new-free-occs)))
	((term-in-pair-form)
	 (let* ((pair1 (term-gen-substitute-and-newfreeoccs
			(term-in-pair-form-to-left term) gen-subst))
		(pair2 (term-gen-substitute-and-newfreeoccs
			(term-in-pair-form-to-right term) gen-subst))
		(new-left (car pair1))
		(new-right (car pair2))
		(new-free-occs (union (cadr pair1) (cadr pair2))))
	   (list (make-term-in-pair-form new-left new-right) new-free-occs)))
	((term-in-lcomp-form)
	 (let* ((pair (term-gen-substitute-and-newfreeoccs
		       (term-in-lcomp-form-to-kernel term) gen-subst))
		(new-kernel (car pair))
		(new-free-occs (cadr pair)))
	   (list (make-term-in-lcomp-form new-kernel) new-free-occs)))
	((term-in-rcomp-form)
	 (let* ((pair (term-gen-substitute-and-newfreeoccs
		       (term-in-rcomp-form-to-kernel term) gen-subst))
		(new-kernel (car pair))
		(new-free-occs (cadr pair)))
	   (list (make-term-in-rcomp-form new-kernel) new-free-occs)))
	((term-in-if-form)
	 (let* ((pair (term-gen-substitute-and-newfreeoccs
		       (term-in-if-form-to-test term) gen-subst))
		(pairs
		 (map (lambda (x)
			(term-gen-substitute-and-newfreeoccs x gen-subst))
		      (term-in-if-form-to-alts term)))
		(new-test (car pair))
		(new-alts (map car pairs))
		(new-free-occs
		 (union (cadr pair) (apply union (map cadr pairs)))))
	   (list (apply make-term-in-if-form
			new-test
			new-alts
			(term-in-if-form-to-rest term))
		 new-free-occs)))
	(else (list term '())))))))

(define (term-gen-subst term term1 term2)
  (term-gen-substitute term (list (list term1 term2))))

;; (term-to-term-with-partial-vars term) changes all total vars free
;; in term into partial vars.

(define (term-to-term-with-partial-vars term)
  (let* ((vars (term-to-free term))
	 (total-vars (list-transform-positive vars
		       (lambda (var) (t-deg-one? (var-to-t-deg var)))))
	 (partial-vars (map (lambda (var)
			      (make-var (var-to-type var)
					(var-to-index var)
					t-deg-zero
					(var-to-name var)))
			    total-vars))
	 (subst (make-substitution
		 total-vars (map make-term-in-var-form partial-vars))))
    (term-substitute term subst)))

;; term-and-var-and-subterm-to-first-decomp-or-f added.  It returns
;; the first term t(var) such that term is t(subterm), and #f if this
;; is impossible.

(define (term-and-var-and-subterm-to-first-decomp-or-f term var subterm)
  (if (not (equal? (term-to-type subterm) (var-to-type var)))
      (myerror "term-and-var-and-subterm-to-first-decomp-or-f"
	       "subterm" subterm "of type" (term-to-type subterm)
	       "should have the same type as variable" var "of type"
	       (var-to-type var)))
  (cond
   ((term=? term subterm) (make-term-in-var-form var))
   ((term-in-const-form? term) #f)
   ((term-in-var-form? term) #f)
   ((term-in-abst-form? term)
    (let ((var1 (term-in-abst-form-to-var term))
	  (kernel (term-in-abst-form-to-kernel term)))
      (if (member var (term-to-free subterm)) #f
	  (let ((prev (term-and-var-and-subterm-to-first-decomp-or-f
		       kernel var subterm)))
	    (if (not prev) #f
		(make-term-in-abst-form var1 prev))))))
   ((term-in-app-form? term)
    (let* ((op (term-in-app-form-to-op term))
	   (arg (term-in-app-form-to-arg term))
	   (prev-op (term-and-var-and-subterm-to-first-decomp-or-f
		     op var subterm)))
      (if prev-op
	  (make-term-in-app-form prev-op arg)
	  (let ((prev-arg (term-and-var-and-subterm-to-first-decomp-or-f
			   arg var subterm)))
	    (if (not prev-arg) #f
		(make-term-in-app-form op prev-arg))))))
   (else (myerror "term-and-var-and-subterm-to-first-decomp-or-f"
		  "term expected" term))))

;; Test
;; (define term (pt "x**n*y"))
;; (define var (pv "z"))
;; (define subterm (pt "x**n"))

;; (pp (term-and-var-and-subterm-to-first-decomp-or-f term var subterm))
;; z*y

;; 6-8. First order unification
;; ============================

;; unify checks whether two terms can be unified.  It returns #f, if this
;; is impossible, and a most general unifier otherwise.  unify-list does
;; the same for lists of terms.

(define (occurs? var term)
  (let occurs-aux ((term term))
    (case (tag term)
      ((term-in-var-form)
       (equal? var (term-in-var-form-to-var term)))
      ((term-in-const-form) #f)
      ((term-in-abst-form)
       (and (not (equal? var (term-in-abst-form-to-var term)))
	    (occurs-aux (term-in-abst-form-to-kernel term))))
      ((term-in-app-form)
       (or (occurs-aux (term-in-app-form-to-op term))
	   (occurs-aux (term-in-app-form-to-arg term))))
      ((term-in-pair-form)
       (or (occurs-aux (term-in-pair-form-to-left term))
	   (occurs-aux (term-in-pair-form-to-right term))))
      ((term-in-lcomp-form)
       (occurs-aux (term-in-lcomp-form-to-kernel term)))
      ((term-in-rcomp-form)
       (occurs-aux (term-in-rcomp-form-to-kernel term)))
      ((term-in-if-form)
       (or (occurs-aux (term-in-if-form-to-test term))
	   (do ((l (term-in-if-form-to-alts term) (cdr l)))
	       ((or (null? l) (occurs-aux (car l)))
		(not (null? l))))))
      (else (myerror "occurs?" "term expected" term)))))

(define (disagreement-pair term1 term2)
  (cond
   ((and (term-in-var-form? term1) (term-in-var-form? term2))
    (if (equal? (term-in-var-form-to-var term1)
		(term-in-var-form-to-var term2))
	#f
	(list term1 term2)))
   ((and (term-in-const-form? term1) (term-in-const-form? term2))
    (if (const=? (term-in-const-form-to-const term1)
		 (term-in-const-form-to-const term2))
	#f
	(list term1 term2)))
   ((and (term-in-abst-form? term1) (term-in-abst-form? term2))
    (let ((var1 (term-in-abst-form-to-var term1))
	  (var2 (term-in-abst-form-to-var term2))
	  (kernel1 (term-in-abst-form-to-kernel term1))
	  (kernel2 (term-in-abst-form-to-kernel term2)))
      (if (equal? var1 var2)
	  (disagreement-pair kernel1 kernel2)
	  (if (equal? (var-to-type var1)
		      (var-to-type var2))
	      (let ((newvar (var-to-new-var var1)))
		(disagreement-pair
		 (term-substitute kernel1 (list (list var1 newvar)))
		 (term-substitute kernel2 (list (list var2 newvar)))))
	      (list term1 term2)))))
   ((and (term-in-app-form? term1) (term-in-app-form? term2))
    (disagreement-pair-l
     (list (term-in-app-form-to-op term1) (term-in-app-form-to-arg term1))
     (list (term-in-app-form-to-op term2) (term-in-app-form-to-arg term2))))
   ((and (term-in-pair-form? term1) (term-in-pair-form? term2))
    (disagreement-pair-l
     (list (term-in-pair-form-to-left term1)
	   (term-in-pair-form-to-right term1))
     (list (term-in-pair-form-to-left term2)
	   (term-in-pair-form-to-right term2))))
   ((and (term-in-lcomp-form? term1) (term-in-lcomp-form? term2))
    (disagreement-pair (term-in-lcomp-form-to-kernel term1)
		       (term-in-lcomp-form-to-kernel term2)))
   ((and (term-in-rcomp-form? term1) (term-in-rcomp-form? term2))
    (disagreement-pair (term-in-rcomp-form-to-kernel term1)
		       (term-in-rcomp-form-to-kernel term2)))
   ((and (term-in-if-form? term1) (term-in-if-form? term2))
    (disagreement-pair-l
     (cons (term-in-if-form-to-test term1)
	   (term-in-if-form-to-alts term1))
     (cons (term-in-if-form-to-test term2)
	   (term-in-if-form-to-alts term2))))
   (else (list term1 term2))))

(define (disagreement-pair-l terms1 terms2)
  (cond
   ((null? terms1)
    (if (null? terms2)
	#f
	(myerror "disagreement-pair-l" "termlists of equal length expected"
		 terms1 terms2)))
   ((null? terms2)
    (myerror "disagreement-pair-l" "termlists of equal length expected"
	     terms1 terms2))
   (else (let ((a (disagreement-pair (car terms1) (car terms2))))
	   (if a
	       a
	       (disagreement-pair-l (cdr terms1) (cdr terms2)))))))

(define (unify term1 term2)
  (let unify-aux ((t1 term1) (t2 term2))
    (let ((p (disagreement-pair t1 t2)))
      (if (not p)
	  empty-subst
	  (let ((l (car p)) (r (cadr p)))
	    (cond ((and (term-in-var-form? l)
			(not (occurs? (term-in-var-form-to-var l) r)))
		   (let* ((var (term-in-var-form-to-var l))
			  (prev (unify-aux (term-subst t1 var r)
					   (term-subst t2 var r))))
		     (if prev
			 (extend-subst prev var r)
			 #f)))
		   ((and (term-in-var-form? r)
			 (not (occurs? (term-in-var-form-to-var r) l)))
		    (let* ((var (term-in-var-form-to-var r))
			   (prev (unify-aux (term-subst t1 var l)
					    (term-subst t2 var l))))
		      (if prev
			  (extend-subst prev var l)
			  #f)))
		   (else #f)))))))

(define (unify-list terms1 terms2)
  (unify (apply mk-term-in-pair-form terms1)
	 (apply mk-term-in-pair-form terms2)))

;; Notice that this algorithm does not yield idempotent unifiers
;; (as opposed to the Martelli-Montanari algorithm in modules/type-inf.scm):
;; (display-substitution
;;  (unify-list (list (pt "boole1") (pt "boole2") (pt "T"))
;; 	     (list (pt "boole2") (pt "boole1") (pt "boole1"))))
;; boole2	->	True
;; boole1	->	boole2

;; 6-9. First and second order matching
;; ====================================

;; match checks whether a given pattern (term or formula with type
;; variables in its types) can be transformed by a tosubst - respecting
;; totality constraints - into a given instance, such that (1) no type
;; variable from a given set of identity variables (2) no object
;; variable from a given set of signature variables gets substituted.
;; It returns #f, if this is impossible, and the tosubst otherwise.

;; match-aux is an auxiliary function.  It takes a list of match
;; problems, i.e. lists of items (sig-tvars sig-vars pattern instance),
;; and the substitutions built so far.  It again returns #f or a
;; tosubst.

;; Example: pattern: [x]..x..n.., instance: [n]..n..m..  Then x is
;; renamed into x0 and we have a recursive call to match-aux with
;; pattern: ..x0..n.., instance: ..n..m.., tosubst: alpha -> nat, x0 ->
;; n.

(define (match pattern instance . opt-ignore-deco-flag-and-sig-tovars)
  (let* ((sig-tvars
	  (list-transform-positive opt-ignore-deco-flag-and-sig-tovars
	    tvar-form?))
	 (sig-vars
	  (list-transform-positive opt-ignore-deco-flag-and-sig-tovars
	    var-form?))
	 (rest
	  (list-transform-positive opt-ignore-deco-flag-and-sig-tovars
	    (lambda (x)
	      (not (or (tvar-form? x) (var-form? x))))))
	 (ignore-deco-flag (if (pair? rest) (car rest) #f)))
    (match-aux (list (list sig-tvars sig-vars pattern instance))
	       ignore-deco-flag empty-subst empty-subst)))

(define (match-list patterns instances . opt-ignore-deco-flag-and-sig-tovars)
  (let* ((sig-tvars
	  (list-transform-positive opt-ignore-deco-flag-and-sig-tovars
	    tvar-form?))
	 (sig-vars
	  (list-transform-positive opt-ignore-deco-flag-and-sig-tovars
	    var-form?))
	 (rest
	  (list-transform-positive opt-ignore-deco-flag-and-sig-tovars
	    (lambda (x)
	      (not (or (tvar-form? x) (var-form? x))))))
	 (ignore-deco-flag (if (pair? rest) (car rest) #f)))
    (if (= (length patterns) (length instances))
	(match-aux (map (lambda (p i) (list sig-tvars sig-vars p i))
			patterns instances)
		   ignore-deco-flag empty-subst empty-subst)
	(apply myerror
	       "match-list" "lists of the same length expected" "patterns"
	       (append patterns
		       (list "instances")
		       instances)))))

(define (match-aux match-problems ignore-deco-flag tsubst subst)
  (if
   (null? match-problems)
   (append tsubst subst)
   (let* ((match-problem (car match-problems))
	  (sig-tvars (car match-problem))
	  (sig-vars (cadr match-problem))
	  (pattern (caddr match-problem))
	  (instance (cadddr match-problem)))
     (cond
      ((term-in-var-form? pattern)
       (let* ((type1 (term-to-type pattern))
	      (type2 (term-to-type instance))
	      (var (term-in-var-form-to-var pattern))
	      (t-deg (var-to-t-deg var))
	      (tvars (type-to-tvars type1)))
	 (cond
	  ((term=? pattern instance)
	   (if (or (assoc var subst)
		   (pair? (intersection tvars (map car tsubst))))
	       #f
	       (match-aux
		(map (lambda (mp)
		       (let ((sig-tvars (car mp))
			     (sig-vars (cadr mp)))
			 (cons (append tvars sig-tvars)
			       (cons (cons var sig-vars) (cddr mp)))))
		     (cdr match-problems))
		ignore-deco-flag tsubst subst)))
	  ((member var sig-vars) #f)
	  ((assoc var subst)
	   (and (term=? instance (cadr (assoc var subst)))
		(match-aux (cdr match-problems)
			   ignore-deco-flag tsubst subst)))
	  (else
	   (let ((prev-tsubst (type-match-aux
			       (list type1) (list type2) sig-tvars tsubst)))
	     (and prev-tsubst
		  (or (t-deg-zero? (var-to-t-deg var))
		      (synt-total? instance))
		  (match-aux (cdr match-problems)
			     ignore-deco-flag  prev-tsubst
			     (append subst (list (list var instance))))))))))
      ((term-in-const-form? pattern)
       (and (term-in-const-form? instance)
	    (let* ((type1 (term-to-type pattern))
		   (type2 (term-to-type instance))
		   (const1 (term-in-const-form-to-const pattern))
		   (name1 (const-to-name const1))
		   (const2 (term-in-const-form-to-const instance))
		   (name2 (const-to-name const2)))
	      (and (string=? name1 name2)
		   (if (equal? type1 type2)
		       (match-aux (cdr match-problems)
				  ignore-deco-flag tsubst subst)
		       (let ((prev-tsubst
			      (type-match-aux
			       (list type1) (list type2) sig-tvars tsubst)))
			 (and
			  prev-tsubst
			  (match-aux (cdr match-problems)
				     ignore-deco-flag prev-tsubst subst))))))))
      ((term-in-abst-form? pattern)
       (and
	(term-in-abst-form? instance)
	(let* ((type1 (term-to-type pattern))
	       (type2 (term-to-type instance))
	       (var1 (term-in-abst-form-to-var pattern))
	       (t-deg1 (var-to-t-deg var1))
	       (kernel1 (term-in-abst-form-to-kernel pattern))
	       (var2 (term-in-abst-form-to-var instance))
	       (t-deg2 (var-to-t-deg var2))
	       (varterm2 (make-term-in-var-form var2))
	       (kernel2 (term-in-abst-form-to-kernel instance))
	       (tsubst-from-types
		(type-match-aux
		 (list type1) (list type2) sig-tvars tsubst))
	       (new-var1 (if (= t-deg1 t-deg2)
			     (var-to-new-var var1)
			     (var-and-t-deg-to-new-var var1 t-deg2)))
	       (new-varterm1 (make-term-in-var-form new-var1))
	       (new-kernel1 (term-subst kernel1 var1 new-varterm1))
	       (prev (and tsubst-from-types
			  (match-aux
			   (cons (list sig-tvars sig-vars
				       new-kernel1 kernel2)
				 (cdr match-problems))
			   ignore-deco-flag
			   tsubst-from-types
			   (append subst (list (list new-var1
						     varterm2)))))))
	  (and prev
	       (let ((prev-tsubst (list-transform-positive prev
				    (lambda (x) (tvar-form? (car x)))))
		     (prev-subst (list-transform-positive prev
				   (lambda (x) (var-form? (car x))))))
		 (append prev-tsubst
			 (list-transform-positive prev-subst
			   (lambda (x)
			     (not (equal? new-var1 (car x)))))))))))
      ((term-in-app-form? pattern)
       (and (term-in-app-form? instance)
	    (let ((op1 (term-in-app-form-to-op pattern))
		  (op2 (term-in-app-form-to-op instance))
		  (arg1 (term-in-app-form-to-arg pattern))
		  (arg2 (term-in-app-form-to-arg instance)))
	      (match-aux
	       (cons (list sig-tvars sig-vars op1 op2)
		     (cons (list sig-tvars sig-vars arg1 arg2)
			   (cdr match-problems)))
	       ignore-deco-flag tsubst subst))))
      ((term-in-pair-form? pattern)
       (and (term-in-pair-form? instance)
	    (let ((left1 (term-in-pair-form-to-left pattern))
		  (right1 (term-in-pair-form-to-right pattern))
		  (left2 (term-in-pair-form-to-left instance))
		  (right2 (term-in-pair-form-to-right instance)))
	      (match-aux
	       (cons (list sig-tvars sig-vars left1 left2)
		     (cons (list sig-tvars sig-vars right1 right2)
			   (cdr match-problems)))
	       ignore-deco-flag tsubst subst))))
      ((term-in-lcomp-form? pattern)
       (and (term-in-lcomp-form? instance)
	    (let ((kernel1 (term-in-lcomp-form-to-kernel pattern))
		  (kernel2 (term-in-lcomp-form-to-kernel instance)))
	      (match-aux
	       (cons (list sig-tvars sig-vars kernel1 kernel2)
		     (cdr match-problems))
	       ignore-deco-flag tsubst subst))))
      ((term-in-rcomp-form? pattern)
       (and (term-in-rcomp-form? instance)
	    (let ((kernel1 (term-in-rcomp-form-to-kernel pattern))
		  (kernel2 (term-in-rcomp-form-to-kernel instance)))
	      (match-aux
	       (cons (list sig-tvars sig-vars kernel1 kernel2)
		     (cdr match-problems))
	       ignore-deco-flag tsubst subst))))
      ((term-in-if-form? pattern)
       (and (term-in-if-form? instance)
	    (let* ((test1 (term-in-if-form-to-test pattern))
		   (alts1 (term-in-if-form-to-alts pattern))
		   (test2 (term-in-if-form-to-test instance))
		   (alts2 (term-in-if-form-to-alts instance)))
	      (and (= (length alts1) (length alts2))
		   (let ((new-mps
			  (map (lambda (x y)
				 (list sig-tvars sig-vars x y))
			       (cons test1 alts1) (cons test2 alts2))))
		     (match-aux (append new-mps (cdr match-problems))
				ignore-deco-flag tsubst subst))))))
      ((bicon-form? pattern) ;to be done before inductively defined predicates
       (and
	(bicon-form? instance)
	(let* ((bicon1 (bicon-form-to-bicon pattern))
	       (bicon2 (bicon-form-to-bicon instance))
	       (bicon-eq-test
		(or
		 (eq? bicon1 bicon2)
		 (and ignore-deco-flag
		      (case bicon1
			((imp impnc)
			 (memq bicon2 '(imp impnc)))
			((ord orl orr oru ornc)
			 (memq bicon2 '(ord orl orr oru ornc)))
			((andd andl andr andnc)
			 (memq bicon2 '(andd andl andr andnc)))
			(else #f)))
		 (and (memq bicon1 '(imp impnc))
		      (memq bicon2 '(imp impnc))
		      (formula-of-nulltype? (bicon-form-to-left pattern))
		      (formula-of-nulltype? (bicon-form-to-left instance))))))
	  (and
	   bicon-eq-test
	   (let* ((left1 (bicon-form-to-left pattern))
		  (right1 (bicon-form-to-right pattern))
		  (left2 (bicon-form-to-left instance))
		  (right2 (bicon-form-to-right instance)))
	     (match-aux (cons (list sig-tvars sig-vars left1 left2)
			      (cons (list sig-tvars sig-vars right1 right2)
				    (cdr match-problems)))
			ignore-deco-flag tsubst subst))))))
      ((quant-form? pattern) ;to be done before inductively defined predicates
       (and
	(quant-form? instance)
	(let* ((quant1 (quant-form-to-quant pattern))
	       (quant2 (quant-form-to-quant instance))
	       (quant-eq-test (or (eq? quant1 quant2)
				  (and ignore-deco-flag
				       (case quant1
					 ((all allnc)
					  (memq quant2 '(all allnc)))
					 ((exd exl exr exnc)
					  (memq quant2 '(exd exl exr exnc)))
					 ((exdt exlt exrt exnct)
					  (memq quant2 '(exdt exlt exrt exnct)))
					 (else #f))))))
	  (and
	   quant-eq-test
	   (let* ((vars1 (quant-form-to-vars pattern))
		  (kernel1 (quant-form-to-kernel pattern))
		  (vars2 (quant-form-to-vars instance))
		  (varterms2 (map make-term-in-var-form vars2))
		  (kernel2 (quant-form-to-kernel instance))
		  (types1 (map var-to-type vars1))
		  (types2 (map var-to-type vars2)))
	     (and
	      (equal? (map var-to-type vars1) (map var-to-type vars2))
	      (equal? (map var-to-t-deg vars1) (map var-to-t-deg vars2))
	      (let* ((tsubst-from-types
		      (type-match-aux types1 types2 sig-tvars tsubst))
		     (new-vars1 (map var-to-new-var vars1))
		     (new-varterms1 (map make-term-in-var-form new-vars1))
		     (new-kernel1 (formula-substitute
				   kernel1 (map list vars1 new-varterms1)))
		     (prev (and tsubst-from-types
				(match-aux
				 (cons (list sig-tvars sig-vars
					     new-kernel1 kernel2)
				       (cdr match-problems))
				 ignore-deco-flag
				 tsubst-from-types
				 (append subst (map list
						    new-vars1 varterms2))))))

		(and prev
		     (let ((prev-tsubst (list-transform-positive prev
					  (lambda (x) (tvar-form? (car x)))))
			   (prev-subst (list-transform-positive prev
					 (lambda (x) (var-form? (car x))))))
		       (append prev-tsubst
			       (list-transform-positive prev-subst
				 (lambda (x)
				   (not (member (car x) new-vars1))))))))))))))
      ((predicate-form? pattern) ;but not an inductively defined bicon or quant
       (and
	(predicate-form? instance)
	(let* ((pred1 (predicate-form-to-predicate pattern))
	       (args1 (predicate-form-to-args pattern))
	       (pred2 (predicate-form-to-predicate instance))
	       (args2 (predicate-form-to-args instance)))
	  (and
	   (= (length args1) (length args2))
	   (let ((new-mps (map (lambda (x y) (list sig-tvars sig-vars x y))
			       args1 args2)))
	     (cond
	      ((and (pvar-form? pred1) (pvar-form? pred2)
		    (predicate-equal? pred1 pred2))
	       (match-aux (append new-mps (cdr match-problems))
			  ignore-deco-flag tsubst subst))
	      ((and (predconst-form? pred1) (predconst-form? pred2)
		    (= (predconst-to-index pred1) (predconst-to-index pred2))
		    (let ((name1 (predconst-to-name pred1))
			  (name2 (predconst-to-name pred2)))
		      (or (string=? name1 name2)
			  (string=? name1 (string-append name2 "Nc"))
			  (string=? (string-append name1 "Nc") name2))))
	       (let* ((arity1 (predconst-to-arity pred1))
		      (arity2 (predconst-to-arity pred2))
		      (types1 (arity-to-types arity1))
		      (types2 (arity-to-types arity2))
		      (prev-tsubst
		       (type-match-aux types1 types2 sig-tvars tsubst)))
		 (and prev-tsubst
		      (match-aux (append new-mps (cdr match-problems))
				 ignore-deco-flag prev-tsubst subst))))
	      ((and (idpredconst-form? pred1) (idpredconst-form? pred2)
		    (let ((name1 (idpredconst-to-name pred1))
			  (name2 (idpredconst-to-name pred2)))
		      (or (string=? name1 name2)
			  (string=? name1 (string-append name2 "Nc"))
			  (string=? (string-append name1 "Nc") name2))))
	       (let* ((types1 (idpredconst-to-types pred1))
		      (types2 (idpredconst-to-types pred2))
		      (prev-tsubst
		       (type-match-aux types1 types2 sig-tvars tsubst))
		      (cterms1 (idpredconst-to-cterms pred1))
		      (cterms2 (idpredconst-to-cterms pred2))
		      (aux-flas1
		       (map (lambda (x)
			      (apply mk-all
				     (append (cterm-to-vars x)
					     (list (cterm-to-formula x)))))
			    cterms1))
		      (aux-flas2
		       (map (lambda (x)
			      (apply mk-all
				     (append (cterm-to-vars x)
					     (list (cterm-to-formula x)))))
			    cterms2))
		      (new-mps-aux
		       (map (lambda (x y) (list sig-tvars sig-vars x y))
			    aux-flas1 aux-flas2)))
		 (and prev-tsubst
		      (match-aux (append
				  new-mps-aux new-mps (cdr match-problems))
				 ignore-deco-flag prev-tsubst subst))))
					;added 2011-09-02
	      ((and (predconst-form? pred1)
		    (member
		     (predconst-to-name pred1) ;TotalMR is obsolete
		     (list "Total" "TotalNc" "CoTotal" "CoTotalNc" "TotalMR"
			   "EqP" "EqPNc" "CoEqP" "CoEqPNc"
			   "EqPMR" "CoEqPMR"))
		    (idpredconst-form? pred2))
	       (let ((prev (match-aux (append new-mps (cdr match-problems))
				      ignore-deco-flag tsubst subst)))
		 (and prev
		      (formula=? instance
				 (unfold-formula
				  (formula-substitute pattern prev))
				 ignore-deco-flag)
		      prev)))
	      (else #f)))))))
      ((atom-form? pattern)
       (and (atom-form? instance)
	    (let ((kernel1 (atom-form-to-kernel pattern))
		  (kernel2 (atom-form-to-kernel instance)))
	      (match-aux
	       (cons (list sig-tvars sig-vars kernel1 kernel2)
		     (cdr match-problems))
	       ignore-deco-flag tsubst subst))))
      (else #f)))))

;; first-match looks for a tosubst transforming pattern into the whole
;; term-or-fla (global-match) or a part of term-or-fla.  This instance
;; of pattern is ignored if one of its free variables is captured in
;; term-or-fla (since term-gen-substitute and formula-gen-substitute
;; do not work in this case).  It returns the tosubst, and #f if no
;; tosubst is found.

(define (first-match sig-tovars pattern term-or-fla)
  (or
   (apply match pattern term-or-fla sig-tovars) ;global-match
   (cond
    ((term-in-abst-form? term-or-fla)
     (let* ((var (term-in-abst-form-to-var term-or-fla))
	    (kernel (term-in-abst-form-to-kernel term-or-fla))
	    (subst-kernel
	     (if (t-deg-zero? (var-to-t-deg var))
		 kernel
		 (term-subst kernel var (make-term-in-var-form
					 (var-to-new-partial-var var)))))
	    (prev (first-match sig-tovars pattern subst-kernel)))
       (if ;tosubst found and var not free in instance of pattern
	(and prev
	     (not (member var (term-to-free (term-substitute pattern prev)))))
	prev
	#f)))
    ((term-in-app-form? term-or-fla)
     (let ((op (term-in-app-form-to-op term-or-fla))
	   (arg (term-in-app-form-to-arg term-or-fla)))
       (or (first-match sig-tovars pattern op)
	   (first-match sig-tovars pattern arg))))
    ((term-in-pair-form? term-or-fla)
     (let ((left (term-in-pair-form-to-left term-or-fla))
	   (right (term-in-pair-form-to-right term-or-fla)))
       (or (first-match sig-tovars pattern left)
	   (first-match sig-tovars pattern right))))
    ((term-in-lcomp-form? term-or-fla)
     (let ((kernel (term-in-lcomp-form-to-kernel term-or-fla)))
       (first-match sig-tovars pattern kernel)))
    ((term-in-rcomp-form? term-or-fla)
     (let ((kernel (term-in-rcomp-form-to-kernel term-or-fla)))
       (first-match sig-tovars pattern kernel)))
    ((term-in-if-form? term-or-fla)
     (let ((test (term-in-if-form-to-test term-or-fla))
	   (alts (term-in-if-form-to-alts term-or-fla)))
       (do ((l alts (cdr l))
	    (res (first-match sig-tovars pattern test)
		 (first-match sig-tovars pattern (car l))))
	   ((or res (null? l))
	    (if res res #f)))))
    ((bicon-form? term-or-fla) ;to be done before inductively defined predicates
     (let ((left (bicon-form-to-left term-or-fla))
	   (right (bicon-form-to-right term-or-fla)))
       (or (first-match sig-tovars pattern left)
	   (first-match sig-tovars pattern right))))
    ((quant-form? term-or-fla) ;to be done before inductively defined predicates
     (let* ((vars (quant-form-to-vars term-or-fla))
	    (kernel (quant-form-to-kernel term-or-fla))
	    (prev (first-match sig-tovars pattern kernel)))
       (if ;tosubst found and none of vars free in instance of pattern
	(and prev
	     (null? (intersection
		     vars (term-to-free (term-substitute pattern prev)))))
	prev
	#f)))
    ;; ((quant-form? term-or-fla) ;to be done before inductively defined predicates
    ;;  (let ((kernel (quant-form-to-kernel term-or-fla)))
    ;;    (first-match sig-tovars pattern kernel)))
    ((predicate-form? term-or-fla) ;not an inductively defined bicon or quant
     (let ((pred (predicate-form-to-predicate term-or-fla))
	   (args (predicate-form-to-args term-or-fla)))
       (cond
	((or (pvar-form? pred) (predconst-form? pred))
	 (do ((l args (cdr l))
	      (res #f (first-match sig-tovars pattern (car l))))
	     ((or res (null? l))
	      (if res res #f))))
	((idpredconst-form? pred)
	 (let* ((cterms (idpredconst-to-cterms pred))
		(cterm-flas (map cterm-to-formula cterms)))
	   (or
	    (check-exists (lambda (fla) (first-match sig-tovars pattern fla))
			  cterm-flas)
	    (do ((l args (cdr l))
		 (res #f (first-match sig-tovars pattern (car l))))
		((or res (null? l))
		 (if res res #f))))))
	(else (myerror "first-match" "predicate expected" pred)))))
    ((atom-form? term-or-fla)
     (let ((kernel (atom-form-to-kernel term-or-fla)))
       (first-match sig-tovars pattern kernel)))
    (else #f))))

(define DIALECTICA-FLAG #t)

;; We temporarily stipulate that inductively defined predicates have
;; neither positive nor negative content.

(define (formula-of-nulltypep? formula)
  (cond
   ((bicon-form? formula)
    (let ((bicon (bicon-form-to-bicon formula))
	  (left (bicon-form-to-left formula))
	  (right (bicon-form-to-right formula)))
      (case bicon
	((imp impnc)
	 (and (formula-of-nulltypen? left) (formula-of-nulltypep? right)))
	((and tensor andd andl andr andnc)
	 (and (formula-of-nulltypep? left) (formula-of-nulltypep? right)))
	((ord orl orr oru) #f)
	(else (myerror "formula-of-nulltypep?" "bicon expected" bicon)))))
   ((quant-form? formula)
    (let ((quant (quant-form-to-quant formula))
	  (kernel (quant-form-to-kernel formula)))
      (case quant
	((all allnc) (formula-of-nulltypep? kernel))
	((ex exd exl exdt exlt) #f)
	((exr exnc exrt exnct) (formula-of-nulltypep? kernel))
	((exca excl excu) (formula-of-nulltypep? (unfold-formula formula)))
	(else (myerror "formula-of-nulltypep?" "quant expected" quant)))))
   ((predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula)))
      (cond ((pvar-form? pred) (not (pvar-with-positive-content? pred)))
	    ((predconst-form? pred) #t)
	    ((idpredconst-form? pred) #t))))
   ((atom-form? formula) #t)
   (else (myerror "formula-of-nulltypep?" "formula expected" formula))))

(define (formula-of-nulltypen? formula)
  (cond
   ((bicon-form? formula)
    (let ((bicon (bicon-form-to-bicon formula))
	  (left (bicon-form-to-left formula))
	  (right (bicon-form-to-right formula)))
      (case bicon
	((imp impnc)
	 (and (formula-of-nulltypep? left) (formula-of-nulltypen? right)))
	((and tensor andd andl andr andnc)
	 (and (formula-of-nulltypen? left) (formula-of-nulltypen? right)))
	((ord orl orr oru)
	 (and (formula-of-nulltypen? left) (formula-of-nulltypen? right)))
	(else (myerror "formula-of-nulltypen?" "bicon expected" bicon)))))
   ((quant-form? formula)
    (let ((quant (quant-form-to-quant formula))
	  (kernel (quant-form-to-kernel formula)))
      (case quant
	((all allnc) #f)
	((ex exd exl exdt exlt exr exnc exrt exnct)
	 (formula-of-nulltypen? kernel))
	((exca excl excu) (formula-of-nulltypen? (unfold-formula formula)))
	(else (myerror "formula-of-nulltypen?" "quant expected" quant)))))
   ((predicate-form? formula)
    (let ((pred (predicate-form-to-predicate formula)))
      (cond ((pvar-form? pred) (not (pvar-with-negative-content? pred)))
	    ((predconst-form? pred) #t)
	    ((idpredconst-form? pred) #t))))
   ((atom-form? formula) #t)
   (else (myerror "formula-of-nulltypen?" "formula expected" formula))))

;; Tests

;; (formula-to-etd-types (pf "(ex boole (Pvar boole)boole -> bot) -> bot"))
;; ((alg "boole") (tconst "nulltype"))

;; (formula-of-nulltypep? (pf "T"))
;; (formula-of-nulltypen? (pf "T"))
;; (formula-of-nulltypep? (pf "bot"))
;; (formula-of-nulltypen? (pf "bot"))
;; (formula-of-nulltypep? (pf "ex boole T"))
;; (formula-of-nulltypen? (pf "ex boole T"))
;; (formula-of-nulltypep? (pf "excl boole T"))
;; (formula-of-nulltypen? (pf "excl boole T"))
;; (formula-of-nulltypep? (pf "all boole0,boole1(T -> T)"))
;; (formula-of-nulltypen? (pf "all boole0,boole1(T -> T)"))
;; (pp (formula-to-etdn-type (pf "all boole0,boole1(T -> T)")))

(set! DIALECTICA-FLAG #f)

;; (pattern-and-instance-to-tsubst pattern instance . sig-topvars)
;; returns either #f or a tsubst.  In the first case instance does not
;; match (passt nicht zum) pattern.  In the second case instance
;; matches pattern if and only if it matches pattern substituted by
;; tsubst, without any further type substitution.

;; pattern-and-instance-to-tsubst-aux is an auxiliary function.  It
;; takes a list of pattern-and-instance-to-tsubst problems, i.e., lists
;; of items (sig-tvars sig-vars sig-pvars pattern instance), and the
;; tsubst and subst built so far.  It returns either #f or a tosubst.

(define (pattern-and-instance-to-tsubst
	 pattern instance . opt-ignore-deco-flag-and-sig-topvars)
  (let* ((sig-tvars
	  (list-transform-positive opt-ignore-deco-flag-and-sig-topvars
	    tvar-form?))
	 (sig-vars
	  (list-transform-positive opt-ignore-deco-flag-and-sig-topvars
	    var-form?))
	 (sig-pvars
	  (list-transform-positive opt-ignore-deco-flag-and-sig-topvars
	    pvar-form?))
	 (rest
	  (list-transform-positive opt-ignore-deco-flag-and-sig-topvars
	    (lambda (x)
	      (not (or (tvar-form? x) (var-form? x) (pvar-form? x))))))
	 (ignore-deco-flag (if (pair? rest) (car rest) #f))
	 (prev (pattern-and-instance-to-tsubst-aux
		(list (list sig-tvars sig-vars sig-pvars pattern instance))
		ignore-deco-flag empty-subst empty-subst)))
    (and prev
	 (list-transform-positive prev
	   (lambda (x) (tvar-form? (car x)))))))

(define (pattern-and-instance-to-tsubst-aux
	 match-problems ignore-deco-flag tsubst subst)
  (if
   (null? match-problems)
   (append tsubst subst)
   (let* ((match-problem (car match-problems))
	  (sig-tvars (car match-problem))
	  (sig-vars (cadr match-problem))
	  (sig-pvars (caddr match-problem))
	  (pattern (cadddr match-problem))
	  (instance (car (cddddr match-problem))))
     (cond
      ((and (term-form? pattern)
	    (term-in-var-form? (term-in-app-form-to-final-op pattern)))
       (let* ((type1 (term-to-type pattern))
	      (type2 (term-to-type instance))
	      (op (term-in-app-form-to-final-op pattern))
	      (var (term-in-var-form-to-var op))
	      (args (term-in-app-form-to-args pattern))
	      (t-deg (var-to-t-deg var))
	      (tvars (type-to-tvars type1)))
	 (cond
	  ((term=? pattern instance)
	   (if (or (assoc var subst)
		   (pair? (intersection tvars (map car tsubst))))
	       #f
	       (pattern-and-instance-to-tsubst-aux
		(map (lambda (mp)
		       (let ((sig-tvars (car mp))
			     (sig-vars (cadr mp))
			     (sig-pvars (caddr mp)))
			 (cons (append tvars sig-tvars)
			       (cons (cons var sig-vars)
				     (cons sig-pvars (cdddr mp))))))
		     (cdr match-problems))
		ignore-deco-flag tsubst subst)))
	  ((member var sig-vars)
	   (and (pair? args)
		(term-in-app-form? instance)
		(let ((op2 (term-in-app-form-to-final-op instance))
		      (args2 (term-in-app-form-to-args instance)))
		  (and (= (length args) (length args2))
		       (let ((new-mps
			      (map (lambda (x y)
				     (list sig-tvars sig-vars sig-pvars x y))
				   args args2)))
			 (and (equal? op op2)
			      (pattern-and-instance-to-tsubst-aux
			       (append new-mps (cdr match-problems))
			       ignore-deco-flag tsubst subst)))))))
	  ((assoc var subst)
	   (let* ((val (cadr (assoc var subst)))
		  (subst-pattern (term-subst-and-beta0-nf pattern var val))
		  (new-mp (list sig-tvars sig-vars sig-pvars
				subst-pattern instance)))
	     (pattern-and-instance-to-tsubst-aux
	      (cons new-mp (cdr match-problems))
	      ignore-deco-flag tsubst subst)))
	  ((not (or (t-deg-zero? (var-to-t-deg var)) (synt-total? instance)))
	   #f)
	  ((null? args)
	   (if (equal? type1 type2)
	       (pattern-and-instance-to-tsubst-aux
		(cdr match-problems)
		ignore-deco-flag tsubst
		(append subst (list (list var instance))))
	       (let ((prev-tsubst
		      (type-match-aux
		       (list type1) (list type2) sig-tvars tsubst)))
		 (and prev-tsubst
		      (pattern-and-instance-to-tsubst-aux
		       (cdr match-problems)
		       ignore-deco-flag prev-tsubst
		       (append subst (list (list var instance))))))))
	  ((term-in-app-form? instance)
	   (let* ((op1 (term-in-app-form-to-op pattern))
		  (arg1 (term-in-app-form-to-arg pattern))
		  (op2 (term-in-app-form-to-op instance))
		  (arg2 (term-in-app-form-to-arg instance))
		  (new-mp-op (list sig-tvars sig-vars sig-pvars op1 op2))
		  (new-mp-arg (list sig-tvars sig-vars sig-pvars arg1 arg2)))
	     (pattern-and-instance-to-tsubst-aux
	      (cons new-mp-op (cons new-mp-arg (cdr match-problems)))
	      ignore-deco-flag tsubst subst)))
	  (else ;x rs and c
	   (if (equal? type1 type2)
	       (pattern-and-instance-to-tsubst-aux
		(cdr match-problems) ignore-deco-flag tsubst subst)
	       (let ((prev-tsubst
		      (type-match-aux
		       (list type1) (list type2) sig-tvars tsubst)))
		 (and prev-tsubst
		      (pattern-and-instance-to-tsubst-aux
		       (cdr match-problems)
		       ignore-deco-flag prev-tsubst subst))))))))
      ((term-in-const-form? pattern)
       (and (term-in-const-form? instance)
	    (let* ((type1 (term-to-type pattern))
		   (type2 (term-to-type instance))
		   (const1 (term-in-const-form-to-const pattern))
		   (name1 (const-to-name const1))
		   (const2 (term-in-const-form-to-const instance))
		   (name2 (const-to-name const2)))
	      (and (string=? name1 name2)
		   (if (equal? type1 type2)
		       (pattern-and-instance-to-tsubst-aux
			(cdr match-problems) ignore-deco-flag tsubst subst)
		       (let ((prev-tsubst
			      (type-match-aux
			       (list type1) (list type2) sig-tvars tsubst)))
			 (and prev-tsubst
			      (pattern-and-instance-to-tsubst-aux
			       (cdr match-problems)
			       ignore-deco-flag prev-tsubst subst))))))))
      ((term-in-abst-form? pattern)
       (and
	(term-in-abst-form? instance)
	(let* ((type1 (term-to-type pattern))
	       (type2 (term-to-type instance))
	       (var1 (term-in-abst-form-to-var pattern))
	       (kernel1 (term-in-abst-form-to-kernel pattern))
	       (var2 (term-in-abst-form-to-var instance))
	       (varterm2 (make-term-in-var-form var2))
	       (kernel2 (term-in-abst-form-to-kernel instance)))
	  (and
	   (= (var-to-t-deg var1) (var-to-t-deg var2))
	   (let* ((tsubst-from-types
		   (type-match-aux
		    (list type1) (list type2) sig-tvars tsubst))
		  (new-var1 (var-to-new-var var1))
		  (new-varterm1 (make-term-in-var-form new-var1))
		  (new-kernel1 (term-subst kernel1 var1 new-varterm1))
		  (prev
		   (and tsubst-from-types
			(pattern-and-instance-to-tsubst-aux
			 (cons (list sig-tvars sig-vars sig-pvars
				     new-kernel1 kernel2)
			       (cdr match-problems))
			 ignore-deco-flag tsubst-from-types
			 (append subst (list (list new-var1 varterm2)))))))
	     (and prev
		  (let ((prev-tsubst (list-transform-positive prev
				       (lambda (x) (tvar-form? (car x)))))
			(prev-subst (list-transform-positive prev
				      (lambda (x) (var-form? (car x))))))
		    (append
		     prev-tsubst
		     (list-transform-positive prev-subst
		       (lambda (x) (not (equal? new-var1 (car x)))))))))))))
      ((term-in-app-form? pattern)
       (and (term-in-app-form? instance)
	    (let ((op1 (term-in-app-form-to-op pattern))
		  (op2 (term-in-app-form-to-op instance))
		  (arg1 (term-in-app-form-to-arg pattern))
		  (arg2 (term-in-app-form-to-arg instance)))
	      (pattern-and-instance-to-tsubst-aux
	       (cons (list sig-tvars sig-vars sig-pvars op1 op2)
		     (cons (list sig-tvars sig-vars sig-pvars arg1 arg2)
			   (cdr match-problems)))
	       ignore-deco-flag tsubst subst))))
      ((term-in-pair-form? pattern)
       (and (term-in-pair-form? instance)
	    (let ((left1 (term-in-pair-form-to-left pattern))
		  (right1 (term-in-pair-form-to-right pattern))
		  (left2 (term-in-pair-form-to-left instance))
		  (right2 (term-in-pair-form-to-right instance)))
	      (pattern-and-instance-to-tsubst-aux
	       (cons (list sig-tvars sig-vars sig-pvars left1 left2)
		     (cons (list sig-tvars sig-vars sig-pvars right1 right2)
			   (cdr match-problems)))
	       ignore-deco-flag tsubst subst))))
      ((term-in-lcomp-form? pattern)
       (and (term-in-lcomp-form? instance)
	    (let ((kernel1 (term-in-lcomp-form-to-kernel pattern))
		  (kernel2 (term-in-lcomp-form-to-kernel instance)))
	      (pattern-and-instance-to-tsubst-aux
	       (cons (list sig-tvars sig-vars sig-pvars kernel1 kernel2)
		     (cdr match-problems))
	       ignore-deco-flag tsubst subst))))
      ((term-in-rcomp-form? pattern)
       (and (term-in-rcomp-form? instance)
	    (let ((kernel1 (term-in-rcomp-form-to-kernel pattern))
		  (kernel2 (term-in-rcomp-form-to-kernel instance)))
	      (pattern-and-instance-to-tsubst-aux
	       (cons (list sig-tvars sig-vars sig-pvars kernel1 kernel2)
		     (cdr match-problems))
	       ignore-deco-flag tsubst subst))))
      ((term-in-if-form? pattern)
       (and (term-in-if-form? instance)
	    (let* ((test1 (term-in-if-form-to-test pattern))
		   (alts1 (term-in-if-form-to-alts pattern))
		   (test2 (term-in-if-form-to-test instance))
		   (alts2 (term-in-if-form-to-alts instance)))
	      (and (= (length alts1) (length alts2))
		   (let ((new-mps
			  (map (lambda (x y)
				 (list sig-tvars sig-vars sig-pvars x y))
			       (cons test1 alts1) (cons test2 alts2))))
		     (pattern-and-instance-to-tsubst-aux
		      (append new-mps (cdr match-problems))
		      ignore-deco-flag tsubst subst))))))
      ((and (predicate-form? pattern)
	    (pvar-form? (predicate-form-to-predicate pattern)))
       (let* ((pvar (predicate-form-to-predicate pattern))
	      (args (predicate-form-to-args pattern))
	      (arity1 (pvar-to-arity pvar))
	      (types (arity-to-types arity1))
	      (tvars (apply append (map type-to-tvars types))))
	 (cond
	  ((formula=? pattern instance)
	   (if (pair? (intersection tvars (map car tsubst)))
	       #f
	       (pattern-and-instance-to-tsubst-aux
		(map (lambda (mp)
		       (let ((sig-tvars (car mp))
			     (sig-vars (cadr mp))
			     (sig-pvars (caddr mp)))
			 (cons sig-tvars
			       (cons sig-vars
				     (cons (cons pvar sig-pvars)
					   (cdddr mp))))))
		     (cdr match-problems))
		ignore-deco-flag tsubst subst)))
	  ((member pvar sig-pvars)
	   (and (pair? args)
		(predicate-form? instance)
		(let ((pred2 (predicate-form-to-predicate instance))
		      (args2 (predicate-form-to-args instance)))
		  (and (= (length args) (length args2))
		       (let ((new-mps
			      (map (lambda (x y)
				     (list sig-tvars sig-vars sig-pvars x y))
				   args args2)))
			 (and (equal? pvar pred2)
			      (pattern-and-instance-to-tsubst-aux
			       (append new-mps (cdr match-problems))
			       ignore-deco-flag tsubst subst)))))))
	  (else
	   (and (if DIALECTICA-FLAG
		    (and (or (formula-of-nulltypep? instance)
			     (pvar-with-positive-content? pvar))
			 (or (formula-of-nulltypen? instance)
			     (pvar-with-negative-content? pvar)))
		    (or (formula-of-nulltype? instance)
			(pvar-with-positive-content? pvar)))
		(pattern-and-instance-to-tsubst-aux
		 (cdr match-problems)
		 ignore-deco-flag tsubst subst))))))
      ((bicon-form? pattern)
       (and
	(bicon-form? instance)
	(let* ((bicon1 (bicon-form-to-bicon pattern))
	       (bicon2 (bicon-form-to-bicon instance))
	       (bicon-eq-test (or (eq? bicon1 bicon2)
				  (and ignore-deco-flag
				       (case bicon1
					 ((imp impnc)
					  (memq bicon2 '(imp impnc)))
					 ((ord orl orr oru)
					  (memq bicon2 '(ord orl orr oru)))
					 ((andd andl andr andnc)
					  (memq bicon2 '(andd andl andr andnc)))
					 (else #f))))))
	  (and
	   bicon-eq-test
	   (let* ((left1 (bicon-form-to-left pattern))
		  (right1 (bicon-form-to-right pattern))
		  (left2 (bicon-form-to-left instance))
		  (right2 (bicon-form-to-right instance)))
	     (pattern-and-instance-to-tsubst-aux
	      (cons (list sig-tvars sig-vars sig-pvars left1 left2)
		    (cons (list sig-tvars sig-vars sig-pvars right1 right2)
			  (cdr match-problems)))
	      ignore-deco-flag tsubst subst))))))
      ((quant-form? pattern)
       (and
	(quant-form? instance)
	(let* ((quant1 (quant-form-to-quant pattern))
	       (quant2 (quant-form-to-quant instance))
	       (quant-eq-test (or (eq? quant1 quant2)
				  (and ignore-deco-flag
				       (case quant1
					 ((all allnc)
					  (memq quant2 '(all allnc)))
					 ((exd exl exr exnc)
					  (memq quant2 '(exd exl exr exnc)))
					 ((exdt exlt exrt exnct)
					  (memq quant2 '(exdt exlt exrt exnct)))
					 (else #f))))))
	  (and
	   quant-eq-test
	   (let* ((vars1 (quant-form-to-vars pattern))
		  (kernel1 (quant-form-to-kernel pattern))
		  (vars2 (quant-form-to-vars instance))
		  (varterms2 (map make-term-in-var-form vars2))
		  (kernel2 (quant-form-to-kernel instance))
		  (types1 (map var-to-type vars1))
		  (types2 (map var-to-type vars2)))
	     (and
	      (equal? (map var-to-t-deg vars1) (map var-to-t-deg vars2))
	      (let* ((tsubst-from-types
		      (type-match-aux types1 types2 sig-tvars tsubst))
		     (new-vars1 (map var-to-new-var vars1))
		     (new-varterms1 (map make-term-in-var-form new-vars1))
		     (new-kernel1 (formula-substitute
				   kernel1 (map list vars1 new-varterms1)))
		     (prev (and tsubst-from-types
				(pattern-and-instance-to-tsubst-aux
				 (cons (list sig-tvars sig-vars sig-pvars
					     new-kernel1 kernel2)
				       (cdr match-problems))
				 ignore-deco-flag tsubst-from-types
				 (append subst
					 (map list
					      new-vars1 varterms2))))))
		(and prev
		     (let ((prev-tsubst (list-transform-positive prev
					  (lambda (x) (tvar-form? (car x)))))
			   (prev-subst (list-transform-positive prev
					 (lambda (x) (var-form? (car x))))))
		       (append prev-tsubst
			       (list-transform-positive prev-subst
				 (lambda (x)
				   (not (member (car x) new-vars1))))))))))))))
      ((predicate-form? pattern) ;but not with a predicate variable
       (and
	(predicate-form? instance)
	(let ((pred1 (predicate-form-to-predicate pattern))
	      (args1 (predicate-form-to-args pattern))
	      (pred2 (predicate-form-to-predicate instance))
	      (args2 (predicate-form-to-args instance)))
	  (and
	   (= (length args1) (length args2))
	   (let ((new-mps
		  (map (lambda (x y) (list sig-tvars sig-vars sig-pvars x y))
		       args1 args2)))
	     (cond
	      ((and (predconst-form? pred1) (predconst-form? pred2)
		    (= (predconst-to-index pred1) (predconst-to-index pred2))
		    (string=? (predconst-to-name pred1)
			      (predconst-to-name pred2)))
	       (let* ((arity1 (predconst-to-arity pred1))
		      (arity2 (predconst-to-arity pred2))
		      (types1 (arity-to-types arity1))
		      (types2 (arity-to-types arity2))
		      (prev-tsubst
		       (type-match-aux types1 types2 sig-tvars tsubst)))
		 (and prev-tsubst
		      (pattern-and-instance-to-tsubst-aux
		       (append new-mps (cdr match-problems))
		       ignore-deco-flag prev-tsubst subst))))
	      ((and (idpredconst-form? pred1) (idpredconst-form? pred2)
		    (string=? (idpredconst-to-name pred1)
			      (idpredconst-to-name pred2)))
	       (let* ((types1 (idpredconst-to-types pred1))
		      (types2 (idpredconst-to-types pred2))
		      (prev-tsubst
		       (type-match-aux types1 types2 sig-tvars tsubst)))
		 (and prev-tsubst
		      (pattern-and-instance-to-tsubst-aux
		       (append new-mps (cdr match-problems))
		       ignore-deco-flag prev-tsubst subst))))
					;added 2012-09-13
	      ((and (predconst-form? pred1)
		    (member
		     (predconst-to-name pred1) ;TotalMR is obsolete
		     (list "Total" "TotalNc" "CoTotal" "CoTotalNc" "TotalMR"
			   "EqP" "EqPNc" "CoEqP" "CoEqPNc" "EqPMR" "CoEqPMR"))
		    (idpredconst-form? pred2))
	       (let ((prev (pattern-and-instance-to-tsubst-aux
			    (append new-mps (cdr match-problems))
			    ignore-deco-flag tsubst subst)))
		 (and prev
		      (formula=? instance
				 (unfold-formula
				  (formula-substitute pattern prev)))
		      prev)))
	      (else #f)))))))
      ((atom-form? pattern)
       (and (atom-form? instance)
	    (let ((kernel1 (atom-form-to-kernel pattern))
		  (kernel2 (atom-form-to-kernel instance)))
	      (pattern-and-instance-to-tsubst-aux
	       (cons (list sig-tvars sig-vars sig-pvars kernel1 kernel2)
		     (cdr match-problems))
	       ignore-deco-flag tsubst subst))))
      (else #f)))))

;; 6-10. Pattern unification
;; =========================

;; A pattern (more precisely a higher order pattern) is an expression
;; (i.e. a term or a formula) in beta normal form with the property
;; that every ``flexible'' variable y occurs in a context yx1...xn with
;; distinct ``forbidden'' (for substitutions) variables x1...xn.
;; Forbidden variables are the ones bound further outside, or given
;; explicitly as forbidden.  Comments:
;; - yx1...xn need not be of ground type.
;; - eta-expansion of the xi is not allowed (for simplicity).

(define (pattern? expr flex-vars forb-vars)
  (cond
   ((term-form? expr)
    (case (tag expr)
      ((term-in-app-form)
       (let* ((op (term-in-app-form-to-final-op expr))
	      (args (term-in-app-form-to-args expr)))
	 (if (and (term-in-var-form? op)
		  (member (term-in-var-form-to-var op) flex-vars))
	     (and (apply and-op (map term-in-var-form? args))
		  (let ((argvars (map term-in-var-form-to-var args)))
		    (and (equal? argvars (remove-duplicates argvars))
			 (null? (set-minus argvars forb-vars)))))
	     (apply and-op (map (lambda (x) (pattern? x flex-vars forb-vars))
				args)))))
      ((term-in-abst-form)
       (let ((var (term-in-abst-form-to-var expr))
	     (kernel (term-in-abst-form-to-kernel expr)))
	 (if (or (member var flex-vars) (member var forb-vars))
	     (let* ((new-var (var-to-new-var var))
		    (new-kernel
		     (term-subst kernel var (make-term-in-var-form new-var))))
	       (pattern? new-kernel flex-vars (cons new-var forb-vars)))
	     (pattern? kernel flex-vars (cons var forb-vars)))))
      ((term-in-var-form term-in-const-form)
       #t)
      ((term-in-pair-form)
       (and (pattern? (term-in-pair-form-to-left expr) flex-vars forb-vars)
	    (pattern? (term-in-pair-form-to-right expr) flex-vars forb-vars)))
      ((term-in-lcomp-form)
       (pattern? (term-in-lcomp-form-to-kernel expr) flex-vars forb-vars))
      ((term-in-rcomp-form)
       (pattern? (term-in-rcomp-form-to-kernel expr) flex-vars forb-vars))
      ((term-in-if-form)
       (apply and-op (map (lambda (x) (pattern? x flex-vars forb-vars))
			  (cons (term-in-if-form-to-test expr)
				(term-in-if-form-to-alts expr)))))
      (else (myerror "pattern?" "term expected" expr))))
   ((formula-form? expr)
    (case (tag expr)
      ((atom)
       (pattern? (atom-form-to-kernel expr) flex-vars forb-vars))
      ((predicate)
       (apply and-op (map (lambda (x) (pattern? x flex-vars forb-vars))
			  (predicate-form-to-args expr))))
      ((imp)
       (and (pattern? (imp-form-to-premise expr) flex-vars forb-vars)
	    (pattern? (imp-form-to-conclusion expr) flex-vars forb-vars)))
      ((and)
       (and (pattern? (and-form-to-left expr) flex-vars forb-vars)
	    (pattern? (and-form-to-right expr) flex-vars forb-vars)))
      ((tensor)
       (and (pattern? (tensor-form-to-left expr) flex-vars forb-vars)
	    (pattern? (tensor-form-to-right expr) flex-vars forb-vars)))
      ((all ex allnc exca excl)
       (let ((vars (quant-form-to-vars expr))
	     (kernel (quant-form-to-kernel expr)))
	 (if (or (pair? (intersection vars flex-vars))
		 (pair? (intersection vars forb-vars)))
	     (let* ((new-vars (map var-to-new-var vars))
		    (new-kernel
		     (formula-substitute
		      kernel (make-substitution
			      vars (map make-term-in-var-form new-vars)))))
	       (pattern? new-kernel flex-vars (append new-vars forb-vars)))
	     (pattern? kernel flex-vars (append vars forb-vars)))))
      (else (myerror "pattern?" "formula expected" expr))))
   (else (myerror "pattern?" "term or formula expected" expr))))

;; The main function pattern-unify implements in a slightly modified form
;; Miller's pattern unification algorithm from Miller (J. Logic Computat.
;; Vol. 1, 1991).  The modification consists in changing the order of
;; steps: raising is postponed until it is needed, to avoid unnecessary
;; creation of new variables.  It is obtained by iterating a one-step
;; function pattern-unify1, implementing the step from a state formula S
;; to either #f, indicating that there is no unifier, or else a pair
;; (rho, S') with a ``transition'' substitution rho.  A state formula S
;; consists of a prefix Q of the form all sig-vars ex flex-vars all
;; forb-vars, followed by a list of unification pairs.  All terms in this
;; list are patterns w.r.t. Q.  We call

;; - sig-vars the signature variables (to avoid unnecessary renaming),

;; - flex-vars the flexible variables (to be substituted),

;; - forb-vars the forbidden variables (not allowed in substitution terms).

;; The domain of rho consists of flexible variables from S only, and its
;; value terms never contain a forbidden variable (of either S or S')
;; free.  Moreover, rho is idempotent.  pattern-unify1 satifies the
;; following property.  Assume (pattern-unify1 S) = (rho S').  Then for
;; every S'-solution phi', (rho composed phi')restricted Q_exists is an
;; S-solution, and every S-solution can be obtained in this way.

(define (pattern-unify sig-vars flex-vars forb-vars . unif-pairs)
  (if
   (null? unif-pairs)
   (list empty-subst sig-vars flex-vars forb-vars)
   (let ((one-step
	  (apply
	   pattern-unify1
	   sig-vars flex-vars (cons forb-vars unif-pairs))))
     (if (pair? one-step)
	 (let* ((rho1 (car one-step))
		(state1 (cdr one-step))
		(prev (apply pattern-unify state1)))
	   (if (pair? prev)
	       (let ((rho (car prev))
		     (final-state (cdr prev)))
		 (cons (compose-substitutions-and-beta0-nf rho1 rho)
		       final-state))
	       #f))
	 #f))))

(define (pattern-unify1 sig-vars flex-vars forb-vars . unif-pairs)
  (if
   (null? unif-pairs)
   (myerror "pattern-unify1" "non null unif-pairs expected")
   (let ((expr1 (caar unif-pairs))
	 (expr2 (cadar unif-pairs))
	 (rest-unif-pairs (cdr unif-pairs)))
     (pattern-unify-equality
      sig-vars flex-vars forb-vars expr1 expr2 rest-unif-pairs))))

;; or more generally

;; (define (pattern-unify-list sig-vars flex-vars forb-vars exprs1 exprs2)
;;   (cond ((and (null? exprs1) (null? exprs2))
;; 	 (list sig-vars flex-vars forb-vars empty-subst))
;; 	((not (= (length exprs1) (length exprs2)))
;; 	 (myerror "pattern-unify-list: equal lengths expected"
;; 		  (length exprs1) (length exprs2)))
;; 	(else (pattern-unify-equality
;; 	       sig-vars flex-vars forb-vars (car exprs1) (car exprs2)
;; 	       (map list (cdr exprs1) (cdr exprs2))
;; 	       empty-subst))))

;; pattern-unify-equality checks whether its two expression arguments are
;; equal.  If so, continue with the remaining unification pairs.  If not,
;; call pattern-unify-xi.

(define (pattern-unify-equality
	 sig-vars flex-vars forb-vars expr1 expr2 rest-unif-pairs)
  (if (or (and (term-form? expr1) (term-form? expr2) (term=? expr1 expr2))
	  (and (formula-form? expr1) (formula-form? expr2)
	       (formula=? expr1 expr2)))
      (if (pair? rest-unif-pairs)
          (pattern-unify-equality
           sig-vars flex-vars forb-vars
           (caar rest-unif-pairs) (cadar rest-unif-pairs)
           (cdr rest-unif-pairs))
          (list empty-subst sig-vars flex-vars forb-vars))
      (pattern-unify-xi
       sig-vars flex-vars forb-vars expr1 expr2 rest-unif-pairs)))

;; pattern-unify-xi removes common bound variables and adds them to the
;; prefix.  Then pattern-unify-rigid-rigid is called.

(define (pattern-unify-xi
	 sig-vars flex-vars forb-vars expr1 expr2 rest-unif-pairs)
  (cond
   ((or (term-in-abst-form? expr1) (term-in-abst-form? expr2))
    (let* ((vars-and-kernels (common-lambda-vars-and-kernels expr1 expr2))
	   (lambda-vars (car vars-and-kernels))
	   (kernel1 (cadr vars-and-kernels))
	   (kernel2 (caddr vars-and-kernels))
	   (info (pair? (intersection
			 (append sig-vars flex-vars forb-vars) lambda-vars)))
	   (new-vars (if info
			 (map var-to-new-var lambda-vars)
			 lambda-vars))
	   (subst (make-substitution-wrt
		   var-term-equal?
		   lambda-vars (map make-term-in-var-form new-vars)))
	   (new-kernel1 (if info
			    (term-substitute kernel1 subst)
			    kernel1))
	   (new-kernel2 (if info
			    (term-substitute kernel2 subst)
			    kernel2)))
      (if (null? flex-vars)
	  (pattern-unify-rigid-rigid
	   (append sig-vars new-vars) '() forb-vars
	   new-kernel1 new-kernel2 rest-unif-pairs)
	  (pattern-unify-rigid-rigid
	   sig-vars flex-vars (append forb-vars new-vars)
	   new-kernel1 new-kernel2 rest-unif-pairs))))
   ((or (and (all-form? expr1) (all-form? expr2))
	(and (allnc-form? expr1) (allnc-form? expr2))
	(and (ex-form? expr1) (ex-form? expr2)))
    (let ((var1 (cond ((all-form? expr1) (all-form-to-var expr1))
		      ((allnc-form? expr1) (allnc-form-to-var expr1))
		      ((ex-form? expr1) (ex-form-to-var expr1))))
	  (kernel1 (cond ((all-form? expr1) (all-form-to-kernel expr1))
			 ((allnc-form? expr1) (allnc-form-to-kernel expr1))
			 ((ex-form? expr1) (ex-form-to-kernel expr1))))
	  (var2 (cond ((all-form? expr2) (all-form-to-var expr2))
		      ((allnc-form? expr2) (allnc-form-to-var expr2))
		      ((ex-form? expr2) (ex-form-to-var expr2))))
	  (kernel2 (cond ((all-form? expr2) (all-form-to-kernel expr2))
			 ((allnc-form? expr2) (allnc-form-to-kernel expr2))
			 ((ex-form? expr2) (ex-form-to-kernel expr2)))))
      (cond
       ((equal? var1 var2)
	(let* ((info (member var1 (append sig-vars flex-vars forb-vars)))
	       (new-var (if info (var-to-new-var var1) var1))
	       (new-kernel1
		(if info
		    (formula-subst
		     kernel1 var1 (make-term-in-var-form new-var))
		    kernel1))
	       (new-kernel2
		(if info
		    (formula-subst
		     kernel2 var2 (make-term-in-var-form new-var))
		    kernel2)))
	  (if (null? flex-vars)
	      (pattern-unify-xi
	       (append sig-vars (list new-var)) '() forb-vars
	       new-kernel1 new-kernel2 rest-unif-pairs)
	      (pattern-unify-xi
	       sig-vars flex-vars (append forb-vars (list new-var))
	       new-kernel1 new-kernel2 rest-unif-pairs))))
       ((and (equal? (var-to-type var1) (var-to-type var2))
	     (= (var-to-t-deg var1) (var-to-t-deg var2)))
	(let* ((new-var (var-to-new-var var1))
	       (new-kernel1 (formula-subst
			     kernel1 var1 (make-term-in-var-form new-var)))
	       (new-kernel2 (formula-subst
			     kernel2 var2 (make-term-in-var-form new-var))))
	  (if (null? flex-vars)
	      (pattern-unify-xi
	       (append sig-vars (list new-var)) '() forb-vars
	       new-kernel1 new-kernel2 rest-unif-pairs)
	      (pattern-unify-xi
	       sig-vars flex-vars (append forb-vars (list new-var))
	       new-kernel1 new-kernel2 rest-unif-pairs))))
       (else #f))))
   (else (pattern-unify-rigid-rigid
	  sig-vars flex-vars forb-vars expr1 expr2 rest-unif-pairs))))

;; We need an auxiliary function common-lambda-vars-and-kernels.  For
;; terms term1 and term2 of the same type it yields alpha-eta-equivalent
;; representations lambda vec{x} s1 and lambda vec{x} s2 with the same
;; variables vec{x} and non-lambda-kernels s1 and s2 (i.e. applications).
;; Examples: [x](f1 x) , f2 => ((x) (f1 x) (f2 x))
;; [x](f1 x) , [y](f2 y) => ((x) (f1 x) (f2 x))

(define (common-lambda-vars-and-kernels term1 term2)
  (let ((type (term-to-type term1)))
    (if
     (ground-type? type)
     (list '() term1 term2)
     (if
      (term-in-abst-form? term1)
      (let ((var1 (term-in-abst-form-to-var term1))
	    (kernel1 (term-in-abst-form-to-kernel term1)))
	(if
	 (term-in-abst-form? term2)
	 (let* ((var2 (term-in-abst-form-to-var term2))
		(kernel2 (term-in-abst-form-to-kernel term2))
		(prev (common-lambda-vars-and-kernels kernel1 kernel2)))
	   (list
	    (cons var1 (car prev))
	    (cadr prev)
	    (if (or (equal? var1 var2) (member var2 (car prev)))
;; 	    (if (equal? var1 var2)
		(caddr prev)
		(term-subst (caddr prev) var2 (make-term-in-var-form var1)))))
	 (let ((prev (common-lambda-vars-and-kernels
		      kernel1
		      (mk-term-in-app-form term2
					   (make-term-in-var-form var1)))))
	   (list (cons var1 (car prev))
		 (cadr prev)
		 (caddr prev)))))
      (if
       (term-in-abst-form? term2)
       (let* ((var2 (term-in-abst-form-to-var term2))
	      (kernel2 (term-in-abst-form-to-kernel term2))
	      (prev (common-lambda-vars-and-kernels
		     (mk-term-in-app-form term1 (make-term-in-var-form var2))
		     kernel2)))
	 (list (cons var2 (car prev)) (cadr prev) (caddr prev)))
       (list '() term1 term2))))))

;; The function pattern-unify-rigid-rigid checks whether both heads are
;; rigid.  If then they are equal, the list rest-unif-pairs is extended
;; by their arguments (which both must be of the same length, since the
;; types are the same, and cannot be null, since the original call was
;; pattern-unify-equality), and pattern-unify-equality is called.  If
;; they are different, #f is returned.  If it is not true that both heads
;; are rigid, pattern-unify-flex-flex is called.

(define (pattern-unify-rigid-rigid
         sig-vars flex-vars forb-vars expr1 expr2 rest-unif-pairs)
  (cond
   ((and (term-form? expr1) (term-form? expr2))
    (let* ((op1 (term-in-app-form-to-final-op expr1))
	   (args1 (term-in-app-form-to-args expr1))
	   (op2 (term-in-app-form-to-final-op expr2))
	   (args2 (term-in-app-form-to-args expr2)))
      (if ;both heads are rigid
       (and (not (and (term-in-var-form? op1)
		      (member (term-in-var-form-to-var op1) flex-vars)))
	    (not (and (term-in-var-form? op2)
		      (member (term-in-var-form-to-var op2) flex-vars))))
       (cond
	((term=? op1 op2) ;both heads are equal
	 (pattern-unify-equality
	  sig-vars flex-vars forb-vars (car args1) (car args2)
	  (append (map list (cdr args1) (cdr args2))
		  rest-unif-pairs)))
	((and (term-in-pair-form? op1)
	      (term-in-pair-form? op2))
	 (let ((left1 (term-in-pair-form-to-left op1))
	       (right1 (term-in-pair-form-to-right op1))
	       (left2 (term-in-pair-form-to-left op2))
	       (right2 (term-in-pair-form-to-right op2)))
	   (pattern-unify-equality
	    sig-vars flex-vars forb-vars left1 left2
	    (cons (list right1 right2) rest-unif-pairs))))
	((and (term-in-lcomp-form? op1)
	      (term-in-lcomp-form? op2))
	 (let ((kernel1 (term-in-lcomp-form-to-kernel op1))
	       (kernel2 (term-in-lcomp-form-to-kernel op2)))
	   (pattern-unify-equality
	    sig-vars flex-vars forb-vars kernel1 kernel2
	    (append (map list args1 args2)
		    rest-unif-pairs))))
	((and (term-in-rcomp-form? op1)
	      (term-in-rcomp-form? op2))
	 (let ((kernel1 (term-in-rcomp-form-to-kernel op1))
	       (kernel2 (term-in-rcomp-form-to-kernel op2)))
	   (pattern-unify-equality
	    sig-vars flex-vars forb-vars kernel1 kernel2
	    (append (map list args1 args2)
		    rest-unif-pairs))))
	((and (term-in-if-form? op1)
	      (term-in-if-form? op2))
	 (let ((test1 (term-in-if-form-to-test op1))
	       (alts1 (term-in-if-form-to-alts op1))
	       (test2 (term-in-if-form-to-test op2))
	       (alts2 (term-in-if-form-to-alts op2)))
	   (pattern-unify-equality
	    sig-vars flex-vars forb-vars test1 test2
	    (append (map list
			 (append alts1 args1)
			 (append alts2 args2))
		    rest-unif-pairs))))
	(else #f))
       (pattern-unify-flex-flex
	sig-vars flex-vars forb-vars expr1 expr2 rest-unif-pairs))))
   ((and (atom-form? expr1) (atom-form? expr2))
    (let ((kernel1 (atom-form-to-kernel expr1))
	  (kernel2 (atom-form-to-kernel expr2)))
      (pattern-unify-equality
       sig-vars flex-vars forb-vars kernel1 kernel2 rest-unif-pairs)))
   ((and (predicate-form? expr1) (predicate-form? expr2))
    (let ((pred1 (predicate-form-to-predicate expr1))
	  (args1 (predicate-form-to-args expr1))
	  (pred2 (predicate-form-to-predicate expr2))
	  (args2 (predicate-form-to-args expr2)))
      (if ;both preds are equal
       (predicate-equal? pred1 pred2)
       (pattern-unify-equality
	sig-vars flex-vars forb-vars (car args1) (car args2)
	(append (map list (cdr args1) (cdr args2))
		rest-unif-pairs))
       #f)))
   ((and (imp-form? expr1) (imp-form? expr2))
    (let ((prem1 (imp-form-to-premise expr1))
	  (concl1 (imp-form-to-conclusion expr1))
	  (prem2 (imp-form-to-premise expr2))
	  (concl2 (imp-form-to-conclusion expr2)))
      (pattern-unify-equality
       sig-vars flex-vars forb-vars prem1 prem2
       (cons (list concl1 concl2) rest-unif-pairs))))
   ((and (and-form? expr1) (and-form? expr2))
    (let ((left1 (and-form-to-left expr1))
	  (right1 (and-form-to-right expr1))
	  (left2 (and-form-to-left expr2))
	  (right2 (and-form-to-right expr2)))
      (pattern-unify-equality
       sig-vars flex-vars forb-vars left1 left2
       (cons (list right1 right2) rest-unif-pairs))))
   ((and (tensor-form? expr1) (tensor-form? expr2))
    (let ((left1 (tensor-form-to-left expr1))
	  (right1 (tensor-form-to-right expr1))
	  (left2 (tensor-form-to-left expr2))
	  (right2 (tensor-form-to-right expr2)))
      (pattern-unify-equality
       sig-vars flex-vars forb-vars left1 left2
       (cons (list right1 right2) rest-unif-pairs))))
   (else #f)))

;; pattern-unify-flex-flex checks whether both heads are flexible.

;; Case 1.  If the heads are equal, the pointwise intersection new-vars
;; of the argument vars is formed.  Then a new variable y' is formed and
;; the new term lambda vars (y' new-vars) is substituted for the flexible
;; variables.  This substitution must also be carried out in
;; rest-unif-pairs. Then a beta0 normalization is done (beta0 because the
;; special form of patterns implies that no new redexes are generated by
;; the beta conversion).  With the result pattern-unify-equality is called.

;; Case 2.  If the heads are different, first check whether one list of
;; argument variables is contained in the other.  If so, the head of the
;; term with more variables is substituted accordingly.  If not, the
;; intersection of the argument variables is computed, a new variable of
;; the corresponding type is formed and both heads are substituted with
;; the new term formed from it.  Then one proceeds as before.  (Note that
;; the check whether one argument list is contained in the other is only
;; done to avoid unneccessary substitution of variables: in this case we
;; can keep the variable with fewer arguments).

;; Otherwise pattern-unify-by-occurs-check-and-pruning is called.

(define (pattern-unify-flex-flex
         sig-vars flex-vars forb-vars term1 term2 rest-unif-pairs)
  ;(display "f")
  (let* ((op1 (term-in-app-form-to-final-op term1))
	 (vars1 (map term-in-var-form-to-var
		     (term-in-app-form-to-args term1)))
	 (op2 (term-in-app-form-to-final-op term2))
	 (vars2 (map term-in-var-form-to-var
		     (term-in-app-form-to-args term2))))
    (if
     (and (term-in-var-form? op1)
	  (member (term-in-var-form-to-var op1) flex-vars))
     (let ((opvar1 (term-in-var-form-to-var op1)))
       (if
	(and (term-in-var-form? op2)
	     (member (term-in-var-form-to-var op2) flex-vars))
	(let ((opvar2 (term-in-var-form-to-var op2)))
	  (if ;equal heads
	   (equal? opvar1 opvar2)
           ;since pattern-unify-equality was called first, the argument
           ;lists must be different.
	   (let* ((new-vars (pointwise-intersection vars1 vars2))
		  (new-type
		   (apply mk-arrow (append (map term-to-type new-vars)
					   (list (term-to-type term1)))))
		  (new-var (type-to-new-var new-type))
		  (new-app-term
		   (apply mk-term-in-app-form
			  (make-term-in-var-form new-var)
			  (map make-term-in-var-form new-vars)))
		  (new-term (apply mk-term-in-abst-form
				   (append vars1 (list new-app-term))))
		  (rho (list (list opvar1 new-term)))
		  (new-flex-vars
		   (append (remove opvar1 flex-vars) (list new-var)))
		  (substituted-rest-unif-pairs
		   (unif-pairs-subst-and-beta0-nf
		    rest-unif-pairs opvar1 new-term)))
	     (append (list rho sig-vars new-flex-vars forb-vars)
		     substituted-rest-unif-pairs))
	   ;now the case of different heads
	   (let ((vars1-in-vars2 (null? (set-minus vars1 vars2)))
		 (vars2-in-vars1 (null? (set-minus vars2 vars1))))
	     (cond
	      (vars1-in-vars2
	       (let* ((new-term (apply mk-term-in-abst-form
				       (append vars2 (list term1))))
		      (rho (list (list opvar2 new-term)))
		      (new-flex-vars (remove opvar2 flex-vars))
		      (substituted-rest-unif-pairs
		       (unif-pairs-subst-and-beta0-nf
			rest-unif-pairs opvar2 new-term)))
		 (append (list rho sig-vars new-flex-vars forb-vars)
			 substituted-rest-unif-pairs)))
	      (vars2-in-vars1
	       (let* ((new-term (apply mk-term-in-abst-form
				       (append vars1 (list term2))))
		      (rho (list (list opvar1 new-term)))
		      (new-flex-vars (remove opvar1 flex-vars))
		      (substituted-rest-unif-pairs
		       (unif-pairs-subst-and-beta0-nf
			rest-unif-pairs opvar1 new-term)))
		 (append (list rho sig-vars new-flex-vars forb-vars)
			 substituted-rest-unif-pairs)))
	      (else ;pruning
	       (let* ((new-vars (intersection vars1 vars2))
		      (new-type (apply mk-arrow
				       (append (map term-to-type new-vars)
					       (list (term-to-type term1)))))
		      (new-var (type-to-new-var new-type))
		      (new-app-term
		       (apply mk-term-in-app-form
			      (make-term-in-var-form new-var)
			      (map make-term-in-var-form new-vars)))
		      (new-term1 (apply mk-term-in-abst-form
					(append vars1 (list new-app-term))))
		      (new-term2 (apply mk-term-in-abst-form
					(append vars2 (list new-app-term))))
		      (rho (list (list opvar1 new-term1)
				 (list opvar2 new-term2)))
		      (new-flex-vars
		       (cons new-var (set-minus flex-vars
						(list opvar1 opvar2))))
		      (substituted-rest-unif-pairs
		       (unif-pairs-subst-and-beta0-nf
			(unif-pairs-subst-and-beta0-nf
			 rest-unif-pairs opvar1 new-term1)
			opvar2 new-term2)))
		 (append (list rho sig-vars new-flex-vars forb-vars)
			 substituted-rest-unif-pairs)))))))
	;case op2 not flexible
	(pattern-unify-by-occurs-check-and-pruning
	 sig-vars flex-vars forb-vars opvar1 vars1 term2 rest-unif-pairs)))
     ;case op1 not flexible
     (if (and (term-in-var-form? op2)
	      (member (term-in-var-form-to-var op2) flex-vars))
	 (pattern-unify-by-occurs-check-and-pruning
	  sig-vars flex-vars forb-vars (term-in-var-form-to-var op2)
	  vars2 term1 rest-unif-pairs)
	 (myerror "pattern-unify-flex-flex applied with heads" op1 op2)))))

;; Here we have used some auxiliary functions:

(define (pointwise-intersection-wrt equality? list1 list2)
  (do ((l1 list1 (cdr l1))
       (l2 list2 (cdr l2))
       (res '() (if (equality? (car l1) (car l2)) (cons (car l1) res) res)))
      ((or (null? l1) (null? l2)) (reverse res))))

(define (pointwise-intersection list1 list2)
  (pointwise-intersection-wrt equal? list1 list2))

(define (pointwise-intersecq list1 list2)
  (pointwise-intersection-wrt eq? list1 list2))

(define (pointwise-intersecv list1 list2)
  (pointwise-intersection-wrt eqv? list1 list2))

(define (term-substitute-and-beta0-nf term subst)
  (if
   (null? subst)
   term
   (if
    (term-in-abst-form? term)
    (let* ((var (term-in-abst-form-to-var term))
	   (kernel (term-in-abst-form-to-kernel term))
	   (vars (map car subst))
	   (active-vars (intersection vars (term-to-free term)))
	   (active-subst
	    (do ((l subst (cdr l))
		 (res '() (if (member (caar l) active-vars)
			      (cons (car l) res)
			      res)))
		((null? l) (reverse res))))
	   (active-terms (map cadr active-subst)))
      (if (member var (apply union (map term-to-free active-terms)))
	  (let ((new-var (var-to-new-var var)))
	    (make-term-in-abst-form
	     new-var
	     (term-substitute-and-beta0-nf
	      kernel (cons (list var (make-term-in-var-form new-var))
			   active-subst))))
	  (make-term-in-abst-form
	   var (term-substitute-and-beta0-nf kernel active-subst))))
    (let* ((op (term-in-app-form-to-final-op term))
	   (args (term-in-app-form-to-args term))
	   (info (if (term-in-var-form? op)
		     (assoc (term-in-var-form-to-var op) subst)
		     #f)))
      (if ;term of the form yr1...rm with y left in subst
       info
       (let* ((kernel-and-vars
	       (term-in-abst-form-to-kernel-and-vars (cadr info)))
	      (kernel (car kernel-and-vars))
	      (vars (cdr kernel-and-vars))
	      (subst (do ((rs args (cdr rs))
			  (vs vars (cdr vs))
			  (res '() (cons (list (car vs) (car rs)) res)))
			 ((or (null? rs) (null? vs)) res)))
	      (new-kernel (term-substitute-and-beta0-nf kernel subst))
	      (n (length vars))
	      (m (length args)))
	 (if
	  (<= m n)
	  (apply mk-term-in-abst-form
		 (append (list-tail vars m) (list new-kernel)))
	  (apply mk-term-in-app-form (cons new-kernel (list-tail args n)))))
       ;; otherwise substitution as usual
       (case (tag term)
	 ((term-in-var-form term-in-const-form) term)
	 ((term-in-app-form)
	  (make-term-in-app-form
	   (term-substitute-and-beta0-nf
	    (term-in-app-form-to-op term) subst)
	   (term-substitute-and-beta0-nf
	    (term-in-app-form-to-arg term) subst)))
	 ((term-in-pair-form)
	  (make-term-in-pair-form
	   (term-substitute-and-beta0-nf
	    (term-in-pair-form-to-left term) subst)
	   (term-substitute-and-beta0-nf
	    (term-in-pair-form-to-right term) subst)))
	 ((term-in-lcomp-form)
	  (make-term-in-lcomp-form
	   (term-substitute-and-beta0-nf
	    (term-in-lcomp-form-to-kernel term) subst)))
	 ((term-in-rcomp-form)
	  (make-term-in-rcomp-form
	   (term-substitute-and-beta0-nf
	    (term-in-rcomp-form-to-kernel term) subst)))
	 ((term-in-if-form)
	  (apply
	   make-term-in-if-form
	   (term-substitute-and-beta0-nf
	    (term-in-if-form-to-test term) subst)
	   (map (lambda (x) (term-substitute-and-beta0-nf x subst))
		(term-in-if-form-to-alts term))
	   (term-in-if-form-to-rest term)))
	 (else (myerror "term-substitute-and-beta0-nf" "term expected"
			term))))))))

(define (term-subst-and-beta0-nf term var term1)
  (term-substitute-and-beta0-nf term (list (list var term1))))

(define (unif-pairs-subst-and-beta0-nf unif-pairs var term)
  (do ((ps unif-pairs (cdr ps))
       (res '()
	    (let ((expr1 (caar ps))
		  (expr2 (cadar ps)))
	      (cons (list (cond ((term-form? expr1)
				 (term-subst-and-beta0-nf expr1 var term))
				((formula-form? expr1)
				 (formula-subst-and-beta0-nf expr1 var term))
				(else
				 (myerror "unif-pairs-subst-and-beta0-nf"
					  "term or formula expected" expr1)))
			  (cond ((term-form? expr2)
				 (term-subst-and-beta0-nf expr2 var term))
				((formula-form? expr2)
				 (formula-subst-and-beta0-nf expr2 var term))
				(else
				 (myerror "unif-pairs-subst-and-beta0-nf"
					  "term or formula expected" expr2))))
		    res))))
      ((null? ps) (reverse res))))

;; pattern-unify-by-occurs-check-and-pruning deals with a situation
;; yx1...xn=r not of the form flex-flex.  First search r for a ``critical
;; subterm'', i.e. a subterm that either
;; - has head y, or
;; - contains an unallowed dependency, i.e. an occurrence (as argument of
;;   a flexible variable) of a variable not among x1...xn that is free
;;   in the total term.
;; If a critical subterm starting with y is found, return #f (occurs check).
;; If a critical subterm with unallowed dependencies is found, delete these
;; dependencies by introducing a new flexible variable new-var and call
;; pattern-unify-by-occurs-check-and-pruning again.  If there is no
;; critical subterm, check whether new-term := [x1,...,xn]r has a free
;; occurrence of a forbidden variable.  If so, return #f, and otherwise
;; return the extended substitution.

(define (pattern-unify-by-occurs-check-and-pruning
         sig-vars flex-vars forb-vars head vars rigid-term rest-unif-pairs)
  ;(display "p")
  (let ((test (term-to-critical-subterm-as-list-with-type
               flex-vars head vars rigid-term)))
    (if ;critical subterm found
     (pair? test)
     (let* ((type (car test))
	    (h (cadr test))
	    (args (cddr test)))
       (if ;occurs check
	(equal? head h)
	#f
	(let* ((new-vars (intersection args vars))
	       (new-type (apply mk-arrow (append (map term-to-type new-vars)
						 (list type))))
	       (new-var (type-to-new-var new-type))
	       (new-app-term
		(apply mk-term-in-app-form
		       (make-term-in-var-form new-var)
		       (map make-term-in-var-form new-vars)))
	       (new-term
		(apply mk-term-in-abst-form (append args (list new-app-term))))
	       (rho (list (list h new-term)))
	       (new-flex-vars (cons new-var (remove h flex-vars)))
	       (substituted-rest-unif-pairs
		(unif-pairs-subst-and-beta0-nf rest-unif-pairs h new-term))
	       (app-term
		(apply mk-term-in-app-form
		       (make-term-in-var-form head)
		       (map make-term-in-var-form vars)))
	       (substituted-rigid-term
		(term-subst-and-beta0-nf rigid-term h new-term)))
	  (append (list rho sig-vars new-flex-vars forb-vars)
		  (cons (list app-term substituted-rigid-term)
			substituted-rest-unif-pairs)))))
     ;; no critical subterm found
     (let ((new-term (apply mk-term-in-abst-form
			    (append vars (list rigid-term)))))
       (if (pair? (intersection (term-to-free new-term) forb-vars))
	   #f
	   (let* ((rho (list (list head new-term)))
		  (new-flex-vars (remove head flex-vars))
		  (substituted-rest-unif-pairs
		   (unif-pairs-subst-and-beta0-nf
		    rest-unif-pairs head new-term)))
	     (append (list rho sig-vars new-flex-vars forb-vars)
		     substituted-rest-unif-pairs)))))))

;; term-to-critical-subterm-as-list-with-type gets flex-vars head vars term
;; as input, with term in beta normal form.  It returns the first
;; critical subterm with its type, if there is any, and the empty list
;; otherwise.  As before a subterm is critical if it starts with head y
;; or contains unallowed dependencies.  Examples:
;; y x1 x2 = a([x3](z x3 x1 x x2))  => (obj->obj z x3 x1 x)
;; y x1 x2 = b([x3](y x3))          => (obj->obj->obj y)
;; y x1 x2 = a([x3](z x3 x1 x2))    => ()

(define (term-to-critical-subterm-as-list-with-type
         flex-vars head vars term)
  (if
   (term-in-abst-form? term)
   (term-to-critical-subterm-as-list-with-type
    flex-vars head (cons (term-in-abst-form-to-var term) vars)
    (term-in-abst-form-to-kernel term))
   (let* ((op (term-in-app-form-to-final-op term))
	  (args (term-in-app-form-to-args term)))
     (if ;critical subterm with operator head found
      (and (term-in-var-form? op)
	   (equal? (term-in-var-form-to-var op) head))
      (list (term-to-type op) (term-in-var-form-to-var op))
      (let* ((op-flex? (and (term-in-var-form? op)
			    (member (term-in-var-form-to-var op) flex-vars)))
	     (argvars (if op-flex? (map term-in-var-form-to-var args))))
	(if ;critical subterm with unallowed dependencies found
	 (and op-flex? (pair? (set-minus argvars vars)))
	 (let ((opvar (term-in-var-form-to-var op)))
	   (do ((x argvars (cdr x))
		(type (term-to-type op) (arrow-form-to-val-type type))
		(l (list opvar) (cons (car x) l)))
	       ((not (member (car x) vars)) ;critical subterm found
		(cons (arrow-form-to-val-type type)
		      (reverse (cons (car x) l))))))
	 (if op-flex?
	     #f ;continue search
	     (let aux ((x args))
	       (if (null? x)
		   #f ;continue search
		   (let ((prev (term-to-critical-subterm-as-list-with-type
				flex-vars head vars (car x))))
		     (if (pair? prev)
			 prev
			 (aux (cdr x)))))))))))))

;; 6-11. Huets unification algorithm
;; =================================

;; Huets unification algorithm needs: simpl, match.  simpl needs
;; rigid heads and decomposes the problem to the arguments.  A term is
;; rigid if its head is either a constant or a bound variable.

;; match gets a flexible and a rigid argument.  It consists of two
;; parts: imitation and projections.

;; Imitation gets f r1 ... rm and A s1 ... sn as arguments.  It
;; produces a substitution, for the flexible head f: f mapsto
;; lambda_xs(A(hs xs)).  This only works if A is a constant.

;; Projection gets f r1 ... rm and A s1 ... sn as arguments.  There are
;; m projections;; each of these pulls one of the rs in front.  So the
;; i-th projection maps f to lambda_{x1...xm}(xi (hs xs)), where the
;; types are as follows: Let beta_i = alpha_{i1} => ... => alpha{i k_i}
;; => iota.  f : beta_1 => ... => beta_m => iota.  ri, xi : beta_i.  hj
;; : beta_1 => ... => beta_m => alpha_{i j}.

;; Notice that for matching f r1 ... rm and A s1 ... sn, up to one
;; imitation and m projections is possible.

;; Organization: Work with lists of unification pairs.  Take the first
;; one, say (r s).  First simp decomposes the structure if possible, or
;; stops with failure.  Then match gets a flex rigid pair.  It calls
;; imitate and then all projections.  For each answer it gets it
;; produces a new unification problem by applying the substitution to
;; all unif-pairs.  Then it recursively calls simpl for each of these,
;; and generates a "match tree" in this way.  The subsitution needs to
;; be carried along (on each path separately), which will finally yield
;; the desired unifier.

(define MATCH-TREE-BOUND 100)

(define (huet-unifiers sig-opvars flex-opvars forb-vars .
		       opt-ignore-deco-flag-and-unif-pairs)
  (if (null? opt-ignore-deco-flag-and-unif-pairs)
      (myerror "huet-unifiers" "non null unif-pairs expected"))
  (let* ((no-flag? (pair? (car opt-ignore-deco-flag-and-unif-pairs)))
	 (ignore-deco-flag (if no-flag? #f
			       (car opt-ignore-deco-flag-and-unif-pairs)))
	 (unif-pairs (if no-flag? opt-ignore-deco-flag-and-unif-pairs
			 (cdr opt-ignore-deco-flag-and-unif-pairs)))
	 (unif-results ;((theta1 sig-opvars1 flex-opvars1 forb-vars1) ...)
	  (huet-unifiers-init
	   sig-opvars flex-opvars forb-vars ignore-deco-flag unif-pairs
	   '() empty-subst MATCH-TREE-BOUND))
	 (restr-unif-results
	  (map (lambda (res)
		 (let ((subst (car res))
		       (state (cdr res)))
		   (cons (restrict-substitution-to-args subst flex-opvars)
			 state)))
	       unif-results)))
    restr-unif-results))

(define (huet-unifiers-init sig-opvars flex-opvars forb-vars ignore-deco-flag
			    unif-pairs flex-flex-pairs opsubst bd)
  (if (null? unif-pairs) ;solution found
      (let* ((exprs (apply append flex-flex-pairs))
	     (varterms (list-transform-positive exprs term-in-var-form?))
	     (vars (map term-in-var-form-to-var varterms))
	     (pvars (list-transform-positive exprs pvar-form?))
	     (types (map var-to-type vars))
	     (groundtypes
	      (apply union (map type-to-final-groundtypes types)))
	     (new-flex-opvars (map type-to-new-var groundtypes))
	     (groundtype-var-alist
	      (map (lambda (type var) (list type var))
		   groundtypes new-flex-opvars))
	     (can-terms
	      (map (lambda (x) (type-to-canonical-term x groundtype-var-alist))
		   types))
	     (can-osubst (map (lambda (var term) (list var term))
			      vars can-terms))
	     (cterms (map pvar-to-cterm pvars))
	     (can-psubst (map (lambda (pvar cterm) (list pvar cterm))
			      pvars cterms))
	     (can-opsubst (append can-osubst can-psubst)))
	(list
	 (list (compose-substitutions-and-beta-nf opsubst can-opsubst)
	       sig-opvars (append flex-opvars new-flex-opvars) forb-vars)))
      (let ((expr1 (caar unif-pairs))
	    (expr2 (cadar unif-pairs))
	    (rest-unif-pairs (cdr unif-pairs)))
	(huet-unifiers-equality
	 sig-opvars flex-opvars forb-vars ignore-deco-flag
	 expr1 expr2 rest-unif-pairs flex-flex-pairs opsubst bd))))

(define (huet-unifiers-equality
	 sig-opvars flex-opvars forb-vars ignore-deco-flag
	 expr1 expr2 rest-unif-pairs flex-flex-pairs opsubst bd)
  (if (or (and (term-form? expr1) (term-form? expr2) (term=? expr1 expr2))
	  (and (formula-form? expr1) (formula-form? expr2)
	       (formula=? expr1 expr2 ignore-deco-flag)))
      (huet-unifiers-init sig-opvars flex-opvars forb-vars ignore-deco-flag
			  rest-unif-pairs flex-flex-pairs opsubst bd)
      (huet-unifiers-xi sig-opvars flex-opvars forb-vars ignore-deco-flag
			expr1 expr2
			rest-unif-pairs flex-flex-pairs opsubst bd)))

(define (huet-unifiers-xi
	 sig-opvars flex-opvars forb-vars ignore-deco-flag
	 expr1 expr2 rest-unif-pairs flex-flex-pairs opsubst bd)
  (cond
   ((and (term-form? expr1) (term-form? expr2)
	 (equal? (term-to-type expr1) (term-to-type expr2)))
    (let ((type (term-to-type expr1)))
      (case (tag type)
	((tvar alg tconst star)
	 (huet-unifiers-rigid-rigid
	  sig-opvars flex-opvars forb-vars ignore-deco-flag
	  expr1 expr2 rest-unif-pairs flex-flex-pairs opsubst bd))
	((arrow)
	 (if (and (term-in-abst-form? expr1) (term-in-abst-form? expr2)
		  (let ((var1 (term-in-abst-form-to-var expr1))
			(kernel1 (term-in-abst-form-to-kernel expr1))
			(var2 (term-in-abst-form-to-var expr2))
			(kernel2 (term-in-abst-form-to-kernel expr2)))
		    (and (equal? var1 var2)
			 (not (member var1 (append sig-opvars
						   flex-opvars
						   forb-vars))))))
	     (let ((var1 (term-in-abst-form-to-var expr1))
		   (kernel1 (term-in-abst-form-to-kernel expr1))
		   (kernel2 (term-in-abst-form-to-kernel expr2)))
	       (huet-unifiers-xi
		sig-opvars flex-opvars (cons var1 forb-vars) ignore-deco-flag
		kernel1 kernel2 rest-unif-pairs flex-flex-pairs opsubst bd))
	     (let* ((arg-type (arrow-form-to-arg-type type))
		    (var (type-to-new-var arg-type))
		    (kernel1
		     (if (term-in-abst-form? expr1)
			 (term-subst (term-in-abst-form-to-kernel expr1)
				     (term-in-abst-form-to-var expr1)
				     (make-term-in-var-form var))
			 (make-term-in-app-form
			  expr1 (make-term-in-var-form var))))
		    (kernel2
		     (if (term-in-abst-form? expr2)
			 (term-subst (term-in-abst-form-to-kernel expr2)
				     (term-in-abst-form-to-var expr2)
				     (make-term-in-var-form var))
			 (make-term-in-app-form
			  expr2 (make-term-in-var-form var)))))
	       (huet-unifiers-xi
		sig-opvars flex-opvars (cons var forb-vars) ignore-deco-flag
		kernel1 kernel2 rest-unif-pairs flex-flex-pairs opsubst bd))))
	(else (myerror "huet-unifiers-xi" "type expected" type)))))
   ((and (term-form? expr1) (term-form? expr2)
	 (not (equal? (term-to-type expr1) (term-to-type expr2))))
    '())
   ((and (formula-form? expr1) (formula-form? expr2))
    (huet-unifiers-rigid-rigid
     sig-opvars flex-opvars forb-vars ignore-deco-flag
     expr1 expr2 rest-unif-pairs flex-flex-pairs opsubst bd))
   (else '())))

;; The function huet-unifiers-rigid-rigid checks whether both heads are
;; rigid.  If the expressions are terms and the heads are equal, the
;; list rest-unif-pairs is extended by their arguments (which both must
;; be of the same length, since the types are the same, and cannot be
;; null, since the original call was huet-unifiers-equality), and
;; huet-unifiers-equality is called.  If the heads are different, '()
;; is returned.  If the expressions are formulas and the heads are
;; idpredconsts with the same name and types but not of bicon or quant
;; form, then rest-unif-pairs is extended by param-cterm-unif-pairs and
;; arg-unif-pairs and huet-unifiers-init is called.  If name or types
;; are different, '() is returned.  If it is not true that both heads
;; are rigid, huet-unifiers-flex-flex is called.

(define (huet-unifiers-rigid-rigid
	 sig-opvars flex-opvars forb-vars ignore-deco-flag expr1 expr2
	 rest-unif-pairs flex-flex-pairs opsubst bd)
  (cond
   ((and (term-form? expr1) (term-form? expr2))
    (let ((op1 (term-in-app-form-to-final-op expr1))
	  (args1 (term-in-app-form-to-args expr1))
	  (op2 (term-in-app-form-to-final-op expr2))
	  (args2 (term-in-app-form-to-args expr2)))
      (if ;both heads are rigid
       (and (or (not (term-in-var-form? op1))
		(not (member (term-in-var-form-to-var op1) flex-opvars)))
	    (or (not (term-in-var-form? op2))
		(not (member (term-in-var-form-to-var op2) flex-opvars))))
       (cond
	((term=? op1 op2) ;both heads are equal
	 (huet-unifiers-equality
	  sig-opvars flex-opvars forb-vars ignore-deco-flag
	  (car args1) (car args2)
	  (append (map list args1 args2)
		  rest-unif-pairs)
	  flex-flex-pairs opsubst bd))
	((and (term-in-pair-form? op1) (term-in-pair-form? op2))
	 (let ((left1 (term-in-pair-form-to-left op1))
	       (right1 (term-in-pair-form-to-right op1))
	       (left2 (term-in-pair-form-to-left op2))
	       (right2 (term-in-pair-form-to-right op2)))
	   (huet-unifiers-equality
	    sig-opvars flex-opvars forb-vars ignore-deco-flag
	    left1 left2 (cons (list right1 right2) rest-unif-pairs)
	    flex-flex-pairs opsubst bd)))
	((and (term-in-lcomp-form? op1) (term-in-lcomp-form? op2))
	 (let ((kernel1 (term-in-lcomp-form-to-kernel op1))
	       (kernel2 (term-in-lcomp-form-to-kernel op2)))
	   (huet-unifiers-equality
	    sig-opvars flex-opvars forb-vars ignore-deco-flag
	    kernel1 kernel2
	    (append (map list args1 args2)
		    rest-unif-pairs)
	    flex-flex-pairs opsubst bd)))
	((and (term-in-rcomp-form? op1) (term-in-rcomp-form? op2))
	 (let ((kernel1 (term-in-rcomp-form-to-kernel op1))
	       (kernel2 (term-in-rcomp-form-to-kernel op2)))
	   (huet-unifiers-equality
	    sig-opvars flex-opvars forb-vars ignore-deco-flag
	    kernel1 kernel2
	    (append (map list args1 args2)
		    rest-unif-pairs)
	    flex-flex-pairs opsubst bd)))
	((and (term-in-if-form? op1)
	      (term-in-if-form? op2)
	      (= (length args1) (length args2)))
	 (let ((test1 (term-in-if-form-to-test op1))
	       (alts1 (term-in-if-form-to-alts op1))
	       (test2 (term-in-if-form-to-test op2))
	       (alts2 (term-in-if-form-to-alts op2)))
	   (huet-unifiers-equality
	    sig-opvars flex-opvars forb-vars ignore-deco-flag test1 test2
	    (append (map list
			 (append alts1 args1)
			 (append alts2 args2))
		    rest-unif-pairs)
	    flex-flex-pairs opsubst bd)))
	(else '()))
       (huet-unifiers-flex-flex
	sig-opvars flex-opvars forb-vars ignore-deco-flag expr1 expr2
	rest-unif-pairs flex-flex-pairs opsubst bd))))
   ((and (formula-form? expr1) (formula-form? expr2))
    (if	;both heads are rigid
     (and (or (atom-form? expr1)
	      (and (predicate-form? expr1)
		   (let ((pred1 (predicate-form-to-predicate expr1)))
		     (or (not (pvar-form? pred1))
			 (not (member pred1 flex-opvars)))))
	      (bicon-form? expr1)
	      (quant-form? expr1))
	  (or (atom-form? expr2)
	      (and (predicate-form? expr2)
		   (let ((pred2 (predicate-form-to-predicate expr2)))
		     (or (not (pvar-form? pred2))
			 (not (member pred2 flex-opvars)))))
	      (bicon-form? expr2)
	      (quant-form? expr2)))
     (cond
      ((and (atom-form? expr1) (atom-form? expr2))
       (let ((kernel1 (atom-form-to-kernel expr1))
	     (kernel2 (atom-form-to-kernel expr2)))
	 (huet-unifiers-equality
	  sig-opvars flex-opvars forb-vars ignore-deco-flag kernel1 kernel2
	  rest-unif-pairs flex-flex-pairs opsubst bd)))
      ((and (bicon-form? expr1) (bicon-form? expr2))
       (let* ((bicon1 (bicon-form-to-bicon expr1))
	      (left1 (bicon-form-to-left expr1))
	      (right1 (bicon-form-to-right expr1))
	      (bicon2 (bicon-form-to-bicon expr2))
	      (left2 (bicon-form-to-left expr2))
	      (right2 (bicon-form-to-right expr2))
	      (bicon-eq-test
	       (or (eq? bicon1 bicon2)
		   (and ignore-deco-flag
			(case bicon1
			  ((imp impnc) (memq bicon2 '(imp impnc)))
			  ((andd andr andnc)
			   (memq bicon2 '(andd andr andnc)))
			  ((ord orl orr oru) (memq bicon2 '(ord orl orr oru)))
			  (else #f))))))
	 (if
	  bicon-eq-test
	  (huet-unifiers-equality
	   sig-opvars flex-opvars forb-vars ignore-deco-flag left1 left2
	   (cons (list right1 right2) rest-unif-pairs)
	   flex-flex-pairs opsubst bd)
	  '())))
      ((and (quant-form? expr1) (quant-form? expr2))
       (let* ((quant1 (quant-form-to-quant expr1))
	      (vars1 (quant-form-to-vars expr1))
	      (kernel1 (quant-form-to-kernel expr1))
	      (quant2 (quant-form-to-quant expr2))
	      (vars2 (quant-form-to-vars expr2))
	      (kernel2 (quant-form-to-kernel expr2))
	      (quant-eq-test
	       (or (eq? quant1 quant2)
		   (and ignore-deco-flag
			(case quant1
			  ((all allnc) (memq quant2 '(all allnc)))
			  ((exd exl exr exnc) (memq quant2 '(exd exl exr exnc)))
			  ((exdt exlt exrt exnct)
			   (memq quant2 '(exdt exlt exrt exnct)))
			  (else #f))))))
	 (if
	  quant-eq-test ;else '()
	  (cond
	   ((equal? vars1 vars2)
	    (let* ((info (or (pair? (intersection sig-opvars vars1))
			     (pair? (intersection flex-opvars vars1))
			     (pair? (intersection forb-vars vars1))))
		   (new-vars (if info (map var-to-new-var vars1) vars1))
		   (var-subst (make-substitution
			       vars1 (map make-term-in-var-form new-vars)))
		   (new-kernel1
		    (if info
			(formula-substitute kernel1 var-subst)
			kernel1))
		   (new-kernel2
		    (if info
			(formula-substitute kernel2 var-subst)
			kernel2)))
	      (huet-unifiers-equality
	       sig-opvars flex-opvars (append forb-vars new-vars)
	       ignore-deco-flag
	       new-kernel1 new-kernel2 rest-unif-pairs flex-flex-pairs
	       opsubst bd)))
	   ((and (equal? (map var-to-type vars1) (map var-to-type vars2))
		 (equal? (map var-to-t-deg vars1) (map var-to-t-deg vars2)))
	    (let* ((new-vars (map var-to-new-var vars1))
		   (var-subst1 (make-substitution
				vars1 (map make-term-in-var-form new-vars)))
		   (new-kernel1 (formula-substitute kernel1 var-subst1))
		   (var-subst2 (make-substitution
				vars2 (map make-term-in-var-form new-vars)))
		   (new-kernel2 (formula-substitute kernel2 var-subst2)))
	      (huet-unifiers-equality
	       sig-opvars flex-opvars (append forb-vars new-vars)
	       ignore-deco-flag
	       new-kernel1 new-kernel2 rest-unif-pairs flex-flex-pairs
	       opsubst bd)))
	   (else '()))
	  '())))
      ((and (predicate-form? expr1) (predicate-form? expr2)
	    (idpredconst-form? (predicate-form-to-predicate expr1))
	    (idpredconst-form? (predicate-form-to-predicate expr2)))
       (let* ((idpc1 (predicate-form-to-predicate expr1))
	      (args1 (predicate-form-to-args expr1))
	      (name1 (idpredconst-to-name idpc1))
	      (types1 (idpredconst-to-types idpc1))
	      (cterms1 (idpredconst-to-cterms idpc1))
	      (idpc2 (predicate-form-to-predicate expr2))
	      (args2 (predicate-form-to-args expr2))
	      (name2 (idpredconst-to-name idpc2))
	      (types2 (idpredconst-to-types idpc2))
	      (cterms2 (idpredconst-to-cterms idpc2)))
	 (if ;else '()
	  (and (string=? name1 name2) (equal? types1 types2))
	  (let ((param-cterm-unif-pairs
		 (map
		  (lambda (cterm1 cterm2) ;through cterms1, cterms2
		    (let* ((vars1 (cterm-to-vars cterm1))
			   (fla1 (cterm-to-formula cterm1))
			   (vars2 (cterm-to-vars cterm2))
			   (fla2 (cterm-to-formula cterm2)))
		      (if
		       (equal? vars1 vars2)
		       (let* ((info (or
				     (pair? (intersection sig-opvars vars1))
				     (pair? (intersection flex-opvars vars1))
				     (pair? (intersection forb-vars vars1))))
			      (new-vars
			       (if info (map var-to-new-var vars1) vars1))
			      (var-subst
			       (make-substitution
				vars1 (map make-term-in-var-form new-vars)))
			      (new-fla1 (if info
					    (formula-substitute fla1 var-subst)
					    fla1))
			      (new-fla2 (if info
					    (formula-substitute fla2 var-subst)
					    fla2)))
			 (list new-fla1 new-fla2))
					;else types equal, t-degs do not matter
		       (let* ((new-vars (map var-to-new-var vars1))
			      (var-subst1
			       (make-substitution
				vars1 (map make-term-in-var-form new-vars)))
			      (new-fla1 (formula-substitute fla1 var-subst1))
			      (var-subst2
			       (make-substitution
				vars2 (map make-term-in-var-form new-vars)))
			      (new-fla2 (formula-substitute fla2 var-subst2)))
			 (list new-fla1 new-fla2)))))
		  cterms1 cterms2))
		(arg-unif-pairs (map (lambda (arg1 arg2) (list arg1 arg2))
				     args1 args2)))
	    (huet-unifiers-init
	     sig-opvars flex-opvars forb-vars ignore-deco-flag
	     (append param-cterm-unif-pairs arg-unif-pairs rest-unif-pairs)
	     flex-flex-pairs opsubst bd))
	  '())))
      ((and (predicate-form? expr1) (predicate-form? expr2))
       (let ((pred1 (predicate-form-to-predicate expr1))
	     (args1 (predicate-form-to-args expr1))
	     (pred2 (predicate-form-to-predicate expr2))
	     (args2 (predicate-form-to-args expr2)))
	 (if ;both preds are equal, or Total and TotalNat
	  (or (predicate-equal? pred1 pred2)
	      (and (totality-pred-form? pred1) (totality-pred-form? pred2)))
	  (huet-unifiers-init
	   sig-opvars flex-opvars forb-vars ignore-deco-flag
	   (append (map (lambda (arg1 arg2) (list arg1 arg2)) args1 args2)
		   rest-unif-pairs)
	   flex-flex-pairs opsubst bd)
	  '())))
      (else '()))
					;not both heads are rigid
     (huet-unifiers-flex-flex
      sig-opvars flex-opvars forb-vars ignore-deco-flag expr1 expr2
      rest-unif-pairs flex-flex-pairs opsubst bd)))
   (else '())))

(define (totality-pred-form? pred)
  (or (and (predconst-form? pred)
	   (string=? "Total" (predconst-to-name pred)))
      (and (idpredconst-form? pred)
	   (initial-substring? "Total" (idpredconst-to-name pred)))))

;; (totality-pred-form? (predicate-form-to-predicate (pf "Total n")))
;; (totality-pred-form? (predicate-form-to-predicate (pf "TotalNat n")))

(define (huet-unifiers-flex-flex
	 sig-opvars flex-opvars forb-vars ignore-deco-flag expr1 expr2
	 rest-unif-pairs flex-flex-pairs opsubst bd)
  (let* ((op1 (if (term-form? expr1)
		  (term-in-app-form-to-final-op expr1)
		  (predicate-form-to-predicate expr1)))
	 (args1 (if (term-form? expr1)
		    (term-in-app-form-to-args expr1)
		    (predicate-form-to-args expr1)))
	 (op2 (if (term-form? expr2)
		  (term-in-app-form-to-final-op expr2)
		  (predicate-form-to-predicate expr2)))
	 (args2 (if (term-form? expr2)
		    (term-in-app-form-to-args expr2)
		    (predicate-form-to-args expr2)))
	 (expr1-is-flex?
	  (or (and (term-in-var-form? op1)
		   (member (term-in-var-form-to-var op1) flex-opvars))
	      (and (pvar-form? op1)
		   (member op1 flex-opvars))))
	 (expr2-is-flex?
	  (or (and (term-in-var-form? op2)
		   (member (term-in-var-form-to-var op2) flex-opvars))
	      (and (pvar-form? op2)
		   (member op2 flex-opvars)))))
    (cond
     ((and expr1-is-flex? expr2-is-flex?)
      (huet-unifiers-init
       sig-opvars flex-opvars forb-vars ignore-deco-flag
       rest-unif-pairs (cons (list expr1 expr2) flex-flex-pairs) opsubst bd))
     (expr2-is-flex? ;but expr1 is rigid
      (huet-unifiers-match
       sig-opvars flex-opvars forb-vars ignore-deco-flag
       expr2 expr1 rest-unif-pairs flex-flex-pairs opsubst bd))
     ;; (else ;expr1 is flex and expr2 rigid
     ;;  (huet-unifiers-match
     ;;   sig-opvars flex-opvars forb-vars ignore-deco-flag
     ;;   expr1 expr2 rest-unif-pairs flex-flex-pairs opsubst bd))
     (expr1-is-flex? ;expr1 is flex and expr2 rigid
      (huet-unifiers-match
       sig-opvars flex-opvars forb-vars ignore-deco-flag
       expr1 expr2 rest-unif-pairs flex-flex-pairs opsubst bd))
     (else '()))))

;; In huet-unifiers-match expr1 is flexible and expr2 is rigid.

(define (huet-unifiers-match
	 sig-opvars flex-opvars forb-vars ignore-deco-flag
	 expr1 expr2 rest-unif-pairs flex-flex-pairs opsubst bd)
  (if
   (zero? bd)
   (begin (display-comment "MATCH-TREE-BOUND reached")
	  (newline)
	  '())
   (let* ((flex-head
	   (if (term-form? expr1)
	       (term-in-var-form-to-var (term-in-app-form-to-final-op expr1))
	       (predicate-form-to-predicate expr1)))
	  (betas (if (term-form? expr1)
		     (arrow-form-to-arg-types (var-to-type flex-head))
		     (arity-to-types (pvar-to-arity flex-head))))
	  (xs (map (lambda (type) (type-to-new-partial-var type)) betas))
	  (proj-substs
	   (if
	    (term-form? expr1)
	    (let* ((n (length betas))
		   (one-to-n (do ((i 1 (+ i 1))
				  (res '() (cons i res)))
				 ((< n i) (reverse res))))
		   (relevant-is (list-transform-positive one-to-n
				  (lambda (i)
				    (equal? (term-to-type expr2)
					    (arrow-form-to-final-val-type
					     (list-ref betas (- i 1))))))))
	      (map (lambda (i) (huet-project i flex-head betas xs))
		   relevant-is))
	    '()))
	  (imit-opsubst
	   (if (term-form? expr1)
	       (if (term-in-if-form? expr2)
		   (huet-imitate-if-term
		    flex-head
		    (cons (term-to-type (term-in-if-form-to-test expr2))
			  (map term-to-type (term-in-if-form-to-alts expr2)))
		    betas xs)
		   (huet-imitate-term
		    flex-head (term-in-app-form-to-final-op expr2) betas xs))
	       (huet-imitate-formula flex-head expr2 betas xs)))
	  (rigid-head-is-a-forbidden-variable?
	   (if (term-form? expr1)
	       (member (term-in-app-form-to-final-op expr2)
		       (map make-term-in-var-form forb-vars))
	       (and (predicate-form? expr1)
		    (member (predicate-form-to-predicate expr1)
			    forb-vars))))
	  (opsubsts ;determines the branching of the match tree
	   (if rigid-head-is-a-forbidden-variable?
	       proj-substs
	       (cons imit-opsubst proj-substs)))
	  (vals (map cadr (apply append opsubsts)))
	  (val-terms (list-transform-positive vals term-form?))
	  (val-cterms (list-transform-positive vals cterm-form?))
	  (sig-vars (list-transform-positive sig-opvars var-form?))
	  (sig-pvars (list-transform-positive sig-opvars pvar-form?))
	  (new-flex-vars
	   (set-minus (apply union (append (map term-to-free val-terms)
					   (map cterm-to-free val-cterms)))
		      sig-vars))
	  (new-flex-pvars
	   (set-minus (apply union (map formula-to-pvars
					(map cterm-to-formula val-cterms)))
		      sig-pvars))
	  (new-flex-opvars (append new-flex-vars new-flex-pvars))
	  (subst-unif-pairs-list
	   (map (lambda (x) (unif-pairs-substitute-and-beta-nf
			     (cons (list expr1 expr2) rest-unif-pairs) x))
		opsubsts))
	  (subst-flex-flex-pairs-list
	   (map (lambda (x)
		  (unif-pairs-substitute-and-beta-nf flex-flex-pairs x))
		opsubsts))
	  (new-subst-list
	   (map (lambda (x) (compose-substitutions-and-beta-nf opsubst x))
		opsubsts)))
     (apply append
	    (map (lambda (subst-unif-pairs subst-flex-flex-pairs new-subst)
		   (huet-unifiers-init
		    sig-opvars (append flex-opvars new-flex-opvars) forb-vars
		    ignore-deco-flag
		    (append subst-unif-pairs subst-flex-flex-pairs)
		    '() new-subst (- bd 1)))
		 subst-unif-pairs-list
		 subst-flex-flex-pairs-list
		 new-subst-list)))))

(define (huet-imitate-if-term flex-head alphas betas xs)
  (let* ((hs (map (lambda (type)
		    (type-to-new-partial-var
		     (apply mk-arrow (append betas (list type)))))
		  alphas))
	 (args ;(hs xs)
	  (map (lambda (h) (apply mk-term-in-app-form
				  (make-term-in-var-form h)
				  (map make-term-in-var-form xs)))
	       hs))
	 (valterm ;lambda_xs[if (hs xs)]
	  (apply mk-term-in-abst-form
		 (append xs (list (make-term-in-if-form
				   (car args) (cdr args)))))))
    (list (list flex-head valterm))))

(define (huet-imitate-term flex-head rigid-head betas xs)
  (cond
   ((term-in-pair-form? rigid-head)
    (let* ((left (term-in-pair-form-to-left rigid-head))
	   (right (term-in-pair-form-to-right rigid-head))
	   (hleft
	    (type-to-new-partial-var
	     (apply mk-arrow (append betas (list (term-to-type left))))))
	   (hright
	    (type-to-new-partial-var
	     (apply mk-arrow (append betas (list (term-to-type right))))))
	   (argleft ;(hleft xs)
	    (apply mk-term-in-app-form
		   (make-term-in-var-form hleft)
		   (map make-term-in-var-form xs)))
	   (argright ;(hright xs)
	    (apply mk-term-in-app-form
		   (make-term-in-var-form hright)
		   (map make-term-in-var-form xs)))
	   (valterm ;lambda_xs((hleft xs)@(hright xs))
	    (apply mk-term-in-abst-form
		   (append xs (list (make-term-in-pair-form
				     argleft argright))))))
      (list (list flex-head valterm))))
   ((term-in-lcomp-form? rigid-head)
    (let* ((kernel (term-in-lcomp-form-to-kernel rigid-head))
	   (pair-type (term-to-type kernel))
	   (alphas (arrow-form-to-arg-types (term-to-type rigid-head)))
	   (h (type-to-new-partial-var
	       (apply mk-arrow (append betas (list pair-type)))))
	   (hs (map (lambda (type)
		      (type-to-new-partial-var
		       (apply mk-arrow (append betas (list type)))))
		    alphas))
	   (arg ;(h xs)
	    (apply mk-term-in-app-form
		   (make-term-in-var-form h)
		   (map make-term-in-var-form xs)))
	   (args ;(hs xs)
	    (map (lambda (h) (apply mk-term-in-app-form
				    (make-term-in-var-form h)
				    (map make-term-in-var-form xs)))
		 hs))
	   (valterm ;lambda_xs(left(h xs)(hs xs))
	    (apply mk-term-in-abst-form
		   (append xs (list (apply mk-term-in-app-form
					   (cons
					    (make-term-in-lcomp-form arg)
					    args)))))))
      (list (list flex-head valterm))))
   ((term-in-rcomp-form? rigid-head)
    (let* ((kernel (term-in-rcomp-form-to-kernel rigid-head))
	   (pair-type (term-to-type kernel))
	   (alphas (arrow-form-to-arg-types (term-to-type rigid-head)))
	   (h (type-to-new-partial-var
	       (apply mk-arrow (append betas (list pair-type)))))
	   (hs (map (lambda (type)
		      (type-to-new-partial-var
		       (apply mk-arrow (append betas (list type)))))
		    alphas))
	   (arg ;(h xs)
	    (apply mk-term-in-app-form
		   (make-term-in-var-form h)
		   (map make-term-in-var-form xs)))
	   (args ;(hs xs)
	    (map (lambda (h) (apply mk-term-in-app-form
				    (make-term-in-var-form h)
				    (map make-term-in-var-form xs)))
		 hs))
	   (valterm ;lambda_xs(right(h xs)(hs xs))
	    (apply mk-term-in-abst-form
		   (append xs (list (apply mk-term-in-app-form
					   (make-term-in-rcomp-form arg)
					   args))))))
      (list (list flex-head valterm))))
   (else
    (let* ((alphas (arrow-form-to-arg-types (term-to-type rigid-head)))
	   (hs (map (lambda (type)
		      (type-to-new-partial-var
		       (apply mk-arrow (append betas (list type)))))
		    alphas))
	   (args ;(hs xs)
	    (map (lambda (h) (apply mk-term-in-app-form
				    (cons (make-term-in-var-form h)
					  (map make-term-in-var-form xs))))
		 hs))
	   (valterm ;lambda_xs(A(hs xs))
	    (apply mk-term-in-abst-form
		   (append xs (list (apply mk-term-in-app-form
					   rigid-head args))))))
      (list (list flex-head valterm))))))

;; huet-imitate-formula only uses the head of its rigid formula, which is
;; one of 'atom, bicon, (quant vars), predicate.  The predicate may be
;; a non-flexible pvar.

(define (huet-imitate-formula pvar rigid-formula betas xs)
  (cond
   ((atom-form? rigid-formula)
    (let* ((h (type-to-new-partial-var
	       (apply mk-arrow (append betas (list (make-alg "boole"))))))
	   (arg ;(h xs)
	    (apply mk-term-in-app-form
		   (make-term-in-var-form h)
		   (map make-term-in-var-form xs)))
	   (val-cterm ;{xs|atom(h xs)}
	    (apply make-cterm
		   (append xs (list (make-atomic-formula arg))))))
      (list (list pvar val-cterm))))
   ((bicon-form? rigid-formula)
    (let* ((bicon (bicon-form-to-bicon rigid-formula))
	   (arity (apply make-arity betas))
	   (new-pvar1 (arity-to-new-pvar arity pvar))
	   (new-pvar2 (arity-to-new-pvar arity pvar))
	   (formula1 (apply make-predicate-formula
			    (cons new-pvar1 (map make-term-in-var-form xs))))
	   (formula2 (apply make-predicate-formula
			    (cons new-pvar2 (map make-term-in-var-form xs))))
	   (val-cterm ;{xs|new-pvar1 xs o new-pvar2 xs}
	    (apply make-cterm
		   (append xs (list (make-bicon bicon formula1 formula2))))))
      (list (list pvar val-cterm))))
   ((quant-form? rigid-formula)
    (let* ((quant (quant-form-to-quant rigid-formula))
	   (vars (quant-form-to-vars rigid-formula))
	   (alphas (map var-to-type vars))
	   (arity (apply make-arity (append alphas betas)))
	   (new-pvar (arity-to-new-pvar arity pvar))
	   (new-kernel (apply make-predicate-formula
			      new-pvar (map make-term-in-var-form
					    (append vars xs))))
	   (val-cterm ;{xs|quant_vars(new-pvar vars xs)}
	    (apply make-cterm
		   (append xs (list (make-quant quant vars new-kernel))))))
      (list (list pvar val-cterm))))
   ((predicate-form? rigid-formula)
    (let* ((predicate (predicate-form-to-predicate rigid-formula))
	   (arity (predicate-to-arity predicate))
	   (alphas (arity-to-types arity))
	   (hs (map (lambda (type)
		      (type-to-new-partial-var
		       (apply mk-arrow (append betas (list type)))))
		    alphas))
	   (args ;(hs xs)
	    (map (lambda (h) (apply mk-term-in-app-form
				    (make-term-in-var-form h)
				    (map make-term-in-var-form xs)))
		 hs))
	   (val-cterm ;{xs|A(hs xs)}
	    (apply make-cterm
		   (append xs (list (apply make-predicate-formula
					   predicate args))))))
      (list (list pvar val-cterm))))
   (else (myerror "huet-imitate-formula" "formula expected" rigid-formula))))

(define (huet-project i flex-head betas xs)
  (let* ((xi-term (make-term-in-var-form (list-ref xs (- i 1))))
	 (betai (list-ref betas (- i 1)))
	 (alphas (arrow-form-to-arg-types betai))
	 (hs (map (lambda (type)
		    (type-to-new-partial-var
		     (apply mk-arrow (append betas (list type)))))
		  alphas))
	 (args ;(hs xs)
	  (map (lambda (h) (apply mk-term-in-app-form
				  (make-term-in-var-form h)
				  (map make-term-in-var-form xs)))
	       hs))
	 (valterm ;lambda_xs(x_i(hs xs))
	  (apply mk-term-in-abst-form
		 (append xs (list (apply mk-term-in-app-form
					 xi-term args))))))
    (list (list flex-head valterm))))

(define (unif-pairs-substitute-and-beta-nf unif-pairs opsubst)
  (do ((ps unif-pairs (cdr ps))
       (res '()
	    (let ((expr1 (caar ps))
		  (expr2 (cadar ps)))
	      (cons (list (cond ((term-form? expr1)
				 (term-to-beta-nf
				  (term-substitute expr1 opsubst)))
				((formula-form? expr1)
				 (formula-to-beta-nf
				  (formula-substitute expr1 opsubst)))
				(else
				 (myerror "unif-pairs-substitute-and-beta-nf"
					  "term or formula expected" expr1)))
			  (cond ((term-form? expr2)
				 (term-to-beta-nf
				  (term-substitute expr2 opsubst)))
				((formula-form? expr2)
				 (formula-to-beta-nf
				  (formula-substitute expr2 opsubst)))
				(else
				 (myerror "unif-pairs-substitute-and-beta-nf"
					  "term or formula expected" expr2))))
		    res))))
      ((null? ps) (reverse res))))

(define (huet-match pattern instance . opt-ignore-deco-flag-and-sig-topvars)
  (let ((tsubst (apply pattern-and-instance-to-tsubst
		       (append (list pattern instance)
			       opt-ignore-deco-flag-and-sig-topvars))))
    (and tsubst
	 (apply huet-match-wrt-tsubst
		(append (list tsubst pattern instance)
			opt-ignore-deco-flag-and-sig-topvars)))))

(define (huet-match-wrt-tsubst
	 tsubst pattern instance . opt-ignore-deco-flag-and-sig-topvars)
  (let* ((sig-vars
	  (list-transform-positive opt-ignore-deco-flag-and-sig-topvars
	    var-form?))
	 (sig-pvars
	  (list-transform-positive opt-ignore-deco-flag-and-sig-topvars
	    pvar-form?))
	 (rest
	  (list-transform-positive opt-ignore-deco-flag-and-sig-topvars
	    (lambda (x)
	      (not (or (tvar-form? x) (var-form? x) (pvar-form? x))))))
	 (ignore-deco-flag (if (pair? rest) (car rest) #f))
	 (vars (cond ((term-form? pattern) (term-to-free pattern))
		     ((formula-form? pattern) (formula-to-free pattern))
		     (else (myerror
			    "huet-match-wrt-tsubst" "term or formula expected"
			    pattern))))
	 (pvars (if (formula-form? pattern) (formula-to-pvars pattern) '()))
	 (critical-tvars (map car tsubst))
	 (critical-vars
	  (list-transform-positive vars
	    (lambda (var)
	      (pair? (intersection (type-to-tvars (var-to-type var))
				   critical-tvars)))))
	 (critical-pvars
	  (list-transform-positive pvars
	    (lambda (pvar)
	      (let* ((arity (pvar-to-arity pvar))
		     (types (arity-to-types arity)))
		(pair? (intersection (apply union (map type-to-tvars types))
				     critical-tvars))))))
	 (renaming-subst
	  (map (lambda (var)
		 (let* ((type (var-to-type var))
			(new-type (type-substitute type tsubst))
			(new-var
			 (if (t-deg-one? (var-to-t-deg var))
			     (type-to-new-var new-type var)
			     (type-to-new-partial-var new-type var))))
		   (list var (make-term-in-var-form new-var))))
	       critical-vars))
	 (renaming-psubst
	  (map (lambda (pvar)
		 (let* ((arity (pvar-to-arity pvar))
			(types (arity-to-types arity))
			(new-types (map (lambda (x)
					  (type-substitute x tsubst))
					types))
			(new-arity (apply make-arity new-types))
			(new-pvar (arity-to-new-pvar new-arity pvar)))
		   (list pvar (predicate-to-cterm new-pvar))))
	       critical-pvars))
	 (renaming-tosubst (append tsubst renaming-subst))
	 (renaming-topsubst (append renaming-tosubst renaming-psubst))
	 (subst-pattern
	  (if (term-form? pattern)
	      (term-substitute pattern renaming-tosubst)
	      (formula-substitute pattern renaming-topsubst)))
	 (critical-sig-vars
	  (list-transform-positive sig-vars
	    (lambda (var)
	      (pair? (intersection (type-to-tvars (var-to-type var))
				   critical-tvars)))))
	 (uncritical-sig-vars
	  (list-transform-positive sig-vars
	    (lambda (var)
	      (null? (intersection (type-to-tvars (var-to-type var))
				   critical-tvars)))))
	 (renamed-critical-sig-vars
	  (map (lambda (var)
		 (term-in-var-form-to-var
		  (term-substitute (make-term-in-var-form var)
				   renaming-tosubst)))
	       critical-sig-vars))
	 (renamed-sig-vars
	  (append uncritical-sig-vars renamed-critical-sig-vars))
	 (critical-sig-pvars
	  (list-transform-positive sig-pvars
	    (lambda (pvar)
	      (let* ((arity (pvar-to-arity pvar))
		     (types (arity-to-types arity)))
		(pair? (intersection (apply union (map type-to-tvars types))
				     critical-tvars))))))
	 (uncritical-sig-pvars
	  (list-transform-positive sig-pvars
	    (lambda (pvar)
	      (let* ((arity (pvar-to-arity pvar))
		     (types (arity-to-types arity)))
		(null? (intersection (apply union (map type-to-tvars types))
				     critical-tvars))))))
	 (renamed-critical-sig-pvars
	  (map (lambda (pvar)
		 (predicate-form-to-predicate
		  (cterm-to-formula
		   (cterm-substitute (predicate-to-cterm pvar)
				     renaming-topsubst))))
	       critical-sig-pvars))
	 (renamed-sig-pvars
	  (append uncritical-sig-pvars renamed-critical-sig-pvars))
	 (new-sig-vars
	  (cond ((term-form? instance) (term-to-free instance))
		((formula-form? instance) (formula-to-free instance))
		(else (myerror
		       "huet-match-wrt-tsubst" "term or formula expected"
		       instance))))
	 (new-sig-pvars (if (formula-form? instance)
			    (formula-to-pvars instance)
			    '()))
	 (new-flex-vars (set-minus (if (term-form? subst-pattern)
				       (term-to-free subst-pattern)
				       (formula-to-free subst-pattern))
				   (append renamed-sig-vars new-sig-vars)))
	 (new-flex-pvars (set-minus (if (term-form? subst-pattern)
					'()
					(formula-to-pvars subst-pattern))
				    (append renamed-sig-pvars
					    new-sig-pvars)))
	 (results (huet-unifiers (append renamed-sig-vars renamed-sig-pvars
					 new-sig-vars new-sig-pvars)
				 (append new-flex-vars new-flex-pvars)
				 '() ;initially no forbidden variables
				 ignore-deco-flag
				 (list subst-pattern instance))))
    (and (pair? results)
	 (let* ((sorted-results
		 (insertsort
		  (lambda (res1 res2)
		    (let* ((opsubst1 (car res1))
			   (opsubst2 (car res2)))
		      (< (opsubst-to-depth opsubst1)
			 (opsubst-to-depth opsubst2))))
		  results))
		(most-detailed-opsubst (caar sorted-results))
		(subst (list-transform-positive most-detailed-opsubst
			 (lambda (x) (var-form? (car x)))))
		(psubst (list-transform-positive most-detailed-opsubst
			  (lambda (x) (pvar-form? (car x)))))
		(composed-subst
		 (compose-substitutions renaming-subst subst))
		(cleaned-composed-subst
		 (list-transform-positive composed-subst
		   (lambda (x) (member (car x) vars))))
		(composed-psubst
		 (compose-substitutions renaming-psubst psubst))
		(cleaned-composed-psubst
		 (list-transform-positive composed-psubst
		   (lambda (x) (member (car x) pvars))))
		(cleaned-composed-subst-in-eta-nf
		 (map (lambda (subst-pair)
			(let ((pvar (car subst-pair))
			      (term (cadr subst-pair)))
			  (list pvar (term-to-eta-nf term))))
		      cleaned-composed-subst))
		(cleaned-composed-psubst-in-eta-nf
		 (map (lambda (subst-pair)
			(let ((pvar (car subst-pair))
			      (cterm (cadr subst-pair)))
			  (list pvar (cterm-to-eta-nf cterm))))
		      cleaned-composed-psubst)))
	   (append tsubst
		   cleaned-composed-subst-in-eta-nf
		   cleaned-composed-psubst-in-eta-nf)))))

(define (opsubst-to-depth opsubst)
  (if (null? opsubst) 0
      (let* ((val (cadar opsubst))
	     (m (cond
		 ((term-form? val)
		  (term-to-depth val))
		 ((cterm-form? val)
		  (formula-to-depth (cterm-to-formula val)))
		 (else (myerror "opsubst-to-depth" "term or cterm expected"
				val)))))
	(max m (opsubst-to-depth (cdr opsubst))))))
