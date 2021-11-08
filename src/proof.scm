;; 2021-11-06.  proof.scm
;; 10. Proofs
;; ==========

;; 10-1. Constructors and accessors
;; ================================

;; Proofs are built from assumption variables and assumption constants
;; (i.e., axioms, theorems and global assumptions) by the usual rules of
;; natural deduction, i.e., introduction and elimination rules for
;; implication, conjunction and universal quantification.  From a proof
;; we can read off its context, which is an ordered list of object and
;; assumption variables.

(define proof-to-formula cadr)

;; Proofs always have the form (tag formula ...) where ... is a list with
;; further information.

;; Constructor, accessor and test for proofs in assumption variable form:
;; (proof-in-avar-form formula avar)

(define (make-proof-in-avar-form avar)
  (list 'proof-in-avar-form (avar-to-formula avar) avar))

(define proof-in-avar-form-to-avar caddr)

(define (proof-in-avar-form? proof)
  (eq? 'proof-in-avar-form (tag proof)))

;; Constructor, accessor and test for proofs in assumption constant form:

(define (make-proof-in-aconst-form aconst)
  (list 'proof-in-aconst-form (aconst-to-formula aconst) aconst))

(define proof-in-aconst-form-to-aconst caddr)

(define (proof-in-aconst-form? proof)
  (eq? 'proof-in-aconst-form (tag proof)))

;; Constructors, accessors and test for implication introduction:

(define (make-proof-in-imp-intro-form avar proof)
  (list 'proof-in-imp-intro-form
	(make-imp (avar-to-formula avar) (proof-to-formula proof))
	avar
	proof))

(define proof-in-imp-intro-form-to-avar caddr)
(define proof-in-imp-intro-form-to-kernel cadddr)

(define (proof-in-imp-intro-form? proof)
  (eq? 'proof-in-imp-intro-form (tag proof)))

(define (make-proof-in-impnc-intro-form avar proof)
  (list 'proof-in-impnc-intro-form
	(make-impnc (avar-to-formula avar) (proof-to-formula proof))
	avar
	proof))

(define proof-in-impnc-intro-form-to-avar caddr)
(define proof-in-impnc-intro-form-to-kernel cadddr)

(define (proof-in-impnc-intro-form? proof)
  (eq? 'proof-in-impnc-intro-form (tag proof)))

;; (mk-proof-in-intro-form x1 ... proof) is formed from proof by first
;; abstracting x1, then x2 and so on.  Here x1, x2 ... can be
;; assumption or object variables.

(define (mk-proof-in-intro-form x . rest)
  (if (null? rest)
      x
      (cond ((avar-form? x)
	     (let ((prev (apply mk-proof-in-intro-form rest)))
	       (make-proof-in-imp-intro-form x prev)))
	    ((var-form? x)
	     (let ((prev (apply mk-proof-in-intro-form rest)))
	       (make-proof-in-all-intro-form x prev)))
	    (else (myerror "mk-proof-in-intro-form"
			   "assumption or object variable expected"
			   x)))))

(define (mk-proof-in-nc-intro-form x . rest)
  (if (null? rest)
      x
      (cond ((avar-form? x)
	     (let ((prev (apply mk-proof-in-nc-intro-form rest)))
	       (make-proof-in-impnc-intro-form x prev)))
	    ((var-form? x)
	     (let ((prev (apply mk-proof-in-nc-intro-form rest)))
	       (make-proof-in-allnc-intro-form x prev)))
	    (else (myerror "mk-proof-in-nc-intro-form"
			   "assumption or object variable expected"
			   x)))))

(define (mk-proof-in-nc-intro-form-without-impnc x . rest)
  (if (null? rest)
      x
      (cond ((avar-form? x)
	     (let ((prev (apply mk-proof-in-nc-intro-form-without-impnc rest)))
	       (make-proof-in-imp-intro-form x prev)))
	    ((var-form? x)
	     (let ((prev (apply mk-proof-in-nc-intro-form-without-impnc rest)))
	       (make-proof-in-allnc-intro-form x prev)))
	    (else (myerror "mk-proof-in-nc-intro-form-without-impnc"
			   "assumption or object variable expected"
			   x)))))

;; In (mk-proof-in-cr-nc-intro-form x . rest) x is obtained from a
;; list of premises and variables where each element is followed by an
;; indicator for nc or cr (true means nc).

(define (mk-proof-in-cr-nc-intro-form x . rest)
  (if (null? rest)
      x
      (cond
       ((avar-form? x)
	(if (null? rest)
	    (myerror "mk-proof-in-cr-nc-intro-form"
		     "nc-indicator expected after" (avar-to-formula x))
	    (let* ((nc-indicator (car rest))
		   (prev (apply mk-proof-in-cr-nc-intro-form (cdr rest))))
	      (if nc-indicator
		  (make-proof-in-impnc-intro-form x prev)
		  (make-proof-in-imp-intro-form x prev)))))
       ((var-form? x)
	(if (null? rest)
	    (myerror "mk-proof-in-cr-nc-intro-form"
		     "nc-indicator expected after" x)
	    (let* ((nc-indicator (car rest))
		   (prev (apply mk-proof-in-cr-nc-intro-form (cdr rest))))
	      (if nc-indicator
		  (make-proof-in-allnc-intro-form x prev)
		  (make-proof-in-all-intro-form x prev)))))
       (else (myerror "mk-proof-in-cr-nc-intro-form"
		      "assumption or object variable expected" x)))))

(define (proof-in-intro-form-to-kernel-and-vars proof)
  (case (tag proof)
    ((proof-in-imp-intro-form)
     (let* ((prev (proof-in-intro-form-to-kernel-and-vars
		   (proof-in-imp-intro-form-to-kernel proof)))
	    (prev-kernel (car prev))
	    (prev-vars (cdr prev)))
       (cons prev-kernel
	     (cons (proof-in-imp-intro-form-to-avar proof) prev-vars))))
    ((proof-in-impnc-intro-form)
     (let* ((prev (proof-in-intro-form-to-kernel-and-vars
		   (proof-in-impnc-intro-form-to-kernel proof)))
	    (prev-kernel (car prev))
	    (prev-vars (cdr prev)))
       (cons prev-kernel
	     (cons (proof-in-impnc-intro-form-to-avar proof) prev-vars))))
    ((proof-in-all-intro-form)
     (let* ((prev (proof-in-intro-form-to-kernel-and-vars
		   (proof-in-all-intro-form-to-kernel proof)))
	    (prev-kernel (car prev))
	    (prev-vars (cdr prev)))
       (cons prev-kernel
	     (cons (proof-in-all-intro-form-to-var proof) prev-vars))))
    ((proof-in-allnc-intro-form)
     (let* ((prev (proof-in-intro-form-to-kernel-and-vars
		   (proof-in-allnc-intro-form-to-kernel proof)))
	    (prev-kernel (car prev))
	    (prev-vars (cdr prev)))
       (cons prev-kernel
	     (cons (proof-in-allnc-intro-form-to-var proof) prev-vars))))
    (else (list proof))))

(define (proof-in-intro-form-to-vars proof . x)
  (cond
   ((null? x)
    (if (proof-in-imp-impnc-all-allnc-intro-form? proof)
	(cons (proof-in-imp-impnc-all-allnc-intro-form-to-var proof)
	      (proof-in-intro-form-to-vars
	       (proof-in-imp-impnc-all-allnc-intro-form-to-kernel proof)))
	'()))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((p proof (proof-in-imp-impnc-all-allnc-intro-form-to-kernel p))
	   (i 0 (+ 1 i))
	   (res '() (cons (proof-in-imp-impnc-all-allnc-intro-form-to-var p)
			  res)))
	  ((or (= n i) (not (proof-in-imp-impnc-all-allnc-intro-form? p)))
	   (reverse res)))))
   (else (myerror "proof-in-intro-form-to-vars" "non-negative integer expected"
		  (car x)))))

;; proof-in-intro-form-to-final-kernel computes the final kernel (the
;; kernel after removing at most (car x) abstracted avars and vars) of
;; a proof.

(define (proof-in-intro-form-to-final-kernel proof . x)
  (cond
   ((null? x)
    (if (proof-in-imp-impnc-all-allnc-intro-form? proof)
	(proof-in-intro-form-to-final-kernel
	 (proof-in-imp-impnc-all-allnc-intro-form-to-kernel proof))
	proof))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (do ((p proof (proof-in-imp-impnc-all-allnc-intro-form-to-kernel p))
	   (i 0 (+ 1 i))
	   (res proof (proof-in-imp-impnc-all-allnc-intro-form-to-kernel res)))
	  ((or (= n i) (not (proof-in-imp-impnc-all-allnc-intro-form? p)))
	   res))))
   (else (myerror "proof-in-intro-form-to-final-kernel"
		  "non-negative integer expected"
		  (car x)))))

(define (intro-proof-and-new-kernel-and-depth-to-proof proof new-kernel . x)
  (cond
   ((null? x)
    (case (tag proof)
      ((proof-in-imp-intro-form)
       (make-proof-in-imp-intro-form
	(proof-in-imp-intro-form-to-avar proof)
	(intro-proof-and-new-kernel-and-depth-to-proof
	 (proof-in-imp-intro-form-to-kernel proof) new-kernel)))
      ((proof-in-impnc-intro-form)
       (make-proof-in-impnc-intro-form
	(proof-in-impnc-intro-form-to-avar proof)
	(intro-proof-and-new-kernel-and-depth-to-proof
	 (proof-in-impnc-intro-form-to-kernel proof) new-kernel)))
      ((proof-in-all-intro-form)
       (make-proof-in-all-intro-form
	(proof-in-all-intro-form-to-var proof)
	(intro-proof-and-new-kernel-and-depth-to-proof
	 (proof-in-all-intro-form-to-kernel proof) new-kernel)))
      ((proof-in-allnc-intro-form)
       (make-proof-in-allnc-intro-form
	(proof-in-allnc-intro-form-to-var proof)
	(intro-proof-and-new-kernel-and-depth-to-proof
	 (proof-in-allnc-intro-form-to-kernel proof) new-kernel)))
      (else new-kernel)))
   ((and (integer? (car x)) (not (negative? (car x))))
    (let ((n (car x)))
      (if
       (zero? n) new-kernel
       (case (tag proof)
	 ((proof-in-imp-intro-form)
	  (make-proof-in-imp-intro-form
	   (proof-in-imp-intro-form-to-avar proof)
	   (intro-proof-and-new-kernel-and-depth-to-proof
	    (proof-in-imp-intro-form-to-kernel proof) new-kernel (- n 1))))
	 ((proof-in-impnc-intro-form)
	  (make-proof-in-impnc-intro-form
	   (proof-in-impnc-intro-form-to-avar proof)
	   (intro-proof-and-new-kernel-and-depth-to-proof
	    (proof-in-impnc-intro-form-to-kernel proof) new-kernel (- n 1))))
	 ((proof-in-all-intro-form)
	  (make-proof-in-all-intro-form
	   (proof-in-all-intro-form-to-var proof)
	   (intro-proof-and-new-kernel-and-depth-to-proof
	    (proof-in-all-intro-form-to-kernel proof) new-kernel (- n 1))))
	 ((proof-in-allnc-intro-form)
	  (make-proof-in-allnc-intro-form
	   (proof-in-allnc-intro-form-to-var proof)
	   (intro-proof-and-new-kernel-and-depth-to-proof
	    (proof-in-allnc-intro-form-to-kernel proof) new-kernel (- n 1))))
	 (else new-kernel)))))))

;; Constructors, accessors and test for implication eliminations:

(define (make-proof-in-imp-elim-form proof1 proof2)
  (list 'proof-in-imp-elim-form
	(imp-form-to-conclusion (proof-to-formula proof1))
	proof1
	proof2))

(define proof-in-imp-elim-form-to-op caddr)
(define proof-in-imp-elim-form-to-arg cadddr)

(define (proof-in-imp-elim-form? proof)
  (eq? 'proof-in-imp-elim-form (tag proof)))

(define (proof-to-final-imp-elim-op proof)
  (if (proof-in-imp-elim-form? proof)
      (proof-to-final-imp-elim-op (proof-in-imp-elim-form-to-op proof))
      proof))

(define (proof-to-imp-elim-args proof)
  (if (proof-in-imp-elim-form? proof)
      (append (proof-to-imp-elim-args
	       (proof-in-imp-elim-form-to-op proof))
	      (list (proof-in-imp-elim-form-to-arg proof)))
      '()))

(define (make-proof-in-impnc-elim-form proof1 proof2)
  (list 'proof-in-impnc-elim-form
	(impnc-form-to-conclusion (proof-to-formula proof1))
	proof1
	proof2))

(define proof-in-impnc-elim-form-to-op caddr)
(define proof-in-impnc-elim-form-to-arg cadddr)

(define (proof-in-impnc-elim-form? proof)
  (eq? 'proof-in-impnc-elim-form (tag proof)))

(define (proof-to-final-impnc-elim-op proof)
  (if (proof-in-impnc-elim-form? proof)
      (proof-to-final-impnc-elim-op (proof-in-impnc-elim-form-to-op proof))
      proof))

(define (proof-to-impnc-elim-args proof)
  (if (proof-in-impnc-elim-form? proof)
      (append (proof-to-impnc-elim-args
	       (proof-in-impnc-elim-form-to-op proof))
	      (list (proof-in-impnc-elim-form-to-arg proof)))
      '()))

(define (proof-in-imp-impnc-all-allnc-intro-form? proof)
  (or (proof-in-imp-intro-form? proof)
      (proof-in-impnc-intro-form? proof)
      (proof-in-all-intro-form? proof)
      (proof-in-allnc-intro-form? proof)))

(define (proof-in-imp-impnc-all-allnc-intro-form-to-var proof)
  (case (tag proof)
    ((proof-in-imp-intro-form)
     (proof-in-imp-intro-form-to-avar proof))
    ((proof-in-impnc-intro-form)
     (proof-in-impnc-intro-form-to-avar proof))
    ((proof-in-all-intro-form)
     (proof-in-all-intro-form-to-var proof))
    ((proof-in-allnc-intro-form)
     (proof-in-allnc-intro-form-to-var proof))
    (else (myerror "proof-in-imp-impnc-all-allnc-intro-form-to-var"
		   "unexpected proof with tag" (tag proof)))))

(define (proof-in-imp-impnc-all-allnc-intro-form-to-kernel proof)
  (case (tag proof)
    ((proof-in-imp-intro-form)
     (proof-in-imp-intro-form-to-kernel proof))
    ((proof-in-impnc-intro-form)
     (proof-in-impnc-intro-form-to-kernel proof))
    ((proof-in-all-intro-form)
     (proof-in-all-intro-form-to-kernel proof))
    ((proof-in-allnc-intro-form)
     (proof-in-allnc-intro-form-to-kernel proof))
    (else (myerror "proof-in-imp-impnc-all-allnc-intro-form-to-kernel"
		   "unexpected proof with tag" (tag proof)))))

(define (mk-proof-in-elim-form proof . elim-items)
  (if
   (null? elim-items)
   proof
   (let ((formula (unfold-formula (proof-to-formula proof))))
     (cond
      ((or (prime-form? formula)
	   (ex-form? formula)
	   (exd-form? formula)
	   (exl-form? formula)
	   (exr-form? formula)
	   (exnc-form? formula)
	   (exdt-form? formula)
	   (exlt-form? formula)
	   (exrt-form? formula)
	   (exnct-form? formula))
       (myerror "mk-proof-in-elim-form"
		"applicable formula expected" formula))
      ((imp-form? formula)
       (apply mk-proof-in-elim-form
	      (make-proof-in-imp-elim-form proof (car elim-items))
	      (cdr elim-items)))
      ((impnc-form? formula)
       (apply mk-proof-in-elim-form
	      (make-proof-in-impnc-elim-form proof (car elim-items))
	      (cdr elim-items)))
      ((and-form? formula)
       (cond ((eq? 'left (car elim-items))
	      (apply mk-proof-in-elim-form
		     (make-proof-in-and-elim-left-form proof)
		     (cdr elim-items)))
	     ((eq? 'right (car elim-items))
	      (apply mk-proof-in-elim-form
		     (make-proof-in-and-elim-right-form proof)
		     (cdr elim-items)))
	     (else (myerror "mk-proof-in-elim-form" "left or right expected"
			    (car elim-items)))))
      ((and (bicon-form? formula)
	    (memq (bicon-form-to-bicon formula)
		  '(andd andl andr andnc)))
       (let ((left-conjunct (bicon-form-to-left formula))
	     (right-conjunct (bicon-form-to-right formula)))
	 (myerror "mk-proof-in-elim-form"
		  "not implemented for"
		  formula)))
      ((all-form? formula)
       (if (term-form? (car elim-items))
	   (apply mk-proof-in-elim-form
		  (make-proof-in-all-elim-form proof (car elim-items))
		  (cdr elim-items))
	   (myerror "mk-proof-in-elim-form" "term expected"
		    (car elim-items))))
      ((allnc-form? formula)
       (if (term-form? (car elim-items))
	   (apply mk-proof-in-elim-form
		  (make-proof-in-allnc-elim-form proof (car elim-items))
		  (cdr elim-items))
	   (myerror "mk-proof-in-elim-form" "term expected"
		    (car elim-items))))
      (else (myerror "mk-proof-in-elim-form" "formula expected" formula))))))

(define (proof-in-elim-form-to-final-op proof)
  (case (tag proof)
    ((proof-in-imp-elim-form)
     (proof-in-elim-form-to-final-op
      (proof-in-imp-elim-form-to-op proof)))
    ((proof-in-impnc-elim-form)
     (proof-in-elim-form-to-final-op
      (proof-in-impnc-elim-form-to-op proof)))
    ((proof-in-and-elim-left-form)
     (proof-in-elim-form-to-final-op
      (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-in-elim-form-to-final-op
      (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-elim-form)
     (proof-in-elim-form-to-final-op
      (proof-in-all-elim-form-to-op proof)))
    ((proof-in-allnc-elim-form)
     (proof-in-elim-form-to-final-op
      (proof-in-allnc-elim-form-to-op proof)))
    (else proof)))

(define (proof-in-elim-form-to-args proof)
  (case (tag proof)
    ((proof-in-imp-elim-form)
     (append (proof-in-elim-form-to-args
	      (proof-in-imp-elim-form-to-op proof))
	     (list (proof-in-imp-elim-form-to-arg proof))))
    ((proof-in-impnc-elim-form)
     (append (proof-in-elim-form-to-args
	      (proof-in-impnc-elim-form-to-op proof))
	     (list (proof-in-impnc-elim-form-to-arg proof))))
    ((proof-in-and-elim-left-form)
     (append (proof-in-elim-form-to-args
	      (proof-in-and-elim-left-form-to-kernel proof))
	     (list 'left)))
    ((proof-in-and-elim-right-form)
     (append (proof-in-elim-form-to-args
	      (proof-in-and-elim-right-form-to-kernel proof))
	     (list 'right)))
    ((proof-in-all-elim-form)
     (append (proof-in-elim-form-to-args
	      (proof-in-all-elim-form-to-op proof))
	     (list (proof-in-all-elim-form-to-arg proof))))
    ((proof-in-allnc-elim-form)
     (append (proof-in-elim-form-to-args
	      (proof-in-allnc-elim-form-to-op proof))
	     (list (proof-in-allnc-elim-form-to-arg proof))))
    (else '())))

(define (proof-in-elim-form-to-final-op-and-args proof)
  (case (tag proof)
    ((proof-in-imp-elim-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-imp-elim-form-to-op proof))
	     (list (proof-in-imp-elim-form-to-arg proof))))
    ((proof-in-impnc-elim-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-impnc-elim-form-to-op proof))
	     (list (proof-in-impnc-elim-form-to-arg proof))))
    ((proof-in-and-elim-left-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-and-elim-left-form-to-kernel proof))
	     (list 'left)))
    ((proof-in-and-elim-right-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-and-elim-right-form-to-kernel proof))
	     (list 'right)))
    ((proof-in-all-elim-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-all-elim-form-to-op proof))
	     (list (proof-in-all-elim-form-to-arg proof))))
    ((proof-in-allnc-elim-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-allnc-elim-form-to-op proof))
	     (list (proof-in-allnc-elim-form-to-arg proof))))
    (else (list proof))))

;; We need to generalize mk-proof-in-gen-elim-form, to also cover the
;; case of Ex-Elim written in application notation.

(define (mk-proof-in-gen-elim-form proof . elim-items)
  (if
   (null? elim-items)
   proof
   (let ((formula (unfold-formula (proof-to-formula proof))))
     (case (tag formula)
       ((atom predicate)
	(myerror "mk-proof-in-gen-elim-form" "applicable formula expected"
		 formula))
       ((ex)
	(let* ((side-premise (car elim-items))
	       (concl (imp-form-to-conclusion
		       (all-form-to-kernel
			(proof-to-formula side-premise))))
	       (ex-elim-aconst
		(ex-formula-and-concl-to-ex-elim-aconst formula concl))
	       (free (union (formula-to-free formula) (formula-to-free concl)))
	       (free-terms (map make-term-in-var-form free)))
	  (apply mk-proof-in-gen-elim-form
		 (make-proof-in-aconst-form ex-elim-aconst)
		 (append free-terms elim-items))))
       ((imp)
	(apply mk-proof-in-gen-elim-form
	       (make-proof-in-imp-elim-form proof (car elim-items))
	       (cdr elim-items)))
       ((impnc)
	(apply mk-proof-in-gen-elim-form
	       (make-proof-in-impnc-elim-form proof (car elim-items))
	       (cdr elim-items)))
       ((and)
	(cond ((eq? 'left (car elim-items))
	       (apply mk-proof-in-gen-elim-form
		      (make-proof-in-and-elim-left-form proof)
		      (cdr elim-items)))
	      ((eq? 'right (car elim-items))
	       (apply mk-proof-in-gen-elim-form
		      (make-proof-in-and-elim-right-form proof)
		      (cdr elim-items)))
	      (else (myerror "mk-proof-in-gen-elim-form"
			     "left or right expected"
			     (car elim-items)))))
       ((all)
	(if (term-form? (car elim-items))
	    (apply mk-proof-in-gen-elim-form
		   (make-proof-in-all-elim-form proof (car elim-items))
		   (cdr elim-items))
	    (myerror "mk-proof-in-gen-elim-form" "term expected"
		     (car elim-items))))
       ((allnc)
	(if (term-form? (car elim-items))
	    (apply mk-proof-in-gen-elim-form
		   (make-proof-in-allnc-elim-form proof (car elim-items))
		   (cdr elim-items))
	    (myerror "mk-proof-in-gen-elim-form" "term expected"
		     (car elim-items))))
       (else (myerror "mk-proof-in-gen-elim-form" "formula expected"
		      formula))))))

;; We generalize proof-in-elim-form-to-final-op and
;; proof-in-elim-form-to-args to treat Ex-Elim axioms as if they
;; were rules in application notation.

(define (proof-in-gen-elim-form-to-final-op proof)
  (case (tag proof)
    ((proof-in-imp-elim-form)
     (let ((op (proof-in-imp-elim-form-to-op proof))
	   (arg (proof-in-imp-elim-form-to-arg proof)))
       (if (and (proof-in-aconst-form? op)
		(string=? "Ex-Elim" (aconst-to-name
				     (proof-in-aconst-form-to-aconst op))))
	   (proof-in-gen-elim-form-to-final-op arg)
	   (proof-in-gen-elim-form-to-final-op op))))
    ((proof-in-impnc-elim-form)
     (let ((op (proof-in-impnc-elim-form-to-op proof))
	   (arg (proof-in-impnc-elim-form-to-arg proof)))
       (if (and (proof-in-aconst-form? op)
		(string=? "Ex-Elim" (aconst-to-name
				     (proof-in-aconst-form-to-aconst op))))
	   (proof-in-gen-elim-form-to-final-op arg)
	   (proof-in-gen-elim-form-to-final-op op))))
    ((proof-in-and-elim-left-form)
     (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (proof-in-gen-elim-form-to-final-op kernel)))
    ((proof-in-and-elim-right-form)
     (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (proof-in-gen-elim-form-to-final-op kernel)))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof)))
       (proof-in-gen-elim-form-to-final-op op)))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof)))
       (proof-in-gen-elim-form-to-final-op op)))
    (else proof)))

(define (proof-in-gen-elim-form-to-args proof)
  (case (tag proof)
    ((proof-in-imp-elim-form)
     (let ((op (proof-in-imp-elim-form-to-op proof))
	   (arg (proof-in-imp-elim-form-to-arg proof)))
       (if (and (proof-in-aconst-form? op)
		(string=? "Ex-Elim" (aconst-to-name
				     (proof-in-aconst-form-to-aconst op))))
	   (proof-in-gen-elim-form-to-args arg)
	   (append (proof-in-gen-elim-form-to-args op) (list arg)))))
    ((proof-in-impnc-elim-form)
     (let ((op (proof-in-impnc-elim-form-to-op proof))
	   (arg (proof-in-impnc-elim-form-to-arg proof)))
       (if (and (proof-in-aconst-form? op)
		(string=? "Ex-Elim" (aconst-to-name
				     (proof-in-aconst-form-to-aconst op))))
	   (proof-in-gen-elim-form-to-args arg)
	   (append (proof-in-gen-elim-form-to-args op) (list arg)))))
    ((proof-in-and-elim-left-form)
     (append (proof-in-gen-elim-form-to-args
	      (proof-in-and-elim-left-form-to-kernel proof))
	     (list 'left)))
    ((proof-in-and-elim-right-form)
     (append (proof-in-gen-elim-form-to-args
	      (proof-in-and-elim-right-form-to-kernel proof))
	     (list 'right)))
    ((proof-in-all-elim-form)
     (append (proof-in-gen-elim-form-to-args
	      (proof-in-all-elim-form-to-op proof))
	     (list (proof-in-all-elim-form-to-arg proof))))
    ((proof-in-allnc-elim-form)
     (append (proof-in-gen-elim-form-to-args
	      (proof-in-allnc-elim-form-to-op proof))
	     (list (proof-in-allnc-elim-form-to-arg proof))))
    (else '())))

;; Constructors, accessors and test for and introduction:

(define (make-proof-in-and-intro-form proof1 proof2)
  (list 'proof-in-and-intro-form
	(make-and (proof-to-formula proof1) (proof-to-formula proof2))
	proof1
	proof2))

(define proof-in-and-intro-form-to-left caddr)
(define proof-in-and-intro-form-to-right cadddr)

(define (proof-in-and-intro-form? proof)
  (eq? 'proof-in-and-intro-form (tag proof)))

(define (mk-proof-in-and-intro-form proof . proofs)
  (if (null? proofs)
      proof
      (make-proof-in-and-intro-form
       proof (apply mk-proof-in-and-intro-form proofs))))

;; Constructors, accessors and test for the left and right and elimination:

(define (make-proof-in-and-elim-left-form proof)
  (let ((formula (proof-to-formula proof)))
    (if (and-form? formula)
	(list 'proof-in-and-elim-left-form
	      (and-form-to-left formula)
	      proof)
	(myerror "make-proof-in-and-elim-left-form" "and form expected"
		 formula))))

(define proof-in-and-elim-left-form-to-kernel caddr)

(define (proof-in-and-elim-left-form? proof)
  (eq? 'proof-in-and-elim-left-form (tag proof)))

(define (make-proof-in-and-elim-right-form proof)
  (let ((formula (proof-to-formula proof)))
    (if (and-form? formula)
	(list 'proof-in-and-elim-right-form
	      (and-form-to-right formula)
	      proof)
	(myerror "make-proof-in-and-elim-right-form" "and form expected"
		 formula))))

(define proof-in-and-elim-right-form-to-kernel caddr)

(define (proof-in-and-elim-right-form? proof)
  (eq? 'proof-in-and-elim-right-form (tag proof)))

;; Constructors, accessors and test for all introduction:

(define (make-proof-in-all-intro-form var proof)
  (list 'proof-in-all-intro-form
	(make-all var (proof-to-formula proof))
	var
	proof))

(define proof-in-all-intro-form-to-var caddr)
(define proof-in-all-intro-form-to-kernel cadddr)

(define (proof-in-all-intro-form? proof)
  (eq? 'proof-in-all-intro-form (tag proof)))

;; Constructors, accessors and test for all elimination:

(define (make-proof-in-all-elim-form proof term . conclusion)
  (if (null? conclusion)
      (let* ((formula (proof-to-formula proof))
	     (var (all-form-to-var formula))
	     (kernel (all-form-to-kernel formula)))
	(list 'proof-in-all-elim-form
	      (if (and (term-in-var-form? term)
		       (equal? var (term-in-var-form-to-var term)))
		  kernel
		  (formula-subst kernel var term))
	      proof
	      term))
      (list 'proof-in-all-elim-form
	    (car conclusion)
	    proof
	    term)))

(define proof-in-all-elim-form-to-op caddr)
(define proof-in-all-elim-form-to-arg cadddr)

(define (proof-in-all-elim-form? proof)
  (eq? 'proof-in-all-elim-form (tag proof)))

(define (proof-to-final-all-elim-op proof)
  (if (proof-in-all-elim-form? proof)
      (proof-to-final-all-elim-op (proof-in-all-elim-form-to-op proof))
      proof))

;; Constructors, accessors and test for allnc introduction:

(define (make-proof-in-allnc-intro-form var proof)
  (list 'proof-in-allnc-intro-form
	(make-allnc var (proof-to-formula proof))
	var
	proof))

(define (mk-proof-in-allnc-intro-form x . rest)
  (if (null? rest)
      x
      (if (var-form? x)
	  (let ((prev (apply mk-proof-in-nc-intro-form rest)))
	    (make-proof-in-allnc-intro-form x prev))
	  (myerror "mk-proof-in-allnc-intro-form"
		   "object variable expected" x))))

(define proof-in-allnc-intro-form-to-var caddr)
(define proof-in-allnc-intro-form-to-kernel cadddr)

(define (proof-in-allnc-intro-form? proof)
  (eq? 'proof-in-allnc-intro-form (tag proof)))

;; Constructors, accessors and test for allnc-elimination:

(define (make-proof-in-allnc-elim-form proof term . conclusion)
  (if (null? conclusion)
      (let* ((formula (proof-to-formula proof))
	     (var (allnc-form-to-var formula))
	     (kernel (allnc-form-to-kernel formula)))
	(list 'proof-in-allnc-elim-form
	      (if (and (term-in-var-form? term)
		       (equal? var (term-in-var-form-to-var term)))
		  kernel
		  (formula-subst kernel var term))
	      proof
	      term))
      (list 'proof-in-allnc-elim-form
	    (car conclusion)
	    proof
	    term)))

(define proof-in-allnc-elim-form-to-op caddr)
(define proof-in-allnc-elim-form-to-arg cadddr)

(define (proof-in-allnc-elim-form? proof)
  (eq? 'proof-in-allnc-elim-form (tag proof)))

(define (proof-to-final-allnc-elim-op proof)
  (if (proof-in-allnc-elim-form? proof)
      (proof-to-final-allnc-elim-op (proof-in-allnc-elim-form-to-op proof))
      proof))

(define (proof-to-final-allnc-elim-op-and-args proof)
  (if (proof-in-allnc-elim-form? proof)
      (let* ((op (proof-in-allnc-elim-form-to-op proof))
	     (arg (proof-in-allnc-elim-form-to-arg proof))
	     (prev (proof-to-final-allnc-elim-op-and-args op)))
	(cons (car prev) (append (cdr prev) (list arg))))
      (list proof)))

(define (proof-to-final-all-allnc-elim-op-and-args proof)
  (case (tag proof)
    ((proof-in-all-elim-form)
     (let* ((op (proof-in-all-elim-form-to-op proof))
	    (arg (proof-in-all-elim-form-to-arg proof))
	    (prev (proof-to-final-all-allnc-elim-op-and-args op)))
	(cons (car prev) (append (cdr prev) (list arg)))))
    ((proof-in-allnc-elim-form)
     (let* ((op (proof-in-allnc-elim-form-to-op proof))
	    (arg (proof-in-allnc-elim-form-to-arg proof))
	    (prev (proof-to-final-all-allnc-elim-op-and-args op)))
	(cons (car prev) (append (cdr prev) (list arg)))))
    (else (list proof))))

;; Sometimes it is useful to have a replacement to the ex-intro rule:

(define (make-proof-in-ex-intro-form term ex-formula proof-of-inst)
  (let* ((var (ex-form-to-var ex-formula))
	 (kernel (ex-form-to-kernel ex-formula))
	 (free (formula-to-free ex-formula)))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form
	    (ex-formula-to-ex-intro-aconst ex-formula))
	   (append (map make-term-in-var-form free)
		   (list term proof-of-inst)))))

(define (mk-proof-in-ex-intro-form . terms-and-ex-formula-and-proof-of-inst)
  (let* ((revargs (reverse terms-and-ex-formula-and-proof-of-inst))
	 (proof-of-inst
	  (if (pair? revargs)
	      (car revargs)
	      (myerror "mk-proof-in-ex-intro-form" "arguments expected")))
	 (ex-formula
	  (if (pair? (cdr revargs))
	      (cadr revargs)
	      (myerror "mk-proof-in-ex-intro-form" ">= 2 arguments expected"
		       terms-and-ex-formula-and-proof-of-inst)))
	 (terms (reverse (cddr revargs))))
    (if
     (null? terms)
     proof-of-inst
     (let* ((var (ex-form-to-var ex-formula))
	    (kernel (ex-form-to-kernel ex-formula))
	    (free (formula-to-free ex-formula))
	    (prev (apply mk-proof-in-ex-intro-form
			 (append (cdr terms)
				 (list (formula-subst kernel var (car terms))
				       proof-of-inst)))))
       (apply mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (ex-formula-to-ex-intro-aconst ex-formula))
	      (append (map make-term-in-var-form free)
		      (list (car terms) prev)))))))

(define (proof-in-ind-rule-form? proof)
  (let ((final-imp-op (proof-to-final-imp-elim-op proof))
        (arglength (length (proof-to-imp-elim-args proof))))
    (and
     (proof-in-all-elim-form? final-imp-op)
     (let ((final-op (proof-to-final-allnc-elim-op
		      (proof-in-all-elim-form-to-op final-imp-op))))
       (and (proof-in-aconst-form? final-op)
	    (string=? "Ind" (aconst-to-name
			     (proof-in-aconst-form-to-aconst final-op)))
	    (let* ((uninst-kernel (all-form-to-kernel
				   (aconst-to-uninst-formula
				    (proof-in-aconst-form-to-aconst
				     final-op))))
		   (indlength (length (imp-form-to-premises uninst-kernel))))
	      (= indlength arglength)))))))

(define (proof-in-cases-rule-form? proof)
  (let ((final-imp-op (proof-to-final-imp-elim-op proof))
        (arglength (length (proof-to-imp-elim-args proof))))
    (and
     (proof-in-all-elim-form? final-imp-op)
     (let ((final-op (proof-to-final-allnc-elim-op
		      (proof-in-all-elim-form-to-op final-imp-op))))
       (and (proof-in-aconst-form? final-op)
	    (string=? "Cases" (aconst-to-name
			       (proof-in-aconst-form-to-aconst final-op)))
	    (let* ((uninst-kernel (all-form-to-kernel
				   (aconst-to-uninst-formula
				    (proof-in-aconst-form-to-aconst
				     final-op))))
		   (caseslength (length (imp-form-to-premises uninst-kernel))))
	      (= caseslength arglength)))))))

(define (proof-in-ex-elim-rule-form? proof)
  (and (proof-in-imp-elim-form? proof)
       (let ((op1 (proof-in-imp-elim-form-to-op proof))
	     (arg1 (proof-in-imp-elim-form-to-arg proof)))
	 (and (all-form? (proof-to-formula arg1))
	      (proof-in-imp-elim-form? op1)
	      (let ((op2 (proof-in-imp-elim-form-to-op op1))
		    (arg2 (proof-in-imp-elim-form-to-arg op1)))
		(and (ex-form? (proof-to-formula arg2))
		     (let ((final-op (proof-to-final-allnc-elim-op op2)))
		       (and (proof-in-aconst-form? final-op)
			    (string=? "Ex-Elim"
				      (aconst-to-name
				       (proof-in-aconst-form-to-aconst
					final-op)))))))))))

(define (make-proof-in-andd-elim-left-form proof)
  (let* ((fla (proof-to-formula proof))
	 (left (if (andd-form? fla)
		   (andd-form-to-left fla)
		   (myerror "make-proof-in-andd-elim-left-form"
			    "andd form expected" fla)))
	 (right (andd-form-to-right fla))
	 (free (formula-to-free fla))
	 (aconst (theorem-name-to-aconst "Lft"))
	 (pvars (map (lambda (cterm) (predicate-form-to-predicate
				      (cterm-to-formula cterm)))
		     (idpredconst-to-cterms
		      (predicate-form-to-predicate
		       (imp-form-to-premise
			(aconst-to-uninst-formula
			 (theorem-name-to-aconst "Lft")))))))
	 (psubst (make-substitution
		  pvars (map make-cterm (list left right))))
	 (subst-aconst (aconst-substitute aconst psubst)))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form subst-aconst)
	   (append (map make-term-in-var-form free)
		   (list proof)))))

(define (make-proof-in-andd-elim-right-form proof)
  (let* ((fla (proof-to-formula proof))
	 (left (if (andd-form? fla)
		   (andd-form-to-left fla)
		   (myerror "make-proof-in-andd-elim-left-form"
			    "andd form expected" fla)))
	 (right (andd-form-to-right fla))
	 (free (formula-to-free fla))
	 (aconst (theorem-name-to-aconst "Rht"))
	 (pvars (map (lambda (cterm) (predicate-form-to-predicate
				      (cterm-to-formula cterm)))
		     (idpredconst-to-cterms
		      (predicate-form-to-predicate
		       (imp-form-to-premise
			(aconst-to-uninst-formula
			 (theorem-name-to-aconst "Lft")))))))
	 (psubst (make-substitution
		  pvars (map make-cterm (list left right))))
	 (subst-aconst (aconst-substitute aconst psubst)))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form subst-aconst)
	   (append (map make-term-in-var-form free)
		   (list proof)))))

(define (make-proof-in-andr-elim-left-form proof)
  (let* ((fla (proof-to-formula proof))
	 (left (if (andr-form? fla)
		   (andr-form-to-left fla)
		   (myerror "make-proof-in-andr-elim-left-form"
			    "andr form expected" fla)))
	 (right (andr-form-to-right fla))
	 (imp-fla (make-imp fla left))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (proj-left-proof ;of Pvar^'1 -> Pvar2 -> Pvar^'1
	  (if (not (formula-of-nulltype? left))
	      (myerror "make-proof-in-andr-elim-left-form"
		       "formula of nulltype expected" left)
	      (let ((u (formula-to-new-avar left))
		    (v (formula-to-new-avar right)))
		(make-proof-in-imp-intro-form
		 u (make-proof-in-imp-intro-form
		    v (make-proof-in-avar-form u)))))))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form aconst)
	   (append (map make-term-in-var-form free)
		   (list proof proj-left-proof)))))

(define (make-proof-in-andr-elim-right-form proof)
  (let* ((fla (proof-to-formula proof))
	 (left (if (andr-form? fla)
		   (andr-form-to-left fla)
		   (myerror "make-proof-in-andr-elim-right-form"
			    "andr form expected" fla)))
	 (right (andr-form-to-right fla))
	 (imp-fla (make-imp fla right))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (proj-right-proof ;of Pvar1 -> Pvar2 -> Pvar2
	  (let ((u (formula-to-new-avar left))
		(v (formula-to-new-avar right)))
	    (make-proof-in-imp-intro-form
	     u (make-proof-in-imp-intro-form
		v (make-proof-in-avar-form v))))))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form aconst)
	   (append (map make-term-in-var-form free)
		   (list proof proj-right-proof)))))

(define (make-proof-in-andl-elim-right-form proof)
  (let* ((fla (proof-to-formula proof))
	 (left (if (andl-form? fla)
		   (andl-form-to-left fla)
		   (myerror "make-proof-in-andl-elim-right-form"
			    "andl form expected" fla)))
	 (right (andl-form-to-right fla))
	 (imp-fla (make-imp fla right))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (proj-right-proof ;of Pvar1 -> Pvar^'2 -> Pvar^'2
	  (if (not (formula-of-nulltype? right))
	      (myerror "make-proof-in-andl-elim-right-form"
		       "formula of nulltype expected" right)
	      (let ((u (formula-to-new-avar left))
		    (v (formula-to-new-avar right)))
		(make-proof-in-imp-intro-form
		 u (make-proof-in-imp-intro-form
		    v (make-proof-in-avar-form v)))))))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form aconst)
	   (append (map make-term-in-var-form free)
		   (list proof proj-right-proof)))))

(define (make-proof-in-andl-elim-left-form proof)
  (let* ((fla (proof-to-formula proof))
	 (left (if (andl-form? fla)
		   (andl-form-to-left fla)
		   (myerror "make-proof-in-andl-elim-left-form"
			    "andl form expected" fla)))
	 (right (andl-form-to-right fla))
	 (imp-fla (make-imp fla left))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (proj-left-proof ;of Pvar1 -> Pvar2 -> Pvar1
	  (let ((u (formula-to-new-avar left))
		(v (formula-to-new-avar right)))
	    (make-proof-in-imp-intro-form
	     u (make-proof-in-imp-intro-form
		v (make-proof-in-avar-form u))))))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form aconst)
	   (append (map make-term-in-var-form free)
	   (list proof proj-left-proof)))))

(define (make-proof-in-andnc-elim-left-form proof)
  (let* ((fla (proof-to-formula proof))
	 (left (if (andnc-form? fla)
		   (andnc-form-to-left fla)
		   (myerror "make-proof-in-andnc-elim-left-form"
			    "andnc form expected" fla)))
	 (right (andnc-form-to-right fla))
	 (imp-fla (make-imp fla left))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (proj-left-proof ;of Pvar^'1 -> Pvar2 -> Pvar^'1
	  (if (not (formula-of-nulltype? left))
	      (myerror "make-proof-in-andnc-elim-left-form"
		       "formula of nulltype expected" left)
	      (let ((u (formula-to-new-avar left))
		    (v (formula-to-new-avar right)))
		(make-proof-in-imp-intro-form
		 u (make-proof-in-imp-intro-form
		    v (make-proof-in-avar-form u)))))))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form aconst)
	   (append (map make-term-in-var-form free)
		   (list proof proj-left-proof)))))

(define (make-proof-in-andnc-elim-right-form proof)
  (let* ((fla (proof-to-formula proof))
	 (left (if (andnc-form? fla)
		   (andnc-form-to-left fla)
		   (myerror "make-proof-in-andnc-elim-right-form"
			    "andnc form expected" fla)))
	 (right (andnc-form-to-right fla))
	 (imp-fla (make-imp fla right))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (proj-right-proof ;of Pvar1 -> Pvar^'2 -> Pvar^'2
	  (if (not (formula-of-nulltype? right))
	      (myerror "make-proof-in-andnc-elim-right-form"
		       "formula of nulltype expected" right)
	  (let ((u (formula-to-new-avar left))
		(v (formula-to-new-avar right)))
		(make-proof-in-imp-intro-form
		 u (make-proof-in-imp-intro-form
		    v (make-proof-in-avar-form v)))))))
    (apply mk-proof-in-elim-form
	   (make-proof-in-aconst-form aconst)
	   (append (map make-term-in-var-form free)
		   (list proof proj-right-proof)))))

;; To define alpha-equality for proofs we use (following Robert Staerk)
;; an auxiliary function (corr x y alist alistrev).  Here
;; alist = ((u1 v1) ... (un vn)), alistrev = ((v1 u1) ... (vn un)).

;; (corr-avar x y alist alistrev) iff one of the following holds.
;; 1. There is a first entry (x v) of the form (x _) in alist
;;    and a first entry (y u) of the form (y _) in alistrev,
;;    and we have v=y and u=x.
;; 2. There is no entry of the form (x _) in alist
;;    and no entry of the form (y _) in alistrev,
;;    and we have x=y.

(define (corr-avar x y alist alistrev)
  (let ((info-x (assoc-wrt avar-form? x alist))
        (info-y (assoc-wrt avar-form? y alistrev)))
    (if info-x
	(and (avar=? (car info-x) (cadr info-y))
	     (avar=? (car info-y) (cadr info-x)))
	(and (not info-y) (avar=? x y)))))

(define (proof=? proof1 proof2)
  (proof=-aux? proof1 proof2 '() '()))

(define (proofs=? proofs1 proofs2)
  (proofs=-aux? proofs1 proofs2 '() '()))

(define (proof=-aux? proof1 proof2 alist alistrev)
  (or (and (proof-in-avar-form? proof1) (proof-in-avar-form? proof2)
           (corr (proof-in-avar-form-to-avar proof1)
		 (proof-in-avar-form-to-avar proof2)
		 alist alistrev))
      (and (proof-in-aconst-form? proof1) (proof-in-aconst-form? proof2)
	   (aconst=? (proof-in-aconst-form-to-aconst proof1)
		     (proof-in-aconst-form-to-aconst proof2)))
      (and (proof-in-imp-intro-form? proof1) (proof-in-imp-intro-form? proof2)
           (let ((avar1 (proof-in-imp-intro-form-to-avar proof1))
		 (avar2 (proof-in-imp-intro-form-to-avar proof2))
		 (kernel1 (proof-in-imp-intro-form-to-kernel proof1))
		 (kernel2 (proof-in-imp-intro-form-to-kernel proof2)))
             (proof=-aux? kernel1 kernel2
			  (cons (list avar1 avar2) alist)
			  (cons (list avar2 avar1) alistrev))))
      (and (proof-in-imp-elim-form? proof1) (proof-in-imp-elim-form? proof2)
           (let ((op1 (proof-in-imp-elim-form-to-op proof1))
                 (op2 (proof-in-imp-elim-form-to-op proof2))
                 (arg1 (proof-in-imp-elim-form-to-arg proof1))
                 (arg2 (proof-in-imp-elim-form-to-arg proof2)))
             (and (proof=-aux? op1 op2 alist alistrev)
                  (proof=-aux? arg1 arg2 alist alistrev))))
      (and (proof-in-impnc-intro-form? proof1)
	   (proof-in-impnc-intro-form? proof2)
           (let ((avar1 (proof-in-impnc-intro-form-to-avar proof1))
		 (avar2 (proof-in-impnc-intro-form-to-avar proof2))
		 (kernel1 (proof-in-impnc-intro-form-to-kernel proof1))
		 (kernel2 (proof-in-impnc-intro-form-to-kernel proof2)))
             (proof=-aux? kernel1 kernel2
			  (cons (list avar1 avar2) alist)
			  (cons (list avar2 avar1) alistrev))))
      (and (proof-in-impnc-elim-form? proof1)
	   (proof-in-impnc-elim-form? proof2)
           (let ((op1 (proof-in-impnc-elim-form-to-op proof1))
                 (op2 (proof-in-impnc-elim-form-to-op proof2))
                 (arg1 (proof-in-impnc-elim-form-to-arg proof1))
                 (arg2 (proof-in-impnc-elim-form-to-arg proof2)))
             (and (proof=-aux? op1 op2 alist alistrev)
                  (proof=-aux? arg1 arg2 alist alistrev))))
      (and (proof-in-and-intro-form? proof1) (proof-in-and-intro-form? proof2)
           (let ((left1 (proof-in-and-intro-form-to-left proof1))
                 (left2 (proof-in-and-intro-form-to-left proof2))
                 (right1 (proof-in-and-intro-form-to-right proof1))
                 (right2 (proof-in-and-intro-form-to-right proof2)))
             (and (proof=-aux? left1 left2 alist alistrev)
                  (proof=-aux? right1 right2 alist alistrev))))
      (and (proof-in-and-elim-left-form? proof1)
	   (proof-in-and-elim-left-form? proof2)
           (let ((kernel1 (proof-in-and-elim-left-form-to-kernel proof1))
                 (kernel2 (proof-in-and-elim-left-form-to-kernel proof2)))
	     (proof=-aux? kernel1 kernel2 alist alistrev)))
      (and (proof-in-and-elim-right-form? proof1)
	   (proof-in-and-elim-right-form? proof2)
           (let ((kernel1 (proof-in-and-elim-right-form-to-kernel proof1))
                 (kernel2 (proof-in-and-elim-right-form-to-kernel proof2)))
	     (proof=-aux? kernel1 kernel2 alist alistrev)))
      (and (proof-in-all-intro-form? proof1) (proof-in-all-intro-form? proof2)
           (let ((var1 (proof-in-all-intro-form-to-var proof1))
		 (var2 (proof-in-all-intro-form-to-var proof2))
		 (kernel1 (proof-in-all-intro-form-to-kernel proof1))
		 (kernel2 (proof-in-all-intro-form-to-kernel proof2)))
             (proof=-aux? kernel1 kernel2
			  (cons (list var1 var2) alist)
			  (cons (list var2 var1) alistrev))))
      (and (proof-in-all-elim-form? proof1) (proof-in-all-elim-form? proof2)
           (let ((op1 (proof-in-all-elim-form-to-op proof1))
                 (op2 (proof-in-all-elim-form-to-op proof2))
                 (arg1 (proof-in-all-elim-form-to-arg proof1))
                 (arg2 (proof-in-all-elim-form-to-arg proof2)))
             (and (proof=-aux? op1 op2 alist alistrev)
                  (term=-aux? arg1 arg2 alist alistrev))))
      (and (proof-in-allnc-intro-form? proof1)
	   (proof-in-allnc-intro-form? proof2)
           (let ((var1 (proof-in-allnc-intro-form-to-var proof1))
		 (var2 (proof-in-allnc-intro-form-to-var proof2))
		 (kernel1 (proof-in-allnc-intro-form-to-kernel proof1))
		 (kernel2 (proof-in-allnc-intro-form-to-kernel proof2)))
             (proof=-aux? kernel1 kernel2
			  (cons (list var1 var2) alist)
			  (cons (list var2 var1) alistrev))))
      (and (proof-in-allnc-elim-form? proof1)
	   (proof-in-allnc-elim-form? proof2)
           (let ((op1 (proof-in-allnc-elim-form-to-op proof1))
                 (op2 (proof-in-allnc-elim-form-to-op proof2))
                 (arg1 (proof-in-allnc-elim-form-to-arg proof1))
                 (arg2 (proof-in-allnc-elim-form-to-arg proof2)))
             (and (proof=-aux? op1 op2 alist alistrev)
                  (term=-aux? arg1 arg2 alist alistrev))))))

(define (proofs=-aux? proofs1 proofs2 alist alistrev)
  (or (and (null? proofs1) (null? proofs2))
      (and (proof=-aux? (car proofs1) (car proofs2) alist alistrev)
           (proofs=-aux? (cdr proofs1) (cdr proofs2) alist alistrev))))

;; For efficiency reasons (when working with goal in interactive proof
;; development) it will be useful to optionally allow the context in a
;; proof.

(define (proof-with-context? proof)
  (case (tag proof)
    ((proof-in-avar-form
      proof-in-aconst-form
      proof-in-and-elim-left-form
      proof-in-and-elim-right-form)
     (pair? (cdddr proof)))
    ((proof-in-imp-intro-form
      proof-in-imp-elim-form
      proof-in-impnc-intro-form
      proof-in-impnc-elim-form
      proof-in-and-intro-form
      proof-in-all-intro-form
      proof-in-all-elim-form
      proof-in-allnc-intro-form
      proof-in-allnc-elim-form)
     (pair? (cddddr proof)))
    (else (myerror "proof-with-context?" "proof tag expected" (tag proof)))))

(define (proof-with-context-to-context proof)
  (case (tag proof)
    ((proof-in-avar-form
      proof-in-aconst-form
      proof-in-and-elim-left-form
      proof-in-and-elim-right-form)
     (car (cdddr proof)))
    ((proof-in-imp-intro-form
      proof-in-imp-elim-form
      proof-in-impnc-intro-form
      proof-in-impnc-elim-form
      proof-in-and-intro-form
      proof-in-all-intro-form
      proof-in-all-elim-form
      proof-in-allnc-intro-form
      proof-in-allnc-elim-form)
     (car (cddddr proof)))
    (else (myerror "proof-with-context-to-context" "proof tag expected"
		   (tag proof)))))

(define (context-item=? x y)
  (or (and (var-form? x) (var-form? y) (equal? x y))
      (and (avar-form? x) (avar-form? y) (avar=? x y))))

(define (proof-to-context proof)
  (if
   (proof-with-context? proof)
   (proof-with-context-to-context proof)
   (case (tag proof)
     ((proof-in-avar-form)
      (let ((avar (proof-in-avar-form-to-avar proof)))
	(append (formula-to-free (avar-to-formula avar)) (list avar))))
     ((proof-in-aconst-form) '())
     ((proof-in-imp-intro-form)
      (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	     (kernel (proof-in-imp-intro-form-to-kernel proof))
	     (context (proof-to-context kernel)))
	(remove-wrt avar=? avar context)))
     ((proof-in-imp-elim-form)
      (let ((context1 (proof-to-context (proof-in-imp-elim-form-to-op proof)))
	    (context2 (proof-to-context
		       (proof-in-imp-elim-form-to-arg proof))))
	(union-wrt context-item=? context1 context2)))
     ((proof-in-impnc-intro-form)
      (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	     (kernel (proof-in-impnc-intro-form-to-kernel proof))
	     (context (proof-to-context kernel)))
	(remove-wrt avar=? avar context)))
     ((proof-in-impnc-elim-form)
      (let ((context1
	     (proof-to-context (proof-in-impnc-elim-form-to-op proof)))
	    (context2
	     (proof-to-context (proof-in-impnc-elim-form-to-arg proof))))
	(union-wrt context-item=? context1 context2)))
     ((proof-in-and-intro-form)
      (union-wrt context-item=?
		 (proof-to-context (proof-in-and-intro-form-to-left proof))
		 (proof-to-context (proof-in-and-intro-form-to-right proof))))
     ((proof-in-and-elim-left-form)
      (proof-to-context (proof-in-and-elim-left-form-to-kernel proof)))
     ((proof-in-and-elim-right-form)
      (proof-to-context (proof-in-and-elim-right-form-to-kernel proof)))
     ((proof-in-all-intro-form)
      (let* ((var (proof-in-all-intro-form-to-var proof))
	     (kernel (proof-in-all-intro-form-to-kernel proof))
	     (context (proof-to-context kernel)))
	(remove var context)))
     ((proof-in-all-elim-form)
      (let ((context (proof-to-context (proof-in-all-elim-form-to-op proof)))
	    (free (term-to-free (proof-in-all-elim-form-to-arg proof))))
	(union context free)))
     ((proof-in-allnc-intro-form)
      (let* ((var (proof-in-allnc-intro-form-to-var proof))
	     (kernel (proof-in-allnc-intro-form-to-kernel proof))
	     (context (proof-to-context kernel)))
	(remove var context)))
     ((proof-in-allnc-elim-form)
      (let ((context (proof-to-context (proof-in-allnc-elim-form-to-op proof)))
	    (free (term-to-free (proof-in-allnc-elim-form-to-arg proof))))
	(union context free)))
     (else (myerror "proof-to-context" "proof tag expected" (tag proof))))))

(define (proof-to-context-wrt avar-eq proof)
  (case (tag proof)
    ((proof-in-avar-form)
     (let ((avar (proof-in-avar-form-to-avar proof)))
       (append (formula-to-free (avar-to-formula avar)) (list avar))))
    ((proof-in-aconst-form) '())
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (context (proof-to-context-wrt avar-eq kernel)))
       (remove-wrt avar-eq avar context)))
    ((proof-in-imp-elim-form)
     (let ((context1 (proof-to-context-wrt
		      avar-eq (proof-in-imp-elim-form-to-op proof)))
	   (context2 (proof-to-context-wrt
		      avar-eq (proof-in-imp-elim-form-to-arg proof))))
       (union-wrt context-item-full=? context1 context2)))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (context (proof-to-context-wrt avar-eq kernel)))
       (remove-wrt avar-eq avar context)))
    ((proof-in-impnc-elim-form)
     (let ((context1 (proof-to-context-wrt
		      avar-eq (proof-in-impnc-elim-form-to-op proof)))
	   (context2 (proof-to-context-wrt
		      avar-eq (proof-in-impnc-elim-form-to-arg proof))))
       (union-wrt context-item-full=? context1 context2)))
    ((proof-in-and-intro-form)
     (union-wrt context-item-full=?
		(proof-to-context-wrt
		 avar-eq (proof-in-and-intro-form-to-left proof))
		(proof-to-context-wrt
		 avar-eq (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-context-wrt
      avar-eq (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-context-wrt
      avar-eq (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (let* ((var (proof-in-all-intro-form-to-var proof))
	    (kernel (proof-in-all-intro-form-to-kernel proof))
	    (context (proof-to-context-wrt avar-eq kernel)))
       (remove var context)))
    ((proof-in-all-elim-form)
     (let ((context (proof-to-context-wrt
		     avar-eq (proof-in-all-elim-form-to-op proof)))
	   (free (term-to-free (proof-in-all-elim-form-to-arg proof))))
       (union context free)))
    ((proof-in-allnc-intro-form)
     (let* ((var (proof-in-allnc-intro-form-to-var proof))
	    (kernel (proof-in-allnc-intro-form-to-kernel proof))
	    (context (proof-to-context-wrt avar-eq kernel)))
       (remove var context)))
    ((proof-in-allnc-elim-form)
     (let ((context (proof-to-context-wrt
		     avar-eq (proof-in-allnc-elim-form-to-op proof)))
	   (free (term-to-free (proof-in-allnc-elim-form-to-arg proof))))
       (union context free)))
    (else (myerror "proof-to-context-wrt" "proof tag expected"
		   (tag proof)))))

(define (context-to-vars context)
  (do ((l context (cdr l))
       (res '() (if (avar-form? (car l)) res (cons (car l) res))))
      ((null? l) (reverse res))))

(define (context-to-avars context)
  (do ((l context (cdr l))
       (res '() (if (avar-form? (car l)) (cons (car l) res) res)))
      ((null? l) (reverse res))))

(define (context=? context1 context2)
  (if (= (length context1) (length context2))
      (let context=?-aux ((c1 context1) (c2 context2))
	(if (null? c1)
	    #t
	    (let ((x1 (car c1))
		  (rest1 (cdr c1))
		  (x2 (car c2))
		  (rest2 (cdr c2)))
	      (if (context-item=? x1 x2)
		  (context=?-aux rest1 rest2)
		  #f))))
      #f))

(define (context-item-full=? x y)
  (or (and (var-form? x) (var-form? y) (equal? x y))
      (and (avar-form? x) (avar-form? y) (avar-full=? x y))))

(define (context-full=? context1 context2)
  (and (null? (context-fullminus context1 context2))
       (null? (context-fullminus context2 context1))))

(define (context-fullminus context1 context2)
  (do ((l context2 (cdr l))
       (res context1 (remove-wrt context-item-full=? (car l) res)))
      ((null? l) res)))

(define (context-to-tvars context)
  (let* ((vars (context-to-vars context))
	 (avars (context-to-avars context))
	 (var-tvars
	  (apply union (map (lambda (x) (type-to-tvars (var-to-type x)))
			    vars)))
	 (avar-tvars
	  (apply union (map (lambda (x) (formula-to-tvars (avar-to-formula x)))
			    avars))))
    (union var-tvars avar-tvars)))

(define (context-and-name-to-avar context name)
  (let* ((avars (context-to-avars context))
	 (name-avar-alist (map (lambda (avar)
				 (list (avar-to-name avar) avar))
			       avars))
	 (info (assoc name name-avar-alist)))
    (if info
	(cadr info)
	(myerror "context-and-name-to-avar" "missing avar" name))))

(define (pp-context context)
  (do ((c context (cdr c))
       (i 1 (if (avar-form? (car c)) (+ 1 i) i))
       (line "" line))
      ((null? c) (if (> (string-length line) 0)
		     (begin (display-comment line) (newline))))
    (if (avar-form? (car c))
	(let* ((string (string-append (avar-to-name (car c)) "_"
				      (number-to-string i))))
	  (set! line (string-append line "  " string ":"))
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
		       (fold-formula (avar-to-formula (car c))))))
	  (if (pair? (cdr c))
	      (begin (display-comment line) (newline)
		     (set! line ""))))
	(let* ((var (car c))
	       (varstring (var-to-string var)))
	  (set! line (string-append line "  " varstring))))))

;; We use acproof to mean proof-with-avar-contexts.  An acproof is a
;; proof in the sense of check-and-display-proof.  It is used to avoid
;; recomputation of avar-contexts when pruning.

(define (make-acproof-in-avar-form avar)
  (list 'proof-in-avar-form (avar-to-formula avar) avar (list avar)))

(define (make-acproof-in-aconst-form aconst)
  (list 'proof-in-aconst-form (aconst-to-formula aconst) aconst '()))

(define (make-acproof-in-imp-intro-form avar proof)
  (list 'proof-in-imp-intro-form
	(make-imp (avar-to-formula avar) (proof-to-formula proof))
	avar
	proof
	(remove-wrt avar=? avar (proof-with-context-to-context proof))))

(define (make-acproof-in-imp-elim-form proof1 proof2)
  (list 'proof-in-imp-elim-form
	(imp-form-to-conclusion (proof-to-formula proof1))
	proof1
	proof2
	(union-wrt avar=?
		   (proof-to-context proof1) (proof-to-context proof2))))

(define (make-acproof-in-impnc-intro-form avar proof)
  (list 'proof-in-impnc-intro-form
	(make-impnc (avar-to-formula avar) (proof-to-formula proof))
	avar
	proof
	(remove-wrt avar=? avar (proof-with-context-to-context proof))))

(define (make-acproof-in-impnc-elim-form proof1 proof2)
  (list 'proof-in-impnc-elim-form
	(impnc-form-to-conclusion (proof-to-formula proof1))
	proof1
	proof2
	(union-wrt avar=?
		   (proof-to-context proof1) (proof-to-context proof2))))

(define (make-acproof-in-and-intro-form proof1 proof2)
  (list 'proof-in-and-intro-form
	(make-and (proof-to-formula proof1) (proof-to-formula proof2))
	proof1
	proof2
	(union-wrt avar=?
		   (proof-to-context proof1) (proof-to-context proof2))))

(define (make-acproof-in-and-elim-left-form proof)
  (let ((formula (proof-to-formula proof)))
    (if (and-form? formula)
	(list 'proof-in-and-elim-left-form
	      (and-form-to-left formula)
	      proof
	      (proof-to-context proof))
	(myerror "make-acproof-in-and-elim-left-form" "and form expected"
		 formula))))

(define (make-acproof-in-and-elim-right-form proof)
  (let ((formula (proof-to-formula proof)))
    (if (and-form? formula)
	(list 'proof-in-and-elim-right-form
	      (and-form-to-right formula)
	      proof
	      (proof-to-context proof))
	(myerror "make-acproof-in-and-elim-right-form" "and form expected"
		 formula))))

(define (make-acproof-in-all-intro-form var proof)
  (list 'proof-in-all-intro-form
	(make-all var (proof-to-formula proof))
	var
	proof
	(proof-to-context proof)))

(define (make-acproof-in-all-elim-form proof term . conclusion)
  (if (null? conclusion)
      (let* ((formula (proof-to-formula proof))
	     (var (all-form-to-var formula))
	     (kernel (all-form-to-kernel formula)))
	(list 'proof-in-all-elim-form
	      (if (and (term-in-var-form? term)
		       (equal? var (term-in-var-form-to-var term)))
		  kernel
		  (formula-subst kernel var term))
	      proof
	      term
	      (proof-to-context proof)))
      (list 'proof-in-all-elim-form
	    (car conclusion)
	    proof
	    term
	    (proof-to-context proof))))

(define (make-acproof-in-allnc-intro-form var proof)
  (list 'proof-in-allnc-intro-form
	(make-allnc var (proof-to-formula proof))
	var
	proof
	(proof-to-context proof)))

(define (make-acproof-in-allnc-elim-form proof term . conclusion)
  (if (null? conclusion)
      (let* ((formula (proof-to-formula proof))
	     (var (allnc-form-to-var formula))
	     (kernel (allnc-form-to-kernel formula)))
	(list 'proof-in-allnc-elim-form
	      (if (and (term-in-var-form? term)
		       (equal? var (term-in-var-form-to-var term)))
		  kernel
		  (formula-subst kernel var term))
	      proof
	      term
	      (proof-to-context proof)))
      (list 'proof-in-allnc-elim-form
	    (car conclusion)
	    proof
	    term
	    (proof-to-context proof))))

(define (proof-to-acproof proof)
  (case (tag proof)
    ((proof-in-avar-form)
     (let ((avar (proof-in-avar-form-to-avar proof)))
       (make-acproof-in-avar-form avar)))
    ((proof-in-aconst-form)
     (let ((aconst (proof-in-aconst-form-to-aconst proof)))
       (make-acproof-in-aconst-form aconst)))
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (prev (proof-to-acproof kernel)))
       (make-acproof-in-imp-intro-form avar prev)))
    ((proof-in-imp-elim-form)
     (let* ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof))
	    (prev1 (proof-to-acproof op))
	    (prev2 (proof-to-acproof arg)))
       (make-acproof-in-imp-elim-form prev1 prev2)))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (prev (proof-to-acproof kernel)))
       (make-acproof-in-impnc-intro-form avar prev)))
    ((proof-in-impnc-elim-form)
     (let* ((op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof))
	    (prev1 (proof-to-acproof op))
	    (prev2 (proof-to-acproof arg)))
       (make-acproof-in-impnc-elim-form prev1 prev2)))
    ((proof-in-and-intro-form)
     (let* ((left (proof-in-and-intro-form-to-left proof))
	    (right (proof-in-and-intro-form-to-right proof))
	    (prev1 (proof-to-acproof left))
	    (prev2 (proof-to-acproof right)))
       (make-acproof-in-and-intro-form prev1 prev2)))
    ((proof-in-and-elim-left-form)
     (let* ((kernel (proof-in-and-elim-left-form-to-kernel proof))
	    (prev (proof-to-acproof kernel)))
       (make-acproof-in-and-elim-left-form prev)))
    ((proof-in-and-elim-right-form)
     (let* ((kernel (proof-in-and-elim-right-form-to-kernel proof))
	    (prev (proof-to-acproof kernel)))
       (make-acproof-in-and-elim-right-form prev)))
    ((proof-in-all-intro-form)
     (let* ((var (proof-in-all-intro-form-to-var proof))
	    (kernel (proof-in-all-intro-form-to-kernel proof))
	    (prev (proof-to-acproof kernel)))
       (make-acproof-in-all-intro-form var prev)))
    ((proof-in-all-elim-form)
     (let* ((op (proof-in-all-elim-form-to-op proof))
	    (prev (proof-to-acproof op))
	    (arg (proof-in-all-elim-form-to-arg proof))
	    (conclusion (proof-to-formula proof)))
       (make-acproof-in-all-elim-form prev arg conclusion)))
    ((proof-in-allnc-intro-form)
     (let* ((var (proof-in-allnc-intro-form-to-var proof))
	    (kernel (proof-in-allnc-intro-form-to-kernel proof))
	    (prev (proof-to-acproof kernel)))
       (make-acproof-in-allnc-intro-form var prev)))
    ((proof-in-allnc-elim-form)
     (let* ((op (proof-in-allnc-elim-form-to-op proof))
	    (prev (proof-to-acproof op))
	    (arg (proof-in-allnc-elim-form-to-arg proof))
	    (conclusion (proof-to-formula proof)))
       (make-acproof-in-allnc-elim-form prev arg conclusion)))
    (else (myerror "proof-to-acproof" "proof tag expected" (tag proof)))))

;; The variable condition for allnc refers to the computational variables.

(define (proof-to-cvars proof)
  (if (formula-of-nulltype? (proof-to-formula proof))
      '()
      (proof-to-cvars-aux proof)))

;; In proof-to-cvars-aux we can assume that the proved formula has
;; computational content.

(define (proof-to-cvars-aux proof)
  (case (tag proof)
    ((proof-in-avar-form) (list (proof-in-avar-form-to-avar proof)))
    ((proof-in-aconst-form) '())
    ((proof-in-imp-intro-form)
     (remove-wrt avar=? (proof-in-imp-intro-form-to-avar proof)
		 (proof-to-cvars-aux
		  (proof-in-imp-intro-form-to-kernel proof))))
    ((proof-in-imp-elim-form)
     (let* ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof))
	    (prevop (proof-to-cvars-aux op))
	    (prevarg (proof-to-cvars arg)))
       (union prevop prevarg)))
    ((proof-in-impnc-intro-form)
     (proof-to-cvars-aux (proof-in-impnc-intro-form-to-kernel proof)))
    ((proof-in-impnc-elim-form)
     (proof-to-cvars-aux (proof-in-impnc-elim-form-to-op proof)))
    ((proof-in-and-intro-form)
     (let* ((left (proof-in-and-intro-form-to-left proof))
	    (right (proof-in-and-intro-form-to-right proof)))
       (if (formula-of-nulltype? (proof-to-formula left))
	   (proof-to-cvars-aux right)
	   (union (proof-to-cvars-aux left)
		  (proof-to-cvars right)))))
    ((proof-in-and-elim-left-form)
     (proof-to-cvars-aux
      (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-cvars-aux
      (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (remove (proof-in-all-intro-form-to-var proof)
	     (proof-to-cvars-aux
	      (proof-in-all-intro-form-to-kernel proof))))
    ((proof-in-all-elim-form)
     (let* ((op (proof-in-all-elim-form-to-op proof))
	    (arg (proof-in-all-elim-form-to-arg proof))
	    (prev (proof-to-cvars-aux op)))
       (union prev (term-to-free arg))))
    ((proof-in-allnc-intro-form)
     (proof-to-cvars-aux
      (proof-in-allnc-intro-form-to-kernel proof)))
    ((proof-in-allnc-elim-form)
     (proof-to-cvars-aux
      (proof-in-allnc-elim-form-to-op proof)))
    (else (myerror "proof-to-cvars" "proof tag expected" (tag proof)))))

(define (proof-to-free proof)
  (case (tag proof)
    ((proof-in-avar-form)
     (formula-to-free (proof-to-formula proof)))
    ((proof-in-aconst-form) '())
    ((proof-in-imp-intro-form)
     (let ((free1 (formula-to-free
		   (avar-to-formula (proof-in-imp-intro-form-to-avar proof))))
	   (free2 (proof-to-free (proof-in-imp-intro-form-to-kernel proof))))
       (union free1 free2)))
    ((proof-in-imp-elim-form)
     (union (proof-to-free (proof-in-imp-elim-form-to-op proof))
	    (proof-to-free (proof-in-imp-elim-form-to-arg proof))))
    ((proof-in-impnc-intro-form)
     (let ((free1 (formula-to-free
		   (avar-to-formula
		    (proof-in-impnc-intro-form-to-avar proof))))
	   (free2 (proof-to-free (proof-in-impnc-intro-form-to-kernel proof))))
       (union free1 free2)))
    ((proof-in-impnc-elim-form)
     (union (proof-to-free (proof-in-impnc-elim-form-to-op proof))
	    (proof-to-free (proof-in-impnc-elim-form-to-arg proof))))
    ((proof-in-and-intro-form)
     (union (proof-to-free (proof-in-and-intro-form-to-left proof))
	    (proof-to-free (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-free (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-free (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (remove (proof-in-all-intro-form-to-var proof)
	     (proof-to-free (proof-in-all-intro-form-to-kernel proof))))
    ((proof-in-all-elim-form)
     (union (proof-to-free (proof-in-all-elim-form-to-op proof))
	    (term-to-free (proof-in-all-elim-form-to-arg proof))))
    ((proof-in-allnc-intro-form)
     (remove (proof-in-allnc-intro-form-to-var proof)
	     (proof-to-free (proof-in-allnc-intro-form-to-kernel proof))))
    ((proof-in-allnc-elim-form)
     (union (proof-to-free (proof-in-allnc-elim-form-to-op proof))
	    (term-to-free (proof-in-allnc-elim-form-to-arg proof))))
    (else (myerror "proof-to-free" "proof tag expected" (tag proof)))))

(define (proof-to-tvars proof)
  (case (tag proof)
    ((proof-in-avar-form)
     (formula-to-tvars (proof-to-formula proof)))
    ((proof-in-aconst-form)
     (formula-to-tvars (proof-to-formula proof)))
    ((proof-in-imp-intro-form)
     (let ((tvars1 (formula-to-tvars
		    (avar-to-formula (proof-in-imp-intro-form-to-avar proof))))
	   (tvars2 (proof-to-tvars (proof-in-imp-intro-form-to-kernel proof))))
       (union tvars1 tvars2)))
    ((proof-in-imp-elim-form)
     (union (proof-to-tvars (proof-in-imp-elim-form-to-op proof))
	    (proof-to-tvars (proof-in-imp-elim-form-to-arg proof))))
    ((proof-in-impnc-intro-form)
     (let ((tvars1 (formula-to-tvars
		    (avar-to-formula
		     (proof-in-impnc-intro-form-to-avar proof))))
	   (tvars2 (proof-to-tvars
		    (proof-in-impnc-intro-form-to-kernel proof))))
       (union tvars1 tvars2)))
    ((proof-in-impnc-elim-form)
     (union (proof-to-tvars (proof-in-impnc-elim-form-to-op proof))
	    (proof-to-tvars (proof-in-impnc-elim-form-to-arg proof))))
    ((proof-in-and-intro-form)
     (union (proof-to-tvars (proof-in-and-intro-form-to-left proof))
	    (proof-to-tvars (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-tvars (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-tvars (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (proof-to-tvars (proof-in-all-intro-form-to-kernel proof)))
    ((proof-in-all-elim-form)
     (proof-to-tvars (proof-in-all-elim-form-to-op proof)))
    ((proof-in-allnc-intro-form)
     (proof-to-tvars (proof-in-allnc-intro-form-to-kernel proof)))
    ((proof-in-allnc-elim-form)
     (proof-to-tvars (proof-in-allnc-elim-form-to-op proof)))
    (else (myerror "proof-to-tvars" "proof tag expected" (tag proof)))))

(define (proof-to-pvars proof)
  (case (tag proof)
    ((proof-in-avar-form)
     (formula-to-pvars (proof-to-formula proof)))
    ((proof-in-aconst-form)
     (formula-to-pvars (proof-to-formula proof)))
    ((proof-in-imp-intro-form)
     (let ((pvars1 (formula-to-pvars
		    (avar-to-formula (proof-in-imp-intro-form-to-avar proof))))
	   (pvars2 (proof-to-pvars (proof-in-imp-intro-form-to-kernel proof))))
       (union pvars1 pvars2)))
    ((proof-in-imp-elim-form)
     (union (proof-to-pvars (proof-in-imp-elim-form-to-op proof))
	    (proof-to-pvars (proof-in-imp-elim-form-to-arg proof))))
    ((proof-in-impnc-intro-form)
     (let ((pvars1 (formula-to-pvars
		    (avar-to-formula
		     (proof-in-impnc-intro-form-to-avar proof))))
	   (pvars2 (proof-to-pvars
		    (proof-in-impnc-intro-form-to-kernel proof))))
       (union pvars1 pvars2)))
    ((proof-in-impnc-elim-form)
     (union (proof-to-pvars (proof-in-impnc-elim-form-to-op proof))
	    (proof-to-pvars (proof-in-impnc-elim-form-to-arg proof))))
    ((proof-in-and-intro-form)
     (union (proof-to-pvars (proof-in-and-intro-form-to-left proof))
	    (proof-to-pvars (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-pvars (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-pvars (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (proof-to-pvars (proof-in-all-intro-form-to-kernel proof)))
    ((proof-in-all-elim-form)
     (proof-to-pvars (proof-in-all-elim-form-to-op proof)))
    ((proof-in-allnc-intro-form)
     (proof-to-pvars (proof-in-allnc-intro-form-to-kernel proof)))
    ((proof-in-allnc-elim-form)
     (proof-to-pvars (proof-in-allnc-elim-form-to-op proof)))
    (else (myerror "proof-to-pvars" "proof tag expected" (tag proof)))))

(define (proof-to-free-avars proof)
  (case (tag proof)
    ((proof-in-avar-form) (list (proof-in-avar-form-to-avar proof)))
    ((proof-in-aconst-form) '())
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (free-avars (proof-to-free-avars kernel)))
       (remove-wrt avar=? avar free-avars)))
    ((proof-in-imp-elim-form)
     (let ((free-avars1
	    (proof-to-free-avars (proof-in-imp-elim-form-to-op proof)))
	   (free-avars2
	    (proof-to-free-avars (proof-in-imp-elim-form-to-arg proof))))
       (union-wrt avar=? free-avars1 free-avars2)))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (free-avars (proof-to-free-avars kernel)))
       (remove-wrt avar=? avar free-avars)))
    ((proof-in-impnc-elim-form)
     (let ((free-avars1
	    (proof-to-free-avars (proof-in-impnc-elim-form-to-op proof)))
	   (free-avars2
	    (proof-to-free-avars (proof-in-impnc-elim-form-to-arg proof))))
       (union-wrt avar=? free-avars1 free-avars2)))
    ((proof-in-and-intro-form)
     (union-wrt
      avar=?
      (proof-to-free-avars (proof-in-and-intro-form-to-left proof))
      (proof-to-free-avars (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-free-avars (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-free-avars (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (proof-to-free-avars (proof-in-all-intro-form-to-kernel proof)))
    ((proof-in-all-elim-form)
     (proof-to-free-avars (proof-in-all-elim-form-to-op proof)))
    ((proof-in-allnc-intro-form)
     (proof-to-free-avars (proof-in-allnc-intro-form-to-kernel proof)))
    ((proof-in-allnc-elim-form)
     (proof-to-free-avars (proof-in-allnc-elim-form-to-op proof)))
    (else (myerror "proof-to-free-avars" "proof tag expected" (tag proof)))))

(define (proof-to-bound-avars proof)
  (case (tag proof)
    ((proof-in-avar-form proof-in-aconst-form) '())
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (bound (proof-to-bound-avars kernel)))
       (adjoin-wrt avar=? avar bound)))
    ((proof-in-imp-elim-form)
     (let ((bound1 (proof-to-bound-avars
		    (proof-in-imp-elim-form-to-op proof)))
	   (bound2 (proof-to-bound-avars
		    (proof-in-imp-elim-form-to-arg proof))))
       (union-wrt avar=? bound1 bound2)))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (bound (proof-to-bound-avars kernel)))
       (adjoin-wrt avar=? avar bound)))
    ((proof-in-impnc-elim-form)
     (let ((bound1 (proof-to-bound-avars
		    (proof-in-impnc-elim-form-to-op proof)))
	   (bound2 (proof-to-bound-avars
		    (proof-in-impnc-elim-form-to-arg proof))))
       (union-wrt avar=? bound1 bound2)))
    ((proof-in-and-intro-form)
     (union-wrt
      avar=?
      (proof-to-bound-avars (proof-in-and-intro-form-to-left proof))
      (proof-to-bound-avars (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-bound-avars (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-bound-avars (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (proof-to-bound-avars (proof-in-all-intro-form-to-kernel proof)))
    ((proof-in-all-elim-form)
     (proof-to-bound-avars (proof-in-all-elim-form-to-op proof)))
    ((proof-in-allnc-intro-form)
     (proof-to-bound-avars (proof-in-allnc-intro-form-to-kernel proof)))
    ((proof-in-allnc-elim-form)
     (proof-to-bound-avars (proof-in-allnc-elim-form-to-op proof)))
    (else (myerror "proof-to-bound-avars" "proof tag expected" (tag proof)))))

(define (proof-to-free-and-bound-avars-wrt avar-eq proof)
  (case (tag proof)
    ((proof-in-avar-form) (list (proof-in-avar-form-to-avar proof)))
    ((proof-in-aconst-form) '())
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (free-and-bound-avars
	     (proof-to-free-and-bound-avars-wrt avar-eq kernel)))
       (union-wrt avar-eq (list avar) free-and-bound-avars)))
    ((proof-in-imp-elim-form)
     (let ((free-and-bound-avars1
	    (proof-to-free-and-bound-avars-wrt
	     avar-eq (proof-in-imp-elim-form-to-op proof)))
	   (free-and-bound-avars2
	    (proof-to-free-and-bound-avars-wrt
	     avar-eq (proof-in-imp-elim-form-to-arg proof))))
       (union-wrt avar-eq free-and-bound-avars1 free-and-bound-avars2)))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (free-and-bound-avars
	     (proof-to-free-and-bound-avars-wrt avar-eq kernel)))
       (union-wrt avar-eq (list avar) free-and-bound-avars)))
    ((proof-in-impnc-elim-form)
     (let ((free-and-bound-avars1
	    (proof-to-free-and-bound-avars-wrt
	     avar-eq (proof-in-impnc-elim-form-to-op proof)))
	   (free-and-bound-avars2
	    (proof-to-free-and-bound-avars-wrt
	     avar-eq (proof-in-impnc-elim-form-to-arg proof))))
       (union-wrt avar-eq free-and-bound-avars1 free-and-bound-avars2)))
    ((proof-in-and-intro-form)
     (union-wrt avar-eq
		(proof-to-free-and-bound-avars-wrt
		 avar-eq (proof-in-and-intro-form-to-left proof))
		(proof-to-free-and-bound-avars-wrt
		 avar-eq (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-free-and-bound-avars-wrt
      avar-eq (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-free-and-bound-avars-wrt
      avar-eq (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (proof-to-free-and-bound-avars-wrt
      avar-eq (proof-in-all-intro-form-to-kernel proof)))
    ((proof-in-all-elim-form)
     (proof-to-free-and-bound-avars-wrt
      avar-eq (proof-in-all-elim-form-to-op proof)))
    ((proof-in-allnc-intro-form)
     (proof-to-free-and-bound-avars-wrt
      avar-eq (proof-in-allnc-intro-form-to-kernel proof)))
    ((proof-in-allnc-elim-form)
     (proof-to-free-and-bound-avars-wrt
      avar-eq (proof-in-allnc-elim-form-to-op proof)))
    (else (myerror "proof-to-free-and-bound-avars-wrt" "proof tag expected"
		   (tag proof)))))

(define (proof-to-free-and-bound-avars proof)
  (proof-to-free-and-bound-avars-wrt avar=? proof))

(define (proof-respects-avar-convention? proof)
  (let* ((avars (proof-to-free-and-bound-avars-wrt avar-full=? proof))
	 (l (map (lambda (avar)
		   (list (avar-to-name avar) (avar-to-index avar)))
		 avars)))
    (equal? (remove-duplicates l) l)))

(define (proof-to-aconsts-without-rules-aux proof)
  (case (tag proof)
    ((proof-in-avar-form) '())
    ((proof-in-aconst-form)
     (let ((aconst (proof-in-aconst-form-to-aconst proof)))
       (if (aconst-without-rules? aconst) (list aconst) '())))
    ((proof-in-imp-intro-form)
     (proof-to-aconsts-without-rules-aux
      (proof-in-imp-intro-form-to-kernel proof)))
    ((proof-in-imp-elim-form)
     (let ((aconsts1 (proof-to-aconsts-without-rules-aux
		      (proof-in-imp-elim-form-to-op proof)))
	   (aconsts2 (proof-to-aconsts-without-rules-aux
		      (proof-in-imp-elim-form-to-arg proof))))
       (append aconsts1 aconsts2)))
    ((proof-in-impnc-intro-form)
     (proof-to-aconsts-without-rules-aux
      (proof-in-impnc-intro-form-to-kernel proof)))
    ((proof-in-impnc-elim-form)
     (let ((aconsts1 (proof-to-aconsts-without-rules-aux
		      (proof-in-impnc-elim-form-to-op proof)))
	   (aconsts2 (proof-to-aconsts-without-rules-aux
		      (proof-in-impnc-elim-form-to-arg proof))))
       (append aconsts1 aconsts2)))
    ((proof-in-and-intro-form)
     (append (proof-to-aconsts-without-rules-aux
	      (proof-in-and-intro-form-to-left proof))
	     (proof-to-aconsts-without-rules-aux
	      (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-aconsts-without-rules-aux
      (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-aconsts-without-rules-aux
      (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (proof-to-aconsts-without-rules-aux
      (proof-in-all-intro-form-to-kernel proof)))
    ((proof-in-all-elim-form)
     (proof-to-aconsts-without-rules-aux
      (proof-in-all-elim-form-to-op proof)))
    ((proof-in-allnc-intro-form)
     (proof-to-aconsts-without-rules-aux
      (proof-in-allnc-intro-form-to-kernel proof)))
    ((proof-in-allnc-elim-form)
     (proof-to-aconsts-without-rules-aux
      (proof-in-allnc-elim-form-to-op proof)))
    (else (myerror "proof-to-aconsts-without-rules-aux" "proof tag expected"
		   (tag proof)))))

(define (proof-to-aconsts-without-rules proof)
  (remove-duplicates-wrt aconst=? (proof-to-aconsts-without-rules-aux proof)))

(define (proof-to-aconsts-with-repetitions proof)
  (case (tag proof)
    ((proof-in-avar-form) '())
    ((proof-in-aconst-form)
     (list (proof-in-aconst-form-to-aconst proof)))
    ((proof-in-imp-intro-form)
     (proof-to-aconsts-with-repetitions
      (proof-in-imp-intro-form-to-kernel proof)))
    ((proof-in-imp-elim-form)
     (let ((aconsts1 (proof-to-aconsts-with-repetitions
		      (proof-in-imp-elim-form-to-op proof)))
	   (aconsts2 (proof-to-aconsts-with-repetitions
		      (proof-in-imp-elim-form-to-arg proof))))
       (append aconsts1 aconsts2)))
    ((proof-in-impnc-intro-form)
     (proof-to-aconsts-with-repetitions
      (proof-in-impnc-intro-form-to-kernel proof)))
    ((proof-in-impnc-elim-form)
     (let ((aconsts1 (proof-to-aconsts-with-repetitions
		      (proof-in-impnc-elim-form-to-op proof)))
	   (aconsts2 (proof-to-aconsts-with-repetitions
		      (proof-in-impnc-elim-form-to-arg proof))))
       (append aconsts1 aconsts2)))
    ((proof-in-and-intro-form)
     (append (proof-to-aconsts-with-repetitions
	      (proof-in-and-intro-form-to-left proof))
	     (proof-to-aconsts-with-repetitions
	      (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-aconsts-with-repetitions
      (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-aconsts-with-repetitions
      (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (proof-to-aconsts-with-repetitions
      (proof-in-all-intro-form-to-kernel proof)))
    ((proof-in-all-elim-form)
     (proof-to-aconsts-with-repetitions (proof-in-all-elim-form-to-op proof)))
    ((proof-in-allnc-intro-form)
     (proof-to-aconsts-with-repetitions
      (proof-in-allnc-intro-form-to-kernel proof)))
    ((proof-in-allnc-elim-form)
     (proof-to-aconsts-with-repetitions
      (proof-in-allnc-elim-form-to-op proof)))
    (else (myerror "proof-to-aconsts-with-repetitions" "proof tag expected"
		   (tag proof)))))

(define (proof-to-aconsts proof)
  (remove-duplicates-wrt aconst=? (proof-to-aconsts-with-repetitions proof)))

(define (proof-to-global-assumptions-with-repetitions proof)
  (case (tag proof)
    ((proof-in-avar-form) '())
    ((proof-in-aconst-form)
     (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	    (name (aconst-to-name aconst)))
       (case (aconst-to-kind aconst)
	 ((theorem)
	  (proof-to-global-assumptions-with-repetitions
	   (theorem-name-to-proof (aconst-to-name aconst))))
	 ((global-assumption)
	  (list aconst))
	 (else '()))))
    ((proof-in-imp-intro-form)
     (proof-to-global-assumptions-with-repetitions
      (proof-in-imp-intro-form-to-kernel proof)))
    ((proof-in-imp-elim-form)
     (let ((aconsts1 (proof-to-global-assumptions-with-repetitions
		      (proof-in-imp-elim-form-to-op proof)))
	   (aconsts2 (proof-to-global-assumptions-with-repetitions
		      (proof-in-imp-elim-form-to-arg proof))))
       (append aconsts1 aconsts2)))
    ((proof-in-impnc-intro-form)
     (proof-to-global-assumptions-with-repetitions
      (proof-in-impnc-intro-form-to-kernel proof)))
    ((proof-in-impnc-elim-form)
     (let ((aconsts1 (proof-to-global-assumptions-with-repetitions
		      (proof-in-impnc-elim-form-to-op proof)))
	   (aconsts2 (proof-to-global-assumptions-with-repetitions
		      (proof-in-impnc-elim-form-to-arg proof))))
       (append aconsts1 aconsts2)))
    ((proof-in-and-intro-form)
     (append (proof-to-global-assumptions-with-repetitions
	      (proof-in-and-intro-form-to-left proof))
	     (proof-to-global-assumptions-with-repetitions
	      (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (proof-to-global-assumptions-with-repetitions
      (proof-in-and-elim-left-form-to-kernel proof)))
    ((proof-in-and-elim-right-form)
     (proof-to-global-assumptions-with-repetitions
      (proof-in-and-elim-right-form-to-kernel proof)))
    ((proof-in-all-intro-form)
     (proof-to-global-assumptions-with-repetitions
      (proof-in-all-intro-form-to-kernel proof)))
    ((proof-in-all-elim-form)
     (proof-to-global-assumptions-with-repetitions
      (proof-in-all-elim-form-to-op proof)))
    ((proof-in-allnc-intro-form)
     (proof-to-global-assumptions-with-repetitions
      (proof-in-allnc-intro-form-to-kernel proof)))
    ((proof-in-allnc-elim-form)
     (proof-to-global-assumptions-with-repetitions
      (proof-in-allnc-elim-form-to-op proof)))
    (else (myerror
	   "proof-to-global-assumptions-with-repetitions" "proof tag expected"
	   (tag proof)))))

(define (proof-to-global-assumptions proof)
  (remove-duplicates-wrt aconst=?
			 (proof-to-global-assumptions-with-repetitions proof)))

(define (thm-or-ga-name-to-proof name)
  (cond
   ((and (string? name) (assoc name THEOREMS))
    (make-proof-in-aconst-form (theorem-name-to-aconst name)))
   ((and (string? name) (assoc name GLOBAL-ASSUMPTIONS))
    (make-proof-in-aconst-form (global-assumption-name-to-aconst name)))
   (else (myerror "thm-or-ga-name-to-proof"
		  "name of theorem or global assumption expected"
		  name))))

;; Now for decoration.

;; The default case for opt-decfla is the formula of the proof.  If
;; opt-decfla is present, it must be a decoration variant of the
;; formula of the proof.  If the optional argument name-and-altname is
;; present, then in every recursive call it is checked whether (1) the
;; present proof is an application of the aconst op with name to some
;; args, (2) op applied to args proves an extension of decfla, and (3)
;; altop applied to args and some of decavars is between op applied to
;; args and decfla w.r.t. extension.  If so, a proof based on altop is
;; returned, else one carries on.

(define (proof-to-free-cr-avars proof id-deco?)
  (let ((formula-of-nulltype-wrt-id-deco?
	 (if id-deco?
	     formula-of-nulltype-under-extension?
	     formula-of-nulltype?)))
    (case (tag proof)
      ((proof-in-avar-form)
       (if (formula-of-nulltype-wrt-id-deco? (proof-to-formula proof))
	   '()
	   (list (proof-in-avar-form-to-avar proof))))
      ((proof-in-aconst-form) '())
      ((proof-in-imp-intro-form)
       (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	      (kernel (proof-in-imp-intro-form-to-kernel proof))
	      (free-cr-avars (proof-to-free-cr-avars kernel id-deco?)))
	 (remove-wrt avar=? avar free-cr-avars)))
      ((proof-in-imp-elim-form)
       (if (formula-of-nulltype-wrt-id-deco? (proof-to-formula proof))
	   '()
	   (let
	       ((free-cr-avars1
		 (proof-to-free-cr-avars (proof-in-imp-elim-form-to-op proof)
					 id-deco?))
		(free-cr-avars2
		 (proof-to-free-cr-avars (proof-in-imp-elim-form-to-arg proof)
					 id-deco?)))
	     (union-wrt avar=? free-cr-avars1 free-cr-avars2))))
      ((proof-in-impnc-intro-form)
       (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	      (kernel (proof-in-impnc-intro-form-to-kernel proof))
	      (free-cr-avars (proof-to-free-cr-avars kernel id-deco?)))
	 (remove-wrt avar=? avar free-cr-avars)))
      ((proof-in-impnc-elim-form)
       (if
	(formula-of-nulltype-wrt-id-deco? (proof-to-formula proof))
	'()
	(let ((free-cr-avars1
	       (proof-to-free-cr-avars (proof-in-impnc-elim-form-to-op proof)
				       id-deco?))
	      (free-cr-avars2
	       (proof-to-free-cr-avars (proof-in-impnc-elim-form-to-arg proof)
				       id-deco?)))
	  (union-wrt avar=? free-cr-avars1 free-cr-avars2))))
      ((proof-in-and-intro-form)
       (union-wrt
	avar=?
	(proof-to-free-cr-avars (proof-in-and-intro-form-to-left proof)
				id-deco?)
	(proof-to-free-cr-avars (proof-in-and-intro-form-to-right proof)
				id-deco?)))
      ((proof-in-and-elim-left-form)
       (if (formula-of-nulltype-wrt-id-deco? (proof-to-formula proof))
	   '()
	   (proof-to-free-cr-avars
	    (proof-in-and-elim-left-form-to-kernel proof) id-deco?)))
      ((proof-in-and-elim-right-form)
       (if (formula-of-nulltype-wrt-id-deco? (proof-to-formula proof))
	   '()
	   (proof-to-free-cr-avars
	    (proof-in-and-elim-right-form-to-kernel proof) id-deco?)))
      ((proof-in-all-intro-form)
       (proof-to-free-cr-avars (proof-in-all-intro-form-to-kernel proof)
			       id-deco?))
      ((proof-in-all-elim-form)
       (proof-to-free-cr-avars (proof-in-all-elim-form-to-op proof)
			       id-deco?))
      ((proof-in-allnc-intro-form)
       (proof-to-free-cr-avars (proof-in-allnc-intro-form-to-kernel proof)
			       id-deco?))
      ((proof-in-allnc-elim-form)
       (proof-to-free-cr-avars (proof-in-allnc-elim-form-to-op proof)
			       id-deco?))
      (else (myerror "proof-to-free-cr-avars" "proof tag expected"
		     (tag proof))))))

(define (decorate proof . opt-decfla-and-name-and-altname)
  (let* ((avars (proof-to-free-cr-avars proof #f)) ;id-deco? is false
	 (flas (list-transform-positive opt-decfla-and-name-and-altname
		 formula-form?))
	 (strings (list-transform-positive opt-decfla-and-name-and-altname
		    string?))
	 (decfla (if (pair? flas) (car flas) (proof-to-formula proof)))
	 (name-and-altname (if (< 1 (length strings))
			       (list (car strings) (cadr strings))
			       '())))
      (if
       (formula-of-nulltype? decfla)
       (cons (tag proof) (cons decfla (cddr proof)))
       (if (null? name-and-altname)
	   (car (ppat-and-decseq-and-availavars-to-proof-and-decavars
		 (proof-to-ppat proof #f) ;id-deco? is false
		 avars
		 decfla
		 avars ;all avars are available initially
		 #f))
	   (car (ppat-and-decseq-and-availavars-to-proof-and-decavars
		 (proof-to-ppat proof #f)
		 avars
		 (proof-to-formula proof)
		 avars ;all avars are available initially
		 #f
		 (car name-and-altname) (cadr name-and-altname)))))))

(define (fully-decorate proof . opt-decfla-and-name-and-altname)
  (let* ((avars (proof-to-free-cr-avars proof #t)) ;id-deco? is true
	 (flas (list-transform-positive opt-decfla-and-name-and-altname
		 formula-form?))
	 (strings (list-transform-positive opt-decfla-and-name-and-altname
		    string?))
	 (decfla (if (pair? flas) (car flas) (proof-to-formula proof)))
	 (name-and-altname (if (< 1 (length strings))
			       (list (car strings) (cadr strings))
			       '())))
      (if
       (formula-of-nulltype? decfla)
       (cons (tag proof) (cons decfla (cddr proof)))
       (if (null? name-and-altname)
	   (car (ppat-and-decseq-and-availavars-to-proof-and-decavars
		 (proof-to-ppat proof #t) ;id-deco? is true
		 avars
		 decfla
		 avars ;all avars are available initially
		 #t))
	   (car (ppat-and-decseq-and-availavars-to-proof-and-decavars
		 (proof-to-ppat proof #t)
		 avars
		 (proof-to-formula proof)
		 avars ;all avars are available initially
		 #t
		 (car name-and-altname) (cadr name-and-altname)))))))

;; proof-to-ppat turns every imp, all formula in the given proof into
;; an impnc, allnc formula, and in case id-deco? is true moreover (i)
;; every existential quantification exd, exl, exr into exnc, (ii) every
;; total existential quantification exdt, exlt, exrt into exnct, (iii)
;; every conjunction andd, andl, andr into andnc (andb is for the
;; boolean operator), and (iv) every disjunction or, orl, orr into oru
;; (orb is for the boolean operator).  This includes the parts of an
;; aconst which come from its uninstatiated formula.  proof-to-ppat
;; does not touch the n.c. parts of the proof, i.e., those which are
;; above a n.c. formula.  ppat is in general not a proof.

(define (proof-to-ppat proof id-deco?)
  (if
   (if id-deco?
       (formula-of-nulltype-under-extension? (proof-to-formula proof))
       (formula-of-nulltype? (proof-to-formula proof)))
   proof
   (case (tag proof)
     ((proof-in-avar-form)
      (let* ((avar (proof-in-avar-form-to-avar proof))
	     (undec-avar (make-avar (formula-to-undec-formula
				     (proof-to-formula proof) id-deco?)
				    (avar-to-index avar) (avar-to-name avar))))
	(make-proof-in-avar-form undec-avar)))
     ((proof-in-aconst-form)
      (let ((aconst (proof-in-aconst-form-to-aconst proof)))
	(list 'proof-in-aconst-form
	      (formula-to-undec-formula (aconst-to-formula aconst) id-deco?)
	      (aconst-to-undec-aconst aconst id-deco?))))
     ((proof-in-imp-intro-form)
      (let* ((kernel (proof-in-imp-intro-form-to-kernel proof))
	     (avar (proof-in-imp-intro-form-to-avar proof))
	     (undec-avar (make-avar (formula-to-undec-formula
				     (avar-to-formula avar) id-deco?)
				    (avar-to-index avar) (avar-to-name avar))))
	(make-proof-in-impnc-intro-form
	 undec-avar (proof-to-ppat kernel id-deco?))))
     ((proof-in-impnc-intro-form)
      (let* ((kernel (proof-in-impnc-intro-form-to-kernel proof))
	     (avar (proof-in-impnc-intro-form-to-avar proof))
	     (undec-avar (make-avar (formula-to-undec-formula
				     (avar-to-formula avar) id-deco?)
				    (avar-to-index avar) (avar-to-name avar))))
	(make-proof-in-impnc-intro-form
	 undec-avar (proof-to-ppat kernel id-deco?))))
     ((proof-in-imp-elim-form)
      (make-proof-in-impnc-elim-form
       (proof-to-ppat (proof-in-imp-elim-form-to-op proof) id-deco?)
       (proof-to-ppat (proof-in-imp-elim-form-to-arg proof) id-deco?)))
     ((proof-in-impnc-elim-form)
      (make-proof-in-impnc-elim-form
       (proof-to-ppat (proof-in-impnc-elim-form-to-op proof) id-deco?)
       (proof-to-ppat (proof-in-impnc-elim-form-to-arg proof) id-deco?)))
     ((proof-in-and-intro-form)
      (make-proof-in-and-intro-form
       (proof-to-ppat (proof-in-and-intro-form-to-left proof) id-deco?)
       (proof-to-ppat (proof-in-and-intro-form-to-right proof) id-deco?)))
     ((proof-in-and-elim-left-form)
      (make-proof-in-and-elim-left-form
       (proof-to-ppat (proof-in-and-elim-left-form-to-kernel proof)
		      id-deco?)))
     ((proof-in-and-elim-right-form)
      (make-proof-in-and-elim-right-form
       (proof-to-ppat (proof-in-and-elim-right-form-to-kernel proof)
		      id-deco?)))
     ((proof-in-all-intro-form)
      (make-proof-in-allnc-intro-form
       (proof-in-all-intro-form-to-var proof)
       (proof-to-ppat (proof-in-all-intro-form-to-kernel proof) id-deco?)))
     ((proof-in-allnc-intro-form)
      (make-proof-in-allnc-intro-form
       (proof-in-allnc-intro-form-to-var proof)
       (proof-to-ppat (proof-in-allnc-intro-form-to-kernel proof) id-deco?)))
     ((proof-in-all-elim-form)
      (make-proof-in-allnc-elim-form
       (proof-to-ppat (proof-in-all-elim-form-to-op proof) id-deco?)
       (proof-in-all-elim-form-to-arg proof)))
     ((proof-in-allnc-elim-form)
      (make-proof-in-allnc-elim-form
       (proof-to-ppat (proof-in-allnc-elim-form-to-op proof) id-deco?)
       (proof-in-allnc-elim-form-to-arg proof)))
     (else (myerror "proof-to-ppat" "proof tag expected" (tag proof))))))

;; ppat-and-decseq-and-availavars-to-proof-and-decavars with named let
;; rather than a do loop in impnc-elim case.

(define (ppat-and-decseq-and-availavars-to-proof-and-decavars
	 ppat decavars decfla availavars id-deco? . name-and-altname)
  (or ;application of aconst name by less extending aconst altname possible
   (and
    (pair? name-and-altname)
    (or (and (predicate-form? decfla)
	     (idpredconst-form? (predicate-form-to-predicate decfla)))
					;temporarily we still have
	(ex-form? decfla)
	(and-form? decfla))
    (let ((op (proof-in-elim-form-to-final-op ppat))
	  (args (proof-in-elim-form-to-args ppat)))
      (and
       (proof-in-aconst-form? op)
       (let ((opname (aconst-to-name (proof-in-aconst-form-to-aconst op))))
	 (and
	  (or (assoc opname THEOREMS) (assoc opname GLOBAL-ASSUMPTIONS))
	  (list? name-and-altname) (= 2 (length name-and-altname))
	  (string=? opname (car name-and-altname))
	  (let* ((name (car name-and-altname))
		 (altname (cadr name-and-altname))
		 (info1 (or (assoc name THEOREMS)
			    (assoc name GLOBAL-ASSUMPTIONS)))
		 (info2 (or (assoc altname THEOREMS)
			    (assoc altname GLOBAL-ASSUMPTIONS))))
	    (and
	     info1 info2
	     (let* ((altop (make-proof-in-aconst-form (cadr info2)))
		    (extending-proof
		     (op-and-args-and-altop-and-decfla-and-availavars-to-proof
		      op args altop decfla availavars id-deco?)))
	       (and extending-proof
		    (list extending-proof decavars))))))))))
   					;else carry on
   (case (tag ppat)
     ((proof-in-avar-form)
      (let*
	  ((avar (proof-in-avar-form-to-avar ppat))
	   (test (member-wrt avar=? avar decavars))
	   (decavar
	    (if test (car test)
		(myerror
		 "ppat-and-decseq-and-availavars-to-proof-and-decavars"
		 "avar" (avar-to-name avar) (avar-to-index avar)
		 "missing in decavars"
		 (pp-context decavars))))
	   (decavar-fla (avar-to-formula decavar))
	   (ext-fla (dec-variants-to-lub id-deco? decfla decavar-fla))
	   (ext-decavar
	    (make-avar ext-fla (avar-to-index avar) (avar-to-name avar))))
	(list (make-proof-in-avar-form ext-decavar)
	      (list ext-decavar))))
     ((proof-in-aconst-form)
      (let* ((aconst (proof-in-aconst-form-to-aconst ppat))
	     (name (aconst-to-name aconst)))
	(if
	 (not id-deco?)
	 (list (aconst-and-decfla-to-proof aconst decfla id-deco?) '())
	 (cond
	  ((string=? "Intro" name)
	   (list (intro-aconst-and-decfla-to-min-intro-proof aconst decfla)
		 '()))
	  ((string=? "Elim" name)
	   (list (elim-aconst-and-decfla-to-min-elim-proof aconst decfla) '()))
	  (else
	   (list (aconst-and-decfla-to-proof aconst decfla id-deco?) '()))))))
     ((proof-in-impnc-intro-form)
      (let* ((kernel (proof-in-impnc-intro-form-to-kernel ppat))
	     (avar (proof-in-impnc-intro-form-to-avar ppat))
	     (decprem (imp-impnc-form-to-premise decfla))
	     (decconc (imp-impnc-form-to-conclusion decfla))
	     (decavar
	      (make-avar decprem (avar-to-index avar) (avar-to-name avar)))
	     (prem-of-nulltype?
	      (if id-deco?
		  (formula-of-nulltype-under-extension? decprem)
		  (formula-of-nulltype? decprem)))
	     (decavars-for-kernel (if prem-of-nulltype?
				      decavars
				      (cons decavar decavars)))
	     (dec-kernel-proof-and-ext-decavars
	      (apply ppat-and-decseq-and-availavars-to-proof-and-decavars
		     kernel decavars-for-kernel decconc
		     (cons avar availavars) id-deco?
		     name-and-altname))
	     (dec-kernel-proof (car dec-kernel-proof-and-ext-decavars))
	     (ext-decavars (cadr dec-kernel-proof-and-ext-decavars))
	     (reduced-ext-decavars (if prem-of-nulltype?
				       ext-decavars
				       (remove-wrt avar=? avar ext-decavars)))
	     (test (member-wrt avar=? avar ext-decavars))
	     (ext-decavar (if test (car test) decavar)))
	(list
	 (if (and
	      (impnc-form? decfla)
	      (not (member-wrt avar=? avar (proof-to-cvars dec-kernel-proof))))
	     (make-proof-in-impnc-intro-form ext-decavar dec-kernel-proof)
	     (make-proof-in-imp-intro-form ext-decavar dec-kernel-proof))
	 reduced-ext-decavars)))
     ((proof-in-impnc-elim-form)
      (let* ((op (proof-in-impnc-elim-form-to-op ppat))
	     (arg (proof-in-impnc-elim-form-to-arg ppat))
	     (arg-of-nulltype?
	      (if id-deco?
		  (formula-of-nulltype-under-extension? (proof-to-formula arg))
		  (formula-of-nulltype? (proof-to-formula arg))))
	     (orig-op-avars (proof-to-free-cr-avars op id-deco?))
	     (orig-arg-avars (proof-to-free-cr-avars arg id-deco?))
	     (orig-avars-int
	      (intersection-wrt avar=? orig-op-avars orig-arg-avars))
	     (orig-avars-lft
	      (set-minus-wrt avar=? orig-op-avars orig-avars-int))
	     (orig-avars-rht
	      (set-minus-wrt avar=? orig-arg-avars orig-avars-int))
	     (avars-to-int
	      (lambda (avars)
		(list-transform-positive avars
		  (lambda (x) (member-wrt avar=? x orig-avars-int)))))
	     (avars-to-lft
	      (lambda (avars)
		(list-transform-positive avars
		  (lambda (x) (member-wrt avar=? x orig-avars-lft)))))
	     (avars-to-rht
	      (lambda (avars)
		(list-transform-positive avars
		  (lambda (x) (member-wrt avar=? x orig-avars-rht)))))
	     (orig-decavars-int (avars-to-int decavars))
	     (orig-decavars-lft (avars-to-lft decavars))
	     (orig-decavars-rht (avars-to-rht decavars))
					;apply IH to op
	     (init-op-proof-and-decavars
	      (apply
	       ppat-and-decseq-and-availavars-to-proof-and-decavars
	       op (append orig-decavars-lft orig-decavars-int)
	       (make-impnc (impnc-form-to-premise (proof-to-formula op))
			   decfla)
	       availavars id-deco?
	       name-and-altname))
	     (init-op-proof (car init-op-proof-and-decavars))
	     (init-op-decavars (cadr init-op-proof-and-decavars))
	     (init-op-decfla (proof-to-formula init-op-proof))
					;apply IH to arg if arg is c.r.
	     (init-arg-proof-and-decavars
	      (if arg-of-nulltype?
		  (list arg '())
		  (apply
		   ppat-and-decseq-and-availavars-to-proof-and-decavars
		   arg (append (avars-to-int init-op-decavars)
			       orig-decavars-rht)
		   (imp-impnc-form-to-premise init-op-decfla)
		   availavars id-deco?
		   name-and-altname))))
	(let
	    loop
	  ((i 0)
	   (op-proof-and-decavars init-op-proof-and-decavars)
	   (arg-proof-and-decavars init-arg-proof-and-decavars))
	  (if (< 0 i) (begin (display i) (display " ")))
	  (let* ((op-proof (car op-proof-and-decavars))
		 (op-decavars (cadr op-proof-and-decavars))
		 (op-fla (proof-to-formula op-proof))
		 (arg-proof (car arg-proof-and-decavars))
		 (arg-decavars (cadr arg-proof-and-decavars))
		 (arg-fla (proof-to-formula arg-proof))
		 (op-prem (imp-impnc-form-to-premise op-fla))
		 (op-conc (imp-impnc-form-to-conclusion op-fla))
		 (op-bicon (bicon-form-to-bicon op-fla))
		 (new-op-fla
		  (if (even? i) (make-bicon op-bicon arg-fla op-conc) op-fla))
		 (new-arg-fla
		  (if (even? i) arg-fla op-prem))
		 (new-op-prem (imp-impnc-form-to-premise new-op-fla))
		 (new-op-conc (imp-impnc-form-to-conclusion new-op-fla)))
	    (if ;Termination condition
	     (or (and (zero? i)
		      (if id-deco?
			  (formula-of-nulltype-under-extension? arg-fla)
			  (formula-of-nulltype? arg-fla)))
		 (and (apply and-op
			     (map (lambda (fla1 fla2)
				    (classical-formula=? fla1 fla2))
				  (map avar-to-formula
				       (avars-to-int op-decavars))
				  (map avar-to-formula
				       (avars-to-int arg-decavars))))
		      (classical-formula=? op-prem arg-fla)))
	     (if (and (zero? i)
		      (if id-deco?
			  (formula-of-nulltype-under-extension? arg-fla)
			  (formula-of-nulltype? arg-fla)))
		 (list (make-proof-in-imp-elim-form op-proof arg-proof)
		       (append op-decavars (avars-to-rht arg-decavars)))
		 (list (if (imp-form? op-fla)
			   (make-proof-in-imp-elim-form op-proof arg-proof)
			   (make-proof-in-impnc-elim-form op-proof arg-proof))
		       (append op-decavars (avars-to-rht arg-decavars))))
					;else carry on
	     (if
	      (even? i) ;then work on op
	      (loop (+ i 1)
		    (apply
		     ppat-and-decseq-and-availavars-to-proof-and-decavars
		     op (append (avars-to-lft op-decavars)
				(avars-to-int arg-decavars))
		     (make-imp new-arg-fla new-op-conc)
		     availavars id-deco?
		     name-and-altname)
		    arg-proof-and-decavars)
					;else work on arg
	      (loop (+ i 1)
		    op-proof-and-decavars
		    (apply
		     ppat-and-decseq-and-availavars-to-proof-and-decavars
		     arg (append (avars-to-int op-decavars)
				 (avars-to-rht arg-decavars))
		     new-op-prem availavars id-deco?
		     name-and-altname))))))))
     ((proof-in-allnc-intro-form)
      (let* ((var (proof-in-allnc-intro-form-to-var ppat))
	     (kernel (proof-in-allnc-intro-form-to-kernel ppat))
	     (decvar (all-allnc-form-to-var decfla))
	     (deckernel (all-allnc-form-to-kernel decfla))
	     (subst-deckernel
	      (if (equal? var decvar)
		  deckernel
		  (formula-subst deckernel decvar
				 (make-term-in-var-form var))))
	     (reduced-availavars ;remove avars violating the variable condition
	      (list-transform-positive availavars
		(lambda (avar)
		  (not (member var (formula-to-free
				    (avar-to-formula avar)))))))
	     (ext-proof-and-ext-decavars
	      (apply
	       ppat-and-decseq-and-availavars-to-proof-and-decavars
	       kernel decavars subst-deckernel
	       reduced-availavars id-deco?
	       name-and-altname))
	     (ext-proof (car ext-proof-and-ext-decavars))
	     (ext-decavars (cadr ext-proof-and-ext-decavars)))
	(list (if (and (allnc-form? decfla)
		       (not (member var (proof-to-cvars ext-proof))))
		  (make-proof-in-allnc-intro-form var ext-proof)
		  (make-proof-in-all-intro-form var ext-proof))
	      ext-decavars)))
     ((proof-in-allnc-elim-form)
      (let* ((op (proof-in-allnc-elim-form-to-op ppat))
	     (arg (proof-in-allnc-elim-form-to-arg ppat))
	     (op-formula (proof-to-formula op))
	     (var (allnc-form-to-var op-formula))
	     (kernel (allnc-form-to-kernel op-formula))
	     (allnc-decfla
	      (make-allnc var (dec-variants-to-lub id-deco? kernel decfla)))
	     (ext-proof-and-ext-decavars
	      (apply
	       ppat-and-decseq-and-availavars-to-proof-and-decavars
	       op decavars allnc-decfla availavars id-deco?
	       name-and-altname))
	     (ext-proof (car ext-proof-and-ext-decavars))
	     (ext-decavars (cadr ext-proof-and-ext-decavars)))
	(list (if (allnc-form? (proof-to-formula ext-proof))
		  (make-proof-in-allnc-elim-form ext-proof arg)
		  (make-proof-in-all-elim-form ext-proof arg))
	      ext-decavars)))
					;to be rewritten as in impnc-elim:
     ((proof-in-and-intro-form)
      (let* ((left (proof-in-and-intro-form-to-left ppat))
	     (right (proof-in-and-intro-form-to-right ppat))
	     (left-of-nulltype?
	      (if
	       id-deco?
	       (formula-of-nulltype-under-extension? (proof-to-formula left))
	       (formula-of-nulltype? (proof-to-formula left))))
	     (right-of-nulltype?
	      (if
	       id-deco?
	       (formula-of-nulltype-under-extension? (proof-to-formula right))
	       (formula-of-nulltype? (proof-to-formula right))))
	     (orig-left-avars (proof-to-free-cr-avars left id-deco?))
	     (orig-right-avars (proof-to-free-cr-avars right id-deco?))
	     (orig-avars-int
	      (intersection-wrt avar=? orig-left-avars orig-right-avars))
	     (orig-avars-lft
	      (set-minus-wrt avar=? orig-left-avars orig-avars-int))
	     (orig-avars-rht
	      (set-minus-wrt avar=? orig-right-avars orig-avars-int))
	     (avars-to-int
	      (lambda (avars)
		(list-transform-positive avars
		  (lambda (x) (member-wrt avar=? x orig-avars-int)))))
	     (avars-to-lft
	      (lambda (avars)
		(list-transform-positive avars
		  (lambda (x) (member-wrt avar=? x orig-avars-lft)))))
	     (avars-to-rht
	      (lambda (avars)
		(list-transform-positive avars
		  (lambda (x) (member-wrt avar=? x orig-avars-rht)))))
	     (orig-decavars-int (avars-to-int decavars))
	     (orig-decavars-lft (avars-to-lft decavars))
	     (orig-decavars-rht (avars-to-rht decavars))
					;apply IH to left if left is c.r.
	     (init-left-proof-and-decavars
	      (if left-of-nulltype?
		  (list left '())
		  (apply
		   ppat-and-decseq-and-availavars-to-proof-and-decavars
		   left (append orig-decavars-lft orig-decavars-int)
		   (and-form-to-left decfla)
		   availavars id-deco?
		   name-and-altname)))
	     (init-left-proof (car init-left-proof-and-decavars))
	     (init-left-decavars (cadr init-left-proof-and-decavars))
	     (init-left-decfla (proof-to-formula init-left-proof))
					;apply IH to right if right is c.r.
	     (init-right-proof-and-decavars
	      (if
	       right-of-nulltype?
	       (list right '())
	       (apply
		ppat-and-decseq-and-availavars-to-proof-and-decavars
		right (append (avars-to-int init-left-decavars)
			      orig-decavars-rht)
		(and-form-to-right decfla)
		availavars id-deco?
		name-and-altname))))
	(let
	    loop
	  ((i 0)
	   (left-proof-and-decavars init-left-proof-and-decavars)
	   (right-proof-and-decavars init-right-proof-and-decavars))
	  (if (< 0 i) (begin (display i) (display " ")))
	  (let* ((left-proof (car left-proof-and-decavars))
		 (left-decavars (cadr left-proof-and-decavars))
		 (left-fla (proof-to-formula left-proof))
		 (right-proof (car right-proof-and-decavars))
		 (right-decavars (cadr right-proof-and-decavars))
		 (right-fla (proof-to-formula right-proof)))
	    (if ;Termination condition
	     (apply and-op
		    (map (lambda (fla1 fla2) (classical-formula=? fla1 fla2))
			 (map avar-to-formula (avars-to-int left-decavars))
			 (map avar-to-formula (avars-to-int right-decavars))))
	     (list (make-proof-in-and-intro-form left-proof right-proof)
		   (append left-decavars (avars-to-rht right-decavars)))
					;else carry on
	     (if
	      (even? i) ;then work on left
	      (loop (+ i 1)
		    (apply
		     ppat-and-decseq-and-availavars-to-proof-and-decavars
		     left (append (avars-to-lft left-decavars)
				  (avars-to-int right-decavars))
		     left-fla
		     availavars id-deco?
		     name-and-altname)
		    right-proof-and-decavars)
					;else work on right
	      (loop (+ i 1)
		    left-proof-and-decavars
		    (apply
		     ppat-and-decseq-and-availavars-to-proof-and-decavars
		     right (append (avars-to-int left-decavars)
				   (avars-to-rht right-decavars))
		     right-fla availavars id-deco?
		     name-and-altname))))))))
     ((proof-in-and-elim-left-form)
      (let* ((kernel (proof-in-and-elim-left-form-to-kernel ppat))
	     (ext-proof-and-ext-decavars
	      (apply
	       ppat-and-decseq-and-availavars-to-proof-and-decavars
	       kernel decavars
	       (make-and decfla
			 (and-form-to-right (proof-to-formula kernel)))
	       availavars id-deco?
	       name-and-altname))
	     (ext-proof (car ext-proof-and-ext-decavars))
	     (ext-decavars (cadr ext-proof-and-ext-decavars)))
	(list (make-proof-in-and-elim-left-form ext-proof)
	      ext-decavars)))
     ((proof-in-and-elim-right-form)
      (let* ((kernel (proof-in-and-elim-right-form-to-kernel ppat))
	     (ext-proof-and-ext-decavars
	      (apply
	       ppat-and-decseq-and-availavars-to-proof-and-decavars
	       kernel decavars
	       (make-and (and-form-to-left (proof-to-formula kernel))
			 decfla)
	       availavars id-deco?
	       name-and-altname))
	     (ext-proof (car ext-proof-and-ext-decavars))
	     (ext-decavars (cadr ext-proof-and-ext-decavars)))
	(list (make-proof-in-and-elim-right-form ext-proof)
	      ext-decavars)))
     (else ;(dp ppat)
      (myerror "ppat-and-decseq-and-availavars-to-proof-and-decavars"
	       "unexpected proof tag"
	       (tag ppat))))))

;; op-and-args-and-altop-and-decfla-and-availavars-to-proof assumes
;; that op applied to args proves an extension of decfla, and that
;; altop differs from op only in possibly requiring additional
;; premises.  In case id-deco? this is w.r.t. full extension,
;; otherwise w.r.t. imp-all extension.  It is tested whether altop
;; applied to args and some of availavars is between op applied to args
;; and decfla w.r.t. the respective extension.  If so, a proof based on
;; altop is returned, else #f.

(define (op-and-args-and-altop-and-decfla-and-availavars-to-proof
	 op args altop decfla availavars id-deco?)
  (do ((altproof-and-restargs-and-proof
	(list altop args op)
	(let* ((altproof (car altproof-and-restargs-and-proof))
	       (restargs (cadr altproof-and-restargs-and-proof))
	       (proof (caddr altproof-and-restargs-and-proof))
	       (altfla (proof-to-formula altproof))
	       (fla (proof-to-formula proof)))
	  (cond
	   ((or (and (all-allnc-form? fla)
		     (all-allnc-form? altfla))
		(and (imp-impnc-form? fla)
		     (imp-impnc-form? altfla)
		     (formula=? (imp-impnc-form-to-premise fla)
				(imp-impnc-form-to-premise altfla))))
	    (list (mk-proof-in-elim-form altproof (car restargs))
		  (cdr restargs)
		  (mk-proof-in-elim-form proof (car restargs))))
	   ((and (imp-impnc-form? altfla)
		 (member-wrt formula=?
			     (imp-impnc-form-to-premise altfla)
			     (map avar-to-formula availavars)))
	    (let ((availavar
		   (car (list-transform-positive availavars
			  (lambda (avar)
			    (formula=? (imp-impnc-form-to-premise altfla)
				       (avar-to-formula avar)))))))
	      (list (mk-proof-in-elim-form
		     altproof (make-proof-in-avar-form availavar))
		    restargs
		    proof)))
	   (else (list #f restargs proof))))))
      ((or (not (car altproof-and-restargs-and-proof))
	   (let* ((altproof (car altproof-and-restargs-and-proof))
		  (proof (caddr altproof-and-restargs-and-proof))
		  (fla (proof-to-formula proof))
		  (altfla (proof-to-formula altproof)))
	     (and (dec-variants? fla altfla id-deco?)
		  (extending-dec-variants? fla altfla id-deco?)
		  (dec-variants? altfla decfla id-deco?)
		  (extending-dec-variants? altfla decfla id-deco?))))
       (car altproof-and-restargs-and-proof))))

;; A test function for proof patterns.

(define (ppat? x)
  (and (proof-form? x)
       (let* ((formula (proof-to-formula x)))
	 (or (formula-of-nulltype? formula)
	     (case (tag x)
	       ((proof-in-avar-form proof-in-aconst-form) #t)
	       ((proof-in-impnc-intro-form)
		(ppat? (proof-in-impnc-intro-form-to-kernel x)))
	       ((proof-in-impnc-elim-form)
		(and (ppat? (proof-in-impnc-elim-form-to-op x))
		     (ppat? (proof-in-impnc-elim-form-to-arg x))))
	       ((proof-in-allnc-intro-form)
		(ppat? (proof-in-allnc-intro-form-to-kernel x)))
	       ((proof-in-allnc-elim-form)
		(ppat? (proof-in-allnc-elim-form-to-op x)))
	       (else (myerror "ppat?" "unexpected proof tag" (tag x))))))))

;; In aconst-and-decfla-to-proof a proof is returned (not an aconst)
;; because of possible all's instead of allnc's binding free variables
;; of the instantiated formula.  Hence all-allnc-form-to-prefix and
;; aconst-and-prefix-to-proof-of-modified-aconst suffice.

(define (aconst-and-decfla-to-proof aconst decfla id-deco?)
  (let* ((name (aconst-to-name aconst))
	 (kind (aconst-to-kind aconst))
	 (uninst-fla (aconst-to-uninst-formula aconst))
	 (repro-data (aconst-to-repro-data aconst))
	 (extended-tpsubst (aconst-and-dec-inst-formula-to-extended-tpsubst
			    aconst decfla id-deco?))
	 (extended-aconst-without-repro-data
	  (make-aconst name kind uninst-fla extended-tpsubst))
	 (extended-aconst
	  (apply make-aconst
		 name kind uninst-fla extended-tpsubst
		 (aconst-to-computed-repro-data
		  extended-aconst-without-repro-data)))
	 (extended-inst-formula (aconst-to-inst-formula extended-aconst))
	 (free (formula-to-free extended-inst-formula))
	 (prefix (all-allnc-form-to-prefix decfla (length free))))
    (aconst-and-prefix-to-proof-of-modified-aconst extended-aconst prefix)))

(define (intro-aconst-and-decfla-to-min-intro-proof aconst decfla)
  (let* ((repro-data (aconst-to-repro-data aconst))
	 (i (car repro-data))
	 (uninst-fla (aconst-to-uninst-formula aconst))
	 (tpsubst (aconst-to-tpsubst aconst))
	 (uninst-idpc-fla (imp-impnc-form-to-final-conclusion
			   (all-allnc-form-to-final-kernel uninst-fla)))
	 (idpc (if (predicate-form? uninst-idpc-fla)
		   (predicate-form-to-predicate uninst-idpc-fla)
		   (myerror "intro-aconst-and-decfla-to-min-intro-proof"
			    "predicate form expected" uninst-idpc-fla)))
	 (idpc-name (idpredconst-to-name idpc))
	 (given-clauses (idpredconst-name-to-clauses idpc-name))
	 (l (length given-clauses))
	 (variant-idpc-names ;assumed to be in increasing order in IDS
	  (list-transform-positive (map car IDS)
	    (lambda (name)
	      (let ((clauses (idpredconst-name-to-clauses name)))
		(and (= (length given-clauses) (length clauses))
		     (apply and-op (map (lambda (cl1 cl2)
					  (dec-variants-up-to-pvars? cl1 cl2))
					given-clauses clauses)))))))
	 (inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (f (length free))
	 (decfla-without-param-vars (all-allnc-form-to-final-kernel decfla f))
	 (dec-kernel
	  (all-allnc-form-to-final-kernel decfla-without-param-vars))
	 (dec-idpc-fla (imp-impnc-form-to-final-conclusion dec-kernel))
	 (dec-idpc (predicate-form-to-predicate dec-idpc-fla))
	 (dec-idpc-name (idpredconst-to-name dec-idpc))
	 (dec-idpc-clauses (idpredconst-name-to-clauses dec-idpc-name))
	 (dec-idpc-clause
	  (if (= l (length dec-idpc-clauses))
	      (list-ref dec-idpc-clauses i)
	      (myerror "intro-aconst-and-decfla-to-min-intro-proof"
		       l "clauses expected for" dec-idpc-name)))
	 (fitting-idpc-names ;such that i-th clause matches dec-idpc-clause
	  (list-transform-positive variant-idpc-names
	    (lambda (name)
	      (let ((clauses (idpredconst-name-to-clauses name)))
		(and (= l (length clauses))
		     (huet-match ;do not ignore decorations
		      (list-ref clauses i) dec-idpc-clause #f))))))
	 (min-idpc-name
	  (if (pair? fitting-idpc-names)
	      (car fitting-idpc-names)
	      (myerror "intro-aconst-and-decfla-to-min-intro-proof"
		       "fitting idpredconst missing for" decfla)))
	 (min-dec-idpc
	  (make-idpredconst min-idpc-name
			    (idpredconst-to-types dec-idpc)
			    (idpredconst-to-cterms dec-idpc)))
	 (min-aconst
	  (number-and-idpredconst-to-intro-aconst i min-dec-idpc))
	 (prefix (all-allnc-form-to-prefix decfla f)))
    (aconst-and-prefix-to-proof-of-modified-aconst min-aconst prefix)))

(define (elim-aconst-and-decfla-to-min-elim-proof aconst decfla)
  (let* ((name (aconst-to-name aconst)) ;"Elim"
	 (kind (aconst-to-kind aconst)) ;'axiom
	 (uninst-fla (aconst-to-uninst-formula aconst))
	 (tpsubst (aconst-to-tpsubst aconst))
	 (uninst-idpc-fla
	  (if (imp-form? uninst-fla)
	      (imp-form-to-premise uninst-fla)
	      (myerror "elim-aconst-and-decfla-to-min-elim-proof"
		       "unexpected uninstatiated formula" uninst-fla)))
	 (idpc (if (predicate-form? uninst-idpc-fla)
		   (predicate-form-to-predicate uninst-idpc-fla)
		   (myerror "elim-aconst-and-decfla-to-min-elim-proof"
			    "predicate form expected" uninst-idpc-fla)))
	 (idpc-name (idpredconst-to-name idpc))
	 (given-clauses (idpredconst-name-to-clauses idpc-name))
	 (l (length given-clauses))
	 (variant-idpc-names ;assumed to be in increasing order in IDS
	  (list-transform-positive (map car IDS)
	    (lambda (name)
	      (let ((clauses (idpredconst-name-to-clauses name)))
		(and (= l (length clauses))
		     (apply and-op (map (lambda (cl1 cl2)
					  (dec-variants-up-to-pvars? cl1 cl2))
					given-clauses clauses)))))))
	 (inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (f (length free))
	 (dec-kernel (all-allnc-form-to-final-kernel decfla))
	 (dec-idpc-fla (imp-form-to-premise dec-kernel))
	 (dec-idpc (predicate-form-to-predicate dec-idpc-fla))
	 (dec-idpc-name (idpredconst-to-name dec-idpc))
	 (dec-args (predicate-form-to-args dec-idpc-fla))
	 (dec-concl (imp-form-to-conclusion dec-kernel))
	 (dec-clauses (imp-impnc-form-to-premises dec-concl l))
	 (dec-final-concl (imp-impnc-form-to-final-conclusion dec-concl l))
	 (fitting-idpc-names ;unique s.t. clauses match dec-clauses
	  (list-transform-positive variant-idpc-names
	    (lambda (name)
	      (let ((clauses (idpredconst-name-to-clauses name)))
		(apply and-op
		       (map (lambda (cl dec-cl)
			      (huet-match cl dec-cl #f)) ;do not ignore decs
			    clauses dec-clauses))))))
	 (fitting-idpc-name-from-clauses-deco ;the least extended one
	  (if (pair? fitting-idpc-names)
	      (car fitting-idpc-names)
	      (myerror "elim-aconst-and-decfla-to-min-elim-proof"
		       "fitting idpredconst missing for" decfla)))
	 (min-idpc-name ;from clauses deco and dec-idpc-name
	  (car (intersection
		(member dec-idpc-name variant-idpc-names)
		(member (car fitting-idpc-names) variant-idpc-names))))
	 (min-dec-idpc
	  (make-idpredconst min-idpc-name
			    (idpredconst-to-types dec-idpc)
			    (idpredconst-to-cterms dec-idpc)))
	 (min-dec-idpc-fla (apply make-predicate-formula
				  min-dec-idpc dec-args))
	 (min-imp-fla (make-imp min-dec-idpc-fla dec-final-concl))
	 (min-elim-aconst (imp-formulas-to-elim-aconst min-imp-fla))
	 (min-uninst-fla (aconst-to-uninst-formula min-elim-aconst))
	 (extended-tpsubst (aconst-and-dec-inst-formula-to-extended-tpsubst
			    min-elim-aconst decfla #t)) ;id-deco? is true
	 (aconst-without-repro-formulas
	  (make-aconst name kind min-uninst-fla extended-tpsubst))
	 (min-aconst
	  (apply make-aconst
		 name kind min-uninst-fla extended-tpsubst
		 (aconst-to-computed-repro-data
		  aconst-without-repro-formulas)))
	 (prefix (all-allnc-form-to-prefix decfla f)))
    (aconst-and-prefix-to-proof-of-modified-aconst min-aconst prefix)))

;; In an aconst the f free variables of its instantiated formula are
;; allnc-quantified.  Let prefix be a list of lists ('all/allnc var) of
;; length f.  aconst-and-prefix-to-proof-of-modified-aconst returns a
;; proof of a modified aconst with the new prefix.  From a decoration
;; of the instantiated formula of an aconst prefix can be computed by
;; (all-allnc-form-to-prefix decfla (length free)).

(define (aconst-and-prefix-to-proof-of-modified-aconst aconst prefix)
  (let* ((inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (rev-of-largest-prefix-ending-with-all
	  (if (and (list? prefix) (= (length prefix) (length free)))
	      (do ((rp (reverse prefix) (cdr rp)))
		  ((or (null? rp) (eq? 'all (caar rp)))
		   rp))
	      (myerror "aconst-and-prefix-to-proof-of-modified-aconst"
		       "prefix of length" (length free) "expected")))
	 (vars (reverse (map cadr rev-of-largest-prefix-ending-with-all)))
	 (allnc-elim-proof
	  (apply mk-proof-in-elim-form
		 (make-proof-in-aconst-form aconst)
		 (map make-term-in-var-form vars))))
    (do ((rp rev-of-largest-prefix-ending-with-all (cdr rp))
	 (res allnc-elim-proof
	      (if (eq? 'all (caar rp))
		  (make-proof-in-all-intro-form (cadar rp) res)
		  (make-proof-in-allnc-intro-form (cadar rp) res))))
	((null? rp) res))))

;; Alternative: (cr-strengthened-dec-variants-to-proof formula1 formula2).
;; It is assumed that both formulas are c.r., and that formula1 is a
;; computational strengthening of formula2 (in the sense of
;; strengthened-dec-variants? , i.e., 7.2.2 in pc10asl, P. 330)

(define (cr-strengthened-dec-variants-to-proof formula1 formula2)
  (let ((u (formula-to-new-avar formula1)))
    (cond
     ((bicon-form? formula1)
      (cond
       ((and (imp-form? formula1) (imp-form? formula2))
	(let* ((prem1 (imp-form-to-premise formula1))
	       (conc1 (imp-form-to-conclusion formula1))
	       (prem2 (imp-form-to-premise formula2))
	       (conc2 (imp-form-to-conclusion formula2))
	       (prevprem (cr-strengthened-dec-variants-to-proof prem2 prem1))
	       (prevconc (cr-strengthened-dec-variants-to-proof conc1 conc2))
	       (u2 (formula-to-new-avar prem2)))

;;                                                        |
;;                                                     A2 -> A1  u2:A2
;;                                                     ---------------
;;                                       u: A1 -> B1          A1
;;                               |       -----------------------
;;                            B1 -> B2               B1
;;                            -------------------------
;;                                        B2

	  (mk-proof-in-intro-form
	   u u2 (make-proof-in-imp-elim-form
		 prevconc (make-proof-in-imp-elim-form
			   (make-proof-in-avar-form u)
			   (make-proof-in-imp-elim-form
			    prevprem (make-proof-in-avar-form u2)))))))
       ((and (impnc-form? formula1) (impnc-form? formula2))
	(let* ((prem1 (impnc-form-to-premise formula1))
	       (conc1 (impnc-form-to-conclusion formula1))
	       (prem2 (impnc-form-to-premise formula2))
	       (conc2 (impnc-form-to-conclusion formula2))
	       (prevprem (cr-strengthened-dec-variants-to-proof prem2 prem1))
	       (prevconc (cr-strengthened-dec-variants-to-proof conc1 conc2))
	       (u2 (formula-to-new-avar prem2)))
	  (make-proof-in-imp-intro-form
	   u (make-proof-in-impnc-intro-form
	      u2 (make-proof-in-imp-elim-form
		  prevconc (make-proof-in-impnc-elim-form
			    (make-proof-in-avar-form u)
			    (make-proof-in-imp-elim-form
			     prevprem (make-proof-in-avar-form u2))))))))
       ((and (impnc-form? formula1) (imp-form? formula2))
	(let* ((prem1 (impnc-form-to-premise formula1))
	       (conc1 (impnc-form-to-conclusion formula1))
	       (prem2 (imp-form-to-premise formula2))
	       (conc2 (imp-form-to-conclusion formula2))
	       (prevprem (cr-strengthened-dec-variants-to-proof prem2 prem1))
	       (prevconc (cr-strengthened-dec-variants-to-proof conc1 conc2))
	       (u2 (formula-to-new-avar prem2)))
	  (mk-proof-in-intro-form
	   u u2 (make-proof-in-imp-elim-form
		 prevconc (make-proof-in-impnc-elim-form
			   (make-proof-in-avar-form u)
			   (make-proof-in-imp-elim-form
			    prevprem (make-proof-in-avar-form u2)))))))
       ((and (imp-form? formula1) (impnc-form? formula2))
	(let* ((prem1 (imp-form-to-premise formula1))
	       (conc1 (imp-form-to-conclusion formula1))
	       (prem2 (impnc-form-to-premise formula2))
	       (conc2 (impnc-form-to-conclusion formula2))
	       (prevconc (cr-strengthened-dec-variants-to-proof conc1 conc2))
	       (u2 (formula-to-new-avar prem2)))

;;                                       u: A1 -> B1       u2:A2
;;                               |       -----------------------
;;                            B1 -> B2               B1
;;                            -------------------------
;;                                        B2

;; A1 and A2 are decoration variants of nulltype, hence considered equal.

	  (make-proof-in-imp-intro-form
	   u (make-proof-in-impnc-intro-form
	      u2 (make-proof-in-imp-elim-form
		  prevconc (make-proof-in-imp-elim-form
			    (make-proof-in-avar-form u)
			    (make-proof-in-avar-form u2)))))))
       (else (myerror "cr-strengthened-dec-variants-to-proof"
		      "not implemented for" formula1 formula2))))
     ((quant-form? formula1)
      (let* ((vars1 (quant-form-to-vars formula1))
	     (vars2 (quant-form-to-vars formula2))
	     (kernel1 (quant-form-to-kernel formula1))
	     (kernel2 (quant-form-to-kernel formula2))
	     (free (formula-to-free formula1))
	     (newvars2 (map (lambda (var) (if (member var free)
					      (var-to-new-var var)
					      var))
			    vars2))
	     (subst-kernel1
	      (if (equal? vars1 newvars2)
		  kernel1
		  (formula-substitute
		   kernel1
		   (make-substitution
		    vars1 (map make-term-in-var-form newvars2)))))
	     (subst-kernel2
	      (if (equal? vars2 newvars2)
		  kernel2
		  (formula-substitute
		   kernel2
		   (make-substitution
		    vars2 (map make-term-in-var-form newvars2)))))
	     (prev (cr-strengthened-dec-variants-to-proof
		    subst-kernel1 subst-kernel2)))
	(cond
	 ((and (all-form? formula1) (all-form? formula2))

;;                                                     u: all x A1(x)  y
;;                                         |           -----------------
;;                                   A1(y) -> A2(y)             A1(y)
;;                                   ----------------------------
;;                                                  A2(y)

	  (make-proof-in-imp-intro-form
	   u (make-proof-in-all-intro-form
	      (car newvars2) (make-proof-in-imp-elim-form
			      prev (make-proof-in-all-elim-form
				    (make-proof-in-avar-form u)
				    (make-term-in-var-form (car newvars2)))))))
	 ((and (allnc-form? formula1) (allnc-form? formula2))
	  (make-proof-in-imp-intro-form
	   u (make-proof-in-allnc-intro-form
	      (car newvars2) (make-proof-in-imp-elim-form
			      prev (make-proof-in-allnc-elim-form
				    (make-proof-in-avar-form u)
				    (make-term-in-var-form (car newvars2)))))))
	 ((and (allnc-form? formula1) (all-form? formula2))
	  (make-proof-in-imp-intro-form
	   u (make-proof-in-all-intro-form
	      (car newvars2) (make-proof-in-imp-elim-form
			      prev (make-proof-in-allnc-elim-form
				    (make-proof-in-avar-form u)
				    (make-term-in-var-form (car newvars2)))))))
	 (else (myerror "cr-strengthened-dec-variants-to-proof"
			"not implemented for" formula1 formula2)))))
     (else
      (if (formula=? formula1 formula2)
	  (make-proof-in-imp-intro-form
	   u (make-proof-in-avar-form u))
	  (myerror "cr-strengthened-dec-variants-to-proof"
		   "equal formulas expected" formula1 formula2))))))

;; 10-2. Normalization by evaluation
;; =================================

;; Normalization of proofs will be done by reduction to normalization of
;; terms.  (1) Construct a term from the proof.  To do this properly,
;; create for every free avar in the given proof a new var whose type
;; comes from the formula of the avar.  Store this information.  Note
;; that in this construction one also has to first create new vars for
;; the bound avars.  Similary to avars we have to treat assumption
;; constants which are not axioms, i.e., theorems or global assumptions.
;; (2) Normalize the resulting term.  (3) Reconstruct a normal proof from
;; this term, the end formula and the stored information.  - The critical
;; variables are carried along for efficiency reasons.

;; To assign recursion constants to induction constants, we need to
;; associate type variables with predicate variables, in such a way
;; that we can later refer to this assignment.  Therefore we use a
;; global variable PVAR-TO-TVAR-ALIST, which memorizes the assigment
;; done so far.  A fixed PVAR-TO-TVAR refers to and updates
;; PVAR-TO-TVAR-ALIST.

;; For term extraction, in particular in formula-to-et-type and
;; formula-to-etd-types, we will also need to assign type variables to
;; predicate variables, this time only for those with positive or
;; negative computational content.  There we will also refer to the
;; same PVAR-TO-TVAR and PVAR-TO-TVARP and PVAR-TO-TVARN.  Later
;; reference is necessary, because such tvars will appear in extracted
;; terms of theorems involving pvars, and in a given development there
;; may be many auxiliary lemmata containing the same pvar.  In a
;; finished development with no free pvars left PVAR-TO-TVAR
;; PVAR-TO-TVARP and PVAR-TO-TVARN are not relevant any more, because
;; all pvars (in aconsts or idpcs) are bound.  In an unfinished
;; development we want to assign the same tvar to all occurrences of a
;; pvar, and it does not matter which tvar it is.

;; Example Id: all alpha, beta all P^(alpha=>prop+beta).  P^ -> P^ has
;; [beta][y]y as extracted term.  The tvar beta disappears as soon as
;; Id is applied to some cterm without pvars.

;; Given a proof and suppose we want to extract its content.  Then we
;; can concentrate on its computationally relevant parts, and replace
;; the rest by newly introduced assumption variables.  This is useful
;; for efficiency reasons when normalizing, and also for studying the
;; need and the effect of pi-normalization, simplification and pruning.

;; Probably PVAR-TO-TVARP is not necessary.  PVAR-TO-TVAR should suffice.

;; PVAR-TO-TVAR-ALIST initially has
;; (Pvar alpha) -> gamma
;; Pvar2 -> beta2
;; Pvar1 -> beta1
;; Pvar  -> beta

(define PVAR-TO-TVAR-ALIST
  (list
   (list (make-pvar (make-arity (make-tvar -1 "alpha"))
		    -1 h-deg-zero n-deg-zero "")
	 (make-tvar -1 "gamma"))
   (list (make-pvar (make-arity) 2 h-deg-zero n-deg-zero "")
	 (make-tvar 2 "beta"))
   (list (make-pvar (make-arity) 1 h-deg-zero n-deg-zero "")
	 (make-tvar 1 "beta"))
   (list (make-pvar (make-arity) -1 h-deg-zero n-deg-zero "")
	 (make-tvar -1 "beta"))))	      

(define (PVAR-TO-TVAR pvar)
  (let ((info (assoc pvar PVAR-TO-TVAR-ALIST)))
    (if info
	(cadr info)
	(let ((newtvar (new-tvar)))
	  (set! PVAR-TO-TVAR-ALIST
		(cons (list pvar newtvar) PVAR-TO-TVAR-ALIST))
	  newtvar))))

(define PVAR-TO-TVARP-ALIST '())

(define (PVAR-TO-TVARP pvar)
  (let ((info (assoc pvar PVAR-TO-TVARP-ALIST)))
    (if info
	(cadr info)
	(let ((newtvarp (new-tvar)))
	  (set! PVAR-TO-TVARP-ALIST
		(cons (list pvar newtvarp) PVAR-TO-TVARP-ALIST))
	  newtvarp))))

(define PVAR-TO-TVARN-ALIST '())

(define (PVAR-TO-TVARN pvar)
  (let ((info (assoc pvar PVAR-TO-TVARN-ALIST)))
    (if info
	(cadr info)
	(let ((newtvarn (new-tvar)))
	  (set! PVAR-TO-TVARN-ALIST
		(cons (list pvar newtvarn) PVAR-TO-TVARN-ALIST))
	  newtvarn))))

(define (nbe-normalize-proof-without-eta proof)
  (nbe-normalize-proof-without-eta-aux proof #f #t))

(define (nbe-normalize-proof-without-eta-for-extraction proof)
  (nbe-normalize-proof-without-eta-aux
   proof #t (not (formula-of-nulltype? (proof-to-formula proof)))))

(define (nbe-normalize-proof-without-eta-aux
	 proof extraction-flag content-flag)
  (if
   (and extraction-flag (not content-flag))
   (let* ((proof-and-asubst (proof-to-c-r-proof-and-asubst proof))
	  (proof1 (car proof-and-asubst))
	  (asubst1 (cadr proof-and-asubst))
	  (nproof1 (nbe-normalize-proof-without-eta proof1)))
     (proof-substitute nproof1 asubst1))
   (let* ((formula (proof-to-formula proof))
	  (genavars (append (proof-to-free-and-bound-avars proof)
			    (proof-to-aconsts-without-rules proof)))
	  (vars (map (lambda (x)
		       (type-to-new-var
			(nbe-formula-to-type
			 (cond ((avar-form? x) (avar-to-formula x))
			       ((aconst-form? x) (aconst-to-formula x))
			       (else (myerror
				      "nbe-normalize-proof"
				      "genavar expected" x))))))
		     genavars))
	  (genavar-var-alist (map list genavars vars))
	  (var-genavar-alist (map list vars genavars))
	  (pterm (proof-and-genavar-var-alist-to-pterm
		  genavar-var-alist proof))
	  (npterm (nbe-normalize-term-without-eta pterm)))
     (npterm-and-var-genavar-alist-and-formula-to-proof
      npterm var-genavar-alist '() (unfold-formula formula)))))

(define (proof-to-c-r-proof-and-asubst proof)
  (if
   (formula-of-nulltype? (proof-to-formula proof))
   (let* ((context (proof-to-context proof))
	  (avar (formula-to-new-avar
		 (context-and-ncvars-and-formula-to-formula
		  context '() (proof-to-formula proof)))))
     (list
      (apply mk-proof-in-elim-form
	     (make-proof-in-avar-form avar)
	     (map (lambda (x) (if (var-form? x)
				  (make-term-in-var-form x)
				  (make-proof-in-avar-form x)))
		  context))
      (list (list avar
		  (apply mk-proof-in-intro-form
			 (append context (list proof)))))))
   (case (tag proof)
     ((proof-in-avar-form proof-in-aconst-form) (list proof '()))
     ((proof-in-imp-intro-form)
      (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	     (kernel (proof-in-imp-intro-form-to-kernel proof))
	     (prev (proof-to-c-r-proof-and-asubst kernel))
	     (prev-proof (car prev))
	     (prev-asubst (cadr prev)))
	(list (make-proof-in-imp-intro-form avar prev-proof)
	      prev-asubst)))
     ((proof-in-imp-elim-form)
      (let* ((op (proof-in-imp-elim-form-to-op proof))
	     (arg (proof-in-imp-elim-form-to-arg proof))
	     (prev1 (proof-to-c-r-proof-and-asubst op))
	     (prev-proof1 (car prev1))
	     (prev-asubst1 (cadr prev1))
	     (prev2 (proof-to-c-r-proof-and-asubst arg))
	     (prev-proof2 (car prev2))
	     (prev-asubst2 (cadr prev2)))
	(list (make-proof-in-imp-elim-form prev-proof1 prev-proof2)
	      (append prev-asubst1 prev-asubst2))))
     ((proof-in-and-intro-form)
      (let* ((left (proof-in-and-intro-form-to-left proof))
	     (right (proof-in-and-intro-form-to-right proof))
	     (prev1 (proof-to-c-r-proof-and-asubst left))
	     (prev-proof1 (car prev1))
	     (prev-asubst1 (cadr prev1))
	     (prev2 (proof-to-c-r-proof-and-asubst right))
	     (prev-proof2 (car prev2))
	     (prev-asubst2 (cadr prev2)))
	(list (make-proof-in-and-intro-form prev-proof1 prev-proof2)
	      (append prev-asubst1 prev-asubst2))))
     ((proof-in-and-elim-left-form)
      (let* ((kernel (proof-in-and-elim-left-form-to-kernel proof))
	     (prev (proof-to-c-r-proof-and-asubst kernel))
	     (prev-proof (car prev))
	     (prev-asubst (cadr prev)))
	(list (make-proof-in-and-elim-left-form prev-proof) prev-asubst)))
     ((proof-in-and-elim-right-form)
      (let* ((kernel (proof-in-and-elim-right-form-to-kernel proof))
	     (prev (proof-to-c-r-proof-and-asubst kernel))
	     (prev-proof (car prev))
	     (prev-asubst (cadr prev)))
	(list (make-proof-in-and-elim-right-form prev-proof) prev-asubst)))
     ((proof-in-all-intro-form)
      (let* ((var (proof-in-all-intro-form-to-var proof))
	     (kernel (proof-in-all-intro-form-to-kernel proof))
	     (prev (proof-to-c-r-proof-and-asubst kernel))
	     (prev-proof (car prev))
	     (prev-asubst (cadr prev)))
	(list (make-proof-in-all-intro-form var prev-proof)
	      prev-asubst)))
     ((proof-in-all-elim-form)
      (let* ((op (proof-in-all-elim-form-to-op proof))
	     (arg (proof-in-all-elim-form-to-arg proof))
	     (prev (proof-to-c-r-proof-and-asubst op))
	     (prev-proof (car prev))
	     (prev-asubst (cadr prev)))
	(list (make-proof-in-all-elim-form prev-proof arg) prev-asubst)))
     ((proof-in-allnc-intro-form)
      (let* ((var (proof-in-allnc-intro-form-to-var proof))
	     (kernel (proof-in-allnc-intro-form-to-kernel proof))
	     (prev (proof-to-c-r-proof-and-asubst kernel))
	     (prev-proof (car prev))
	     (prev-asubst (cadr prev)))
	(list (make-proof-in-allnc-intro-form var prev-proof)
	      prev-asubst)))
     ((proof-in-allnc-elim-form)
      (let* ((op (proof-in-allnc-elim-form-to-op proof))
	     (arg (proof-in-allnc-elim-form-to-arg proof))
	     (prev (proof-to-c-r-proof-and-asubst op))
	     (prev-proof (car prev))
	     (prev-asubst (cadr prev)))
	(list (make-proof-in-allnc-elim-form prev-proof arg) prev-asubst)))
     (else (myerror "proof-to-c-r-proof-and-asubst" "not implemented for"
		    (tag proof))))))

(define (genavar=? genavar1 genavar2)
  (or (and (avar-form? genavar1) (avar-form? genavar2)
	   (avar=? genavar1 genavar2))
      (and (aconst-form? genavar1) (aconst-form? genavar2)
	   (aconst=? genavar1 genavar2))))

(define (proof-and-genavar-var-alist-to-pterm genavar-var-alist proof)
  (case (tag proof)
    ((proof-in-avar-form)
     (let* ((avar (proof-in-avar-form-to-avar proof))
	    (info (assoc-wrt genavar=? avar genavar-var-alist))
	    (var (cadr info)))
       (make-term-in-var-form var)))
    ((proof-in-aconst-form)
     (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	    (name (aconst-to-name aconst))
	    (repro-data (aconst-to-repro-data aconst)))
       (if (aconst-without-rules? aconst)
	   (let ((info (assoc-wrt genavar=? aconst genavar-var-alist)))
	     (if info
		 (make-term-in-var-form (cadr info))
		 (myerror
		  "proof-and-genavar-var-alist-to-pterm" "genavar expected"
		  (aconst-to-string aconst))))
	   (make-term-in-const-form
	    (cond
	     ((string=? "Ind" name)
	      (apply all-formulas-to-rec-const repro-data))
	     ((string=? "Cases" name)
	      (all-formula-to-cases-const (car repro-data)))
             ((string=? "GInd" name)
              (let* ((uninst-formula (aconst-to-uninst-formula aconst))
                     (vars (all-form-to-vars uninst-formula))
                     (m (- (length vars) 1)))
                (all-formula-and-number-to-grecguard-const
		 (car repro-data) m)))
             ((string=? "Efq" name) ;This is a hack.  The formula should be (?)
					;in the repro-data but isn't because
					;Efq is a global-assumption.
              (let ((formula (imp-form-to-conclusion
                              (allnc-form-to-final-kernel
                               (aconst-to-formula aconst)))))
                (formula-to-efq-const formula)))
	     ((string=? "Intro" name)
	      (apply number-and-idpredconst-to-intro-const repro-data))
	     ((string=? "Elim" name)
	      (apply imp-formulas-to-rec-const repro-data))
	     ((string=? "Ex-Intro" name)
	      (ex-formula-to-ex-intro-const (car repro-data)))
	     ((string=? "Ex-Elim" name)
	      (apply ex-formula-and-concl-to-ex-elim-const repro-data))
	     (else
	      (myerror "proof-and-genavar-var-alist-to-pterm" "aconst expected"
		       name)))))))
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (info (assoc-wrt avar=? avar genavar-var-alist))
	    (var (cadr info)))
       (make-term-in-abst-form var (proof-and-genavar-var-alist-to-pterm
				    genavar-var-alist kernel))))
    ((proof-in-imp-elim-form)
     (let* ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof)))
       (make-term-in-app-form
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist op)
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist arg))))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (info (assoc-wrt avar=? avar genavar-var-alist))
	    (var (cadr info)))
       (make-term-in-abst-form var (proof-and-genavar-var-alist-to-pterm
				    genavar-var-alist kernel))))
    ((proof-in-impnc-elim-form)
     (let* ((op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof)))
       (make-term-in-app-form
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist op)
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist arg))))
    ((proof-in-and-intro-form)
     (let ((left (proof-in-and-intro-form-to-left proof))
	   (right (proof-in-and-intro-form-to-right proof)))
       (make-term-in-pair-form
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist left)
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist right))))
    ((proof-in-and-elim-left-form)
     (let* ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (make-term-in-lcomp-form
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist kernel))))
    ((proof-in-and-elim-right-form)
     (let* ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (make-term-in-rcomp-form
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist kernel))))
    ((proof-in-all-intro-form)
     (let* ((var (proof-in-all-intro-form-to-var proof))
	    (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-term-in-abst-form
	var (proof-and-genavar-var-alist-to-pterm genavar-var-alist kernel))))
    ((proof-in-all-elim-form)
     (let* ((op (proof-in-all-elim-form-to-op proof))
	    (arg (proof-in-all-elim-form-to-arg proof)))
       (make-term-in-app-form
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist op)
	arg)))
    ((proof-in-allnc-intro-form)
     (let* ((var (proof-in-allnc-intro-form-to-var proof))
	    (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-term-in-abst-form
	var (proof-and-genavar-var-alist-to-pterm genavar-var-alist kernel))))
    ((proof-in-allnc-elim-form)
     (let* ((op (proof-in-allnc-elim-form-to-op proof))
	    (arg (proof-in-allnc-elim-form-to-arg proof)))
       (make-term-in-app-form
	(proof-and-genavar-var-alist-to-pterm genavar-var-alist op)
	arg)))
    (else
     (myerror "proof-and-genavar-var-alist-to-pterm" "proof tag expected"
	      (tag proof)))))

(define (npterm-and-var-genavar-alist-and-formula-to-proof
	 npterm var-genavar-alist crit formula)
  (case (tag npterm)
    ((term-in-abst-form)
     (let* ((npterm-var (term-in-abst-form-to-var npterm))
	    (npterm-kernel (term-in-abst-form-to-kernel npterm)))
       (cond
	((imp-form? formula)
	 (let* ((premise (imp-form-to-premise formula))
		(avar (formula-to-new-avar premise))
		(conclusion (imp-form-to-conclusion formula)))
	   (make-proof-in-imp-intro-form
	    avar
	    (npterm-and-var-genavar-alist-and-formula-to-proof
	     npterm-kernel
	     (cons (list npterm-var avar) var-genavar-alist)
	     (union (formula-to-free premise) crit)
	     conclusion))))
	((impnc-form? formula)
	 (let* ((premise (impnc-form-to-premise formula))
		(avar (formula-to-new-avar premise))
		(conclusion (impnc-form-to-conclusion formula)))
	   (make-proof-in-impnc-intro-form
	    avar
	    (npterm-and-var-genavar-alist-and-formula-to-proof
	     npterm-kernel
	     (cons (list npterm-var avar) var-genavar-alist)
	     (union (formula-to-free premise) crit)
	     conclusion))))
	((all-form? formula)
	 (let* ((var (all-form-to-var formula))
		(kernel (all-form-to-kernel formula))
		(var-is-crit? (member var crit))
		(new-var (if var-is-crit? (var-to-new-var var) var))
		(new-kernel
		 (if var-is-crit?
		     (formula-subst kernel var (make-term-in-var-form new-var))
		     kernel))
		(new-npterm-kernel
		 (if (equal? npterm-var new-var)
		     npterm-kernel
		     (term-subst npterm-kernel
				 npterm-var
				 (make-term-in-var-form new-var)))))
	   (make-proof-in-all-intro-form
	    new-var
	    (npterm-and-var-genavar-alist-and-formula-to-proof
	     new-npterm-kernel var-genavar-alist crit new-kernel))))
	((allnc-form? formula)
	 (let* ((var (allnc-form-to-var formula))
		(kernel (allnc-form-to-kernel formula))
		(var-is-crit? (member var crit))
		(new-var (if var-is-crit? (var-to-new-var var) var))
		(new-kernel
		 (if var-is-crit?
		     (formula-subst kernel var (make-term-in-var-form new-var))
		     kernel))
		(new-npterm-kernel
		 (if (equal? npterm-var new-var)
		     npterm-kernel
		     (term-subst npterm-kernel
				 npterm-var
				 (make-term-in-var-form new-var)))))
	   (make-proof-in-allnc-intro-form
	    new-var
	    (npterm-and-var-genavar-alist-and-formula-to-proof
	     new-npterm-kernel var-genavar-alist crit new-kernel))))
	(else
	 (myerror
	  "npterm-and-var-genavar-alist-and-formula-to-proof"
	  "imp- or all-formula expected"
	  formula)))))
    ((term-in-pair-form)
     (let ((npterm-left (term-in-pair-form-to-left npterm))
	   (npterm-right (term-in-pair-form-to-right npterm)))
       (cond ((and-form? formula)
	      (let ((left-formula (and-form-to-left formula))
		    (right-formula (and-form-to-right formula)))
		(make-proof-in-and-intro-form
		 (npterm-and-var-genavar-alist-and-formula-to-proof
		  npterm-left var-genavar-alist crit left-formula)
		 (npterm-and-var-genavar-alist-and-formula-to-proof
		  npterm-right var-genavar-alist crit right-formula))))
	     (else (myerror
		    "npterm-and-var-genavar-alist-and-formula-to-proof"
		    "and-formula expected"
		    formula)))))
    (else
     (let ((prev (elim-npterm-and-var-genavar-alist-to-proof
		  npterm var-genavar-alist crit)))
       (if (classical-formula=? formula (proof-to-formula prev))
	   prev
	   (myerror "npterm-and-var-genavar-alist-and-formula-to-proof"
                    "classical equal formulas expected"
		    formula
		    (proof-to-formula prev)))))))

(define (elim-npterm-and-var-genavar-alist-to-proof
	 npterm var-genavar-alist crit)
  (case (tag npterm)
    ((term-in-var-form)
     (let* ((var (term-in-var-form-to-var npterm))
	    (info (assoc var var-genavar-alist)))
       (if info
	   (let ((genavar (cadr info)))
	     (cond
	      ((avar-form? genavar) (make-proof-in-avar-form genavar))
	      ((aconst-form? genavar) (make-proof-in-aconst-form genavar))
	      (else (myerror "elim-npterm-and-var-genavar-alist-to-proof"
			     "unexpected genavar" genavar))))
	   (myerror
	    "elim-npterm-and-var-genavar-alist-to-proof" "unexpected term"
	    npterm))))
    ((term-in-const-form)
     (let* ((const (term-in-const-form-to-const npterm))
	    (name (const-to-name const))
	    (repro-data (const-to-repro-data const)))
       (make-proof-in-aconst-form
	(cond
	 ((string=? "Rec" name) ;first repro fla depends on type of rec const
	  (if
	   (all-form? (car repro-data))
	   (let* ((uninst-recop-type (const-to-uninst-type const))
                  (f (length (formula-to-free (car repro-data))))
		  (arg-types (arrow-form-to-arg-types uninst-recop-type))
		  (alg-type (list-ref arg-types f))
		  (alg-name (alg-form-to-name alg-type))
		  (transformed-repro-formulas
		   (list-transform-positive repro-data
		     (lambda (x)
		       (let* ((type (var-to-type (all-form-to-var x))))
			 (and (alg-form? type)
			      (equal? (alg-form-to-name type) alg-name))))))
		  (repro-formula
		   (if (= 1 (length transformed-repro-formulas))
		       (car transformed-repro-formulas)
		       (myerror
			"elim-npterm-and-var-genavar-alist-to-proof"
			"unexpected repro formulas" repro-data)))
		  (permuted-repro-formulas
		   (cons repro-formula
			 (remove-wrt classical-formula=?
				     repro-formula repro-data))))
	     (apply all-formulas-to-ind-aconst permuted-repro-formulas))
	   (let* ((uninst-recop-type (const-to-uninst-type const))
                  (f (length (formula-to-free (car repro-data))))
		  (arg-types (arrow-form-to-arg-types uninst-recop-type))
                  (alg-type (list-ref arg-types f))
		  (alg-name (alg-form-to-name alg-type))
		  (transformed-repro-formulas
		   (list-transform-positive repro-data
		     (lambda (x)
		       (let* ((prem (imp-form-to-premise x))
			      (pred (predicate-form-to-predicate prem))
			      (name (idpredconst-to-name pred))
			      (nbe-alg-name (idpredconst-name-to-nbe-alg-name
					     name)))
			 (equal? nbe-alg-name alg-name)))))
		  (repro-formula
		   (if (= 1 (length transformed-repro-formulas))
		       (car transformed-repro-formulas)
		       (myerror
			"elim-npterm-and-var-genavar-alist-to-proof"
			"unexpected repro formulas" repro-data)))
		  (permuted-repro-formulas
		   (cons repro-formula
			 (remove-wrt classical-formula=?
				     repro-formula repro-data))))
	     (apply imp-formulas-to-elim-aconst permuted-repro-formulas))))
	 ((string=? "Cases" name)
	  (all-formula-to-cases-aconst (car repro-data)))
         ((string=? "GRec" name) ;should not happen since "GRec" is not normal
          (myerror "elim-npterm-and-var-genavar-alist-to-proof"
		   "unexpected term"
                   name))
         ((string=? "GRecGuard" name)
          (let* ((free (formula-to-free (car repro-data)))
                 (f (length free))
                 (type (term-to-type npterm))
                 (auxtype (arrow-form-to-final-val-type type f))
                 (argtypes (arrow-form-to-arg-types
                            (arrow-form-to-arg-type auxtype)))
                 (m (length argtypes)))
            (all-formula-and-number-to-gind-aconst (car repro-data) m)))
         ((string=? "Efq" name)
          (formula-to-efq-aconst (car repro-data)))
	 ((string=? "Intro" name)
	  (apply number-and-idpredconst-to-intro-aconst repro-data))
	 ((string=? "Ex-Intro" name)
	  (ex-formula-to-ex-intro-aconst (car repro-data)))
	 ((string=? "Ex-Elim" name)
	  (apply ex-formula-and-concl-to-ex-elim-aconst repro-data))
	 (else (myerror
		"elim-npterm-and-var-genavar-alist-to-proof" "unexpected term"
		name))))))
    ((term-in-app-form)
     (let* ((op (term-in-app-form-to-op npterm))
	    (arg (term-in-app-form-to-arg npterm))
	    (prev1 (elim-npterm-and-var-genavar-alist-to-proof
		    op var-genavar-alist crit))
	    (formula ;unfolding might still be necessary for aconsts 02-07-10
	     (unfold-formula (proof-to-formula prev1))))
       (cond
	((imp-form? formula)
	 (make-proof-in-imp-elim-form
	  prev1
	  (npterm-and-var-genavar-alist-and-formula-to-proof
	   arg var-genavar-alist crit (imp-form-to-premise formula))))
	((impnc-form? formula)
	 (make-proof-in-impnc-elim-form
	  prev1
	  (npterm-and-var-genavar-alist-and-formula-to-proof
	   arg var-genavar-alist crit (impnc-form-to-premise formula))))
	((all-form? formula) (make-proof-in-all-elim-form prev1 arg))
	((allnc-form? formula) (make-proof-in-allnc-elim-form prev1 arg))
	(else (myerror "elim-npterm-and-var-genavar-alist-to-proof"
		       "imp- or all-formula expected"
		       formula)))))
    ((term-in-lcomp-form)
     (let* ((kernel (term-in-lcomp-form-to-kernel npterm))
	    (prev (elim-npterm-and-var-genavar-alist-to-proof
		   kernel var-genavar-alist crit))
	    (formula (proof-to-formula prev)))
       (cond
	((and-form? formula)
	 (make-proof-in-and-elim-left-form prev))
	(else (myerror "elim-npterm-and-var-genavar-alist-to-proof"
		       "and-formula expected"
		       formula)))))
    ((term-in-rcomp-form)
     (let* ((kernel (term-in-rcomp-form-to-kernel npterm))
	    (prev (elim-npterm-and-var-genavar-alist-to-proof
		   kernel var-genavar-alist crit))
	    (formula (proof-to-formula prev)))
       (cond
	((and-form? formula)
	 (make-proof-in-and-elim-right-form prev))
	(else (myerror "elim-npterm-and-var-genavar-alist-to-proof"
		       "and-formula expected"
		       formula)))))
    (else
     (myerror "elim-npterm-and-var-genavar-alist-to-proof" "unexpected term"
	      npterm))))

(define (proof-to-eta-nf proof)
  (proof-to-eta-nf-aux proof #f #t))

(define (proof-to-eta-nf-for-extraction proof)
  (proof-to-eta-nf-aux
   proof #t (not (formula-of-nulltype? (proof-to-formula proof)))))

(define (proof-to-eta-nf-aux proof extraction-flag content-flag)
  (if
   (and extraction-flag (not content-flag))
   proof
   (case (tag proof)
     ((proof-in-imp-intro-form) ;[u]Mu -> M, if u is not free in M
      (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	     (kernel (proof-in-imp-intro-form-to-kernel proof))
	     (prev (proof-to-eta-nf-aux kernel extraction-flag content-flag)))
	(if (and (proof-in-imp-elim-form? prev)
		 (proof=? (proof-in-imp-elim-form-to-arg prev)
			  (make-proof-in-avar-form avar))
		 (not (member-wrt
		       avar=? avar (proof-to-context
				    (proof-in-imp-elim-form-to-op prev)))))
	    (proof-in-imp-elim-form-to-op prev)
	    (make-proof-in-imp-intro-form avar prev))))
     ((proof-in-imp-elim-form)
      (let ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof)))
	(make-proof-in-imp-elim-form
	 (proof-to-eta-nf-aux op extraction-flag content-flag)
	 (proof-to-eta-nf-aux
	  arg extraction-flag
	  (not (formula-of-nulltype? (proof-to-formula arg)))))))
     ((proof-in-impnc-intro-form) ;[u]Mu -> M, if u is not free in M
      (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	     (kernel (proof-in-impnc-intro-form-to-kernel proof))
	     (prev (proof-to-eta-nf-aux kernel extraction-flag content-flag)))
	(if (and (proof-in-impnc-elim-form? prev)
		 (proof=? (proof-in-impnc-elim-form-to-arg prev)
			  (make-proof-in-avar-form avar))
		 (not (member-wrt
		       avar=? avar (proof-to-context
				    (proof-in-impnc-elim-form-to-op prev)))))
	    (proof-in-impnc-elim-form-to-op prev)
	    (make-proof-in-impnc-intro-form avar prev))))
     ((proof-in-impnc-elim-form)
      (let ((op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof)))
	(make-proof-in-impnc-elim-form
	 (proof-to-eta-nf-aux op extraction-flag content-flag)
	 (proof-to-eta-nf-aux arg extraction-flag #f))))
     ((proof-in-and-intro-form) ;(and-intro p_1M p_2M) -> M
      (let* ((left (proof-in-and-intro-form-to-left proof))
	     (right (proof-in-and-intro-form-to-right proof))
	     (prev-left
	      (proof-to-eta-nf-aux
	       left extraction-flag
	       (not (formula-of-nulltype? (proof-to-formula left)))))
	     (prev-right
	      (proof-to-eta-nf-aux
	       right extraction-flag
	       (not (formula-of-nulltype? (proof-to-formula right))))))
	(if (and (proof-in-and-elim-left-form? prev-left)
		 (proof-in-and-elim-right-form? prev-right)
		 (proof=?
		  (proof-in-and-elim-left-form-to-kernel prev-left)
		  (proof-in-and-elim-right-form-to-kernel prev-right)))
	    (proof-in-and-elim-left-form-to-kernel prev-left)
	    (make-proof-in-and-intro-form prev-left prev-right))))
     ((proof-in-and-elim-left-form)
      (let* ((kernel (proof-in-and-elim-left-form-to-kernel proof))
	     (prev (proof-to-eta-nf-aux kernel extraction-flag content-flag)))
	(if (proof-in-and-intro-form? prev)
	    (proof-in-and-intro-form-to-left prev)
	    (make-proof-in-and-elim-left-form prev))))
     ((proof-in-and-elim-right-form)
      (let* ((kernel (proof-in-and-elim-right-form-to-kernel proof))
	     (prev (proof-to-eta-nf-aux kernel extraction-flag content-flag)))
	(if (proof-in-and-intro-form? prev)
	    (proof-in-and-intro-form-to-right prev)
	    (make-proof-in-and-elim-right-form prev))))
     ((proof-in-all-intro-form) ;[x]Mx -> M, if x is not free in M
      (let* ((var (proof-in-all-intro-form-to-var proof))
	     (kernel (proof-in-all-intro-form-to-kernel proof))
	     (prev (proof-to-eta-nf-aux kernel extraction-flag content-flag)))
	(if (and (proof-in-all-elim-form? prev)
		 (term=? (proof-in-all-elim-form-to-arg prev)
			 (make-term-in-var-form var))
		 (not (member var (proof-to-context
				   (proof-in-all-elim-form-to-op prev)))))
	    (proof-in-all-elim-form-to-op prev)
	    (make-proof-in-all-intro-form var prev))))
     ((proof-in-all-elim-form)
      (let ((op (proof-in-all-elim-form-to-op proof))
	    (arg (proof-in-all-elim-form-to-arg proof)))
	(make-proof-in-all-elim-form
	 (proof-to-eta-nf-aux op extraction-flag content-flag)
	 (term-to-eta-nf arg))))
     ((proof-in-allnc-intro-form) ;[x]Mx -> M, if x is not free in M
      (let* ((var (proof-in-allnc-intro-form-to-var proof))
	     (kernel (proof-in-allnc-intro-form-to-kernel proof))
	     (prev (proof-to-eta-nf-aux kernel extraction-flag content-flag)))
	(if (and (proof-in-allnc-elim-form? prev)
		 (term=? (proof-in-allnc-elim-form-to-arg prev)
			 (make-term-in-var-form var))
		 (not (member var (proof-to-context
				   (proof-in-allnc-elim-form-to-op prev)))))
	    (proof-in-allnc-elim-form-to-op prev)
	    (make-proof-in-allnc-intro-form var prev))))
     ((proof-in-allnc-elim-form)
      (let ((op (proof-in-allnc-elim-form-to-op proof))
	    (arg (proof-in-allnc-elim-form-to-arg proof)))
	(make-proof-in-allnc-elim-form
	 (proof-to-eta-nf-aux op extraction-flag content-flag)
	 (term-to-eta-nf arg))))
     (else proof))))

;; For a full normalization of proofs, including permutative
;; conversions, we define a preprocessing step that eta expands
;; permutative aconsts such that the conclusion is atomic or
;; existential.

(define (proof-to-proof-with-eta-expanded-permutative-aconsts proof)
  (proof-to-proof-with-eta-expanded-permutative-aconsts-aux proof #f #t))

(define (proof-to-proof-with-eta-expanded-permutative-aconsts-for-extraction
	 proof)
  (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
   proof #t (not (formula-of-nulltype? (proof-to-formula proof)))))

(define (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	 proof extraction-flag content-flag)
  (if
   (and extraction-flag (not content-flag))
   proof
   (case (tag proof)
     ((proof-in-aconst-form)
      (if (permutative-aconst? (proof-in-aconst-form-to-aconst proof))
	  (permutative-aconst-proof-to-eta-expansion proof)
	  proof))
     ((proof-in-imp-intro-form)
      (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	     (kernel (proof-in-imp-intro-form-to-kernel proof)))
	(make-proof-in-imp-intro-form
	 avar (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	       kernel extraction-flag content-flag))))
     ((proof-in-imp-elim-form)
      (let ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof)))
	(make-proof-in-imp-elim-form
	 (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	  op extraction-flag content-flag)
	 (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	  arg extraction-flag
	  (not (formula-of-nulltype? (proof-to-formula arg)))))))
     ((proof-in-impnc-intro-form)
      (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	     (kernel (proof-in-impnc-intro-form-to-kernel proof)))
	(make-proof-in-impnc-intro-form
	 avar (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	       kernel extraction-flag content-flag))))
     ((proof-in-impnc-elim-form)
      (let ((op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof)))
	(make-proof-in-impnc-elim-form
	 (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	  op extraction-flag content-flag)
	 (if (not extraction-flag)
	     (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	      arg #f #t) ;content flag irrelevant here
	     arg))))
     ((proof-in-and-intro-form)
      (let* ((left (proof-in-and-intro-form-to-left proof))
	     (right (proof-in-and-intro-form-to-right proof)))
	(make-proof-in-and-intro-form
	 (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	  left extraction-flag
	  (not (formula-of-nulltype? (proof-to-formula left))))
	 (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	  right extraction-flag
	  (not (formula-of-nulltype? (proof-to-formula right)))))))
     ((proof-in-and-elim-left-form)
      (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
      (make-proof-in-and-elim-left-form
       (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	kernel extraction-flag content-flag))))
     ((proof-in-and-elim-right-form)
      (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
      (make-proof-in-and-elim-right-form
       (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	kernel extraction-flag content-flag))))
     ((proof-in-all-intro-form)
      (let* ((var (proof-in-all-intro-form-to-var proof))
	     (kernel (proof-in-all-intro-form-to-kernel proof)))
	(make-proof-in-all-intro-form
	 var (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	      kernel extraction-flag content-flag))))
     ((proof-in-all-elim-form)
      (let ((op (proof-in-all-elim-form-to-op proof))
	    (arg (proof-in-all-elim-form-to-arg proof)))
	(make-proof-in-all-elim-form
	 (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	  op extraction-flag content-flag) arg)))
     ((proof-in-allnc-intro-form)
      (let* ((var (proof-in-allnc-intro-form-to-var proof))
	     (kernel (proof-in-allnc-intro-form-to-kernel proof)))
	(make-proof-in-allnc-intro-form
	 var (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	      kernel extraction-flag content-flag))))
     ((proof-in-allnc-elim-form)
      (let ((op (proof-in-allnc-elim-form-to-op proof))
	    (arg (proof-in-allnc-elim-form-to-arg proof)))
	(make-proof-in-allnc-elim-form
	 (proof-to-proof-with-eta-expanded-permutative-aconsts-aux
	  op extraction-flag content-flag) arg)))
     (else proof))))

(define (permutative-aconst-proof-to-eta-expansion proof)
  (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (final-concl (imp-impnc-all-allnc-form-to-final-conclusion
		       uninst-formula))
	 (var-or-prem-list
	  (imp-impnc-all-allnc-form-to-vars-and-premises uninst-formula))
	 (pvar (predicate-form-to-predicate final-concl))
	 (tpsubst (aconst-to-tpsubst aconst))
	 (info (assoc pvar tpsubst))
	 (tpsubst-without-pvar
	  (if info
	      (list-transform-positive tpsubst
		(lambda (x) (not (equal? (car x) pvar))))
	      tpsubst))
	 (orig-formula (if info (cterm-to-formula (cadr info)) final-concl))
	 (formula
	  (if (quant-form? orig-formula)
	      (let* ((quant (quant-form-to-quant orig-formula))
		     (vars (quant-form-to-vars orig-formula))
		     (kernel (quant-form-to-kernel orig-formula))
		     (bound-vars (formula-to-bound uninst-formula)))
		(if (pair? (intersection vars bound-vars))
		    (let* ((new-vars (map var-to-new-var vars)))
		      (make-quant
		       quant new-vars
		       (formula-substitute
			kernel
			(map (lambda (var new-var)
			       (list var (make-term-in-var-form new-var)))
			     vars new-vars))))
		    orig-formula))
	      orig-formula)))
    (case (tag formula)
      ((imp)
       (permutative-aconst-proof-to-eta-expansion-aux
	proof var-or-prem-list pvar tpsubst-without-pvar formula
	make-proof-in-imp-intro-form
	(formula-to-new-avar (imp-form-to-premise formula))))
      ((impnc)
       (permutative-aconst-proof-to-eta-expansion-aux
	proof var-or-prem-list pvar tpsubst-without-pvar formula
	make-proof-in-impnc-intro-form
	(formula-to-new-avar (impnc-form-to-premise formula))))
      ((and)
       (permutative-aconst-proof-to-eta-expansion-aux
	proof var-or-prem-list pvar tpsubst-without-pvar formula
	make-proof-in-and-intro-form))
      ((all)
       (permutative-aconst-proof-to-eta-expansion-aux
	proof var-or-prem-list pvar tpsubst-without-pvar formula
	make-proof-in-all-intro-form))
      ((allnc)
       (permutative-aconst-proof-to-eta-expansion-aux
	proof var-or-prem-list pvar tpsubst-without-pvar formula
	make-proof-in-allnc-intro-form))
      (else proof))))

;; permutative-aconst-proof-to-eta-expansion-aux is a generic helper
;; function, which does eta-expansion in a perm-aconst with a composite
;; formula (imp, impnc, and, all or allnc), where the introduction
;; proof constructor is make-intro.  It returns the final proof.

(define (permutative-aconst-proof-to-eta-expansion-aux
	 proof var-or-prem-list pvar tpsubst-without-pvar formula
	 make-intro . possible-avar)
  (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	 (name (aconst-to-name aconst))
	 (kind (aconst-to-kind aconst))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (inst-formula (aconst-to-inst-formula aconst))
	 (free (formula-to-free inst-formula))
	 (var-or-inst-prem-list
	  (imp-impnc-all-allnc-form-to-vars-and-premises
	   inst-formula (length var-or-prem-list)))
	 (var-and-args-list ;((var1 arg11 arg12 ..) (var2 args21 arg22 ..) ..)
	  (do ((l1 var-or-prem-list (cdr l1))
	       (l2 var-or-inst-prem-list (cdr l2))
	       (res
		'()
		(let ((var-or-prem (car l1))
		      (var-or-inst-prem (car l2)))
		  (cond
		   ((var-form? var-or-prem)
		    (cons (list var-or-prem
				(make-term-in-var-form var-or-prem))
			  res))
		   ((not (member pvar (formula-to-pvars var-or-prem)))
		    (let ((avar (formula-to-new-avar var-or-inst-prem)))
		      (cons (list avar (make-proof-in-avar-form avar))
			    res)))
		   (else
		    (let*
			((l (length
			     (imp-impnc-all-allnc-form-to-vars-and-premises
			      var-or-prem)))
			 (new-avar (formula-to-new-avar var-or-inst-prem))
			 (inner-var-or-prem-list
			  (imp-impnc-all-allnc-form-to-vars-and-premises
			   var-or-inst-prem l))
			 (inner-vars-and-avars
			  (map (lambda (x)
				 (if (var-form? x) x
				     (formula-to-new-avar x)))
			       inner-var-or-prem-list))
			 (inner-elim-proof ;of inst pvar
			  (apply
			   mk-proof-in-elim-form
			   (make-proof-in-avar-form new-avar)
			   (map (lambda (x)
				  (if (var-form? x)
				      (make-term-in-var-form x)
				      (make-proof-in-avar-form x)))
				inner-vars-and-avars)))
			 (abst-applied-inner-elim-proofs
			  (case (tag formula)
			    ((imp)
			     (let* ((prem (imp-form-to-premise formula))
				    (prem-avar (car possible-avar))
				    (applied-inner-elim-proof
				     (make-proof-in-imp-elim-form
				      inner-elim-proof
				      (make-proof-in-avar-form prem-avar))))
			       (list
				(apply mk-proof-in-intro-form
				       (append
					inner-vars-and-avars
					(list applied-inner-elim-proof))))))
			    ((impnc)
			     (let* ((prem (impnc-form-to-premise formula))
				    (prem-avar (car possible-avar))
				    (applied-inner-elim-proof
				     (make-proof-in-impnc-elim-form
				      inner-elim-proof
				      (make-proof-in-avar-form prem-avar))))
			       (list
				(apply mk-proof-in-intro-form
				       (append
					inner-vars-and-avars
					(list applied-inner-elim-proof))))))
			    ((and)
			     (let* ((left (and-form-to-left formula))
				    (right (and-form-to-right formula))
				    (applied-inner-elim-proofs
				     (list (make-proof-in-and-elim-left-form
					    inner-elim-proof)
					   (make-proof-in-and-elim-right-form
					    inner-elim-proof))))
			       (map (lambda (p)
				      (apply mk-proof-in-intro-form
					     (append inner-vars-and-avars
						     (list p))))
				    applied-inner-elim-proofs)))
			    ((all)
			     (let* ((var (all-form-to-var formula))
				    (applied-inner-elim-proof
				     (make-proof-in-all-elim-form
				      inner-elim-proof
				      (make-term-in-var-form var))))
			       (list
				(apply mk-proof-in-intro-form
				       (append
					inner-vars-and-avars
					(list applied-inner-elim-proof))))))
			    ((allnc)
			     (let* ((var (allnc-form-to-var formula))
				    (applied-inner-elim-proof
				     (make-proof-in-allnc-elim-form
				      inner-elim-proof
				      (make-term-in-var-form var))))
			       (list
				(apply mk-proof-in-intro-form
				       (append
					inner-vars-and-avars
					(list applied-inner-elim-proof))))))
			    (else (myerror "not implemented")))))
		      (cons (cons new-avar abst-applied-inner-elim-proofs)
			    res)))))))
	      ((null? l1) (reverse res))))
	 (vars (map car var-and-args-list))
	 (args-list (map cdr var-and-args-list))
	 (args-left (map car args-list))
	 (args-right (map (lambda (args)
			    (if (= 1 (length args)) (car args) (cadr args)))
			  args-list))
	 (intro-items
	  (case (tag formula)
	    ((imp)
	     (let* ((prem (imp-form-to-premise formula))
		    (concl (imp-form-to-conclusion formula))
		    (prem-avar (car possible-avar))
		    (cterm (make-cterm concl))
		    (new-tpsubst (if (pvar-cterm-equal? pvar cterm)
				     tpsubst-without-pvar
				     (append tpsubst-without-pvar
					     (list (list pvar cterm)))))
		    (new-aconst
		     (let ((aconst-without-repro-formulas
			    (make-aconst
			     name kind uninst-formula new-tpsubst)))
		       (apply make-aconst
			      name kind uninst-formula new-tpsubst
			      (aconst-to-computed-repro-data
			       aconst-without-repro-formulas))))
		    (new-inst-formula (aconst-to-inst-formula new-aconst))
		    (new-free (formula-to-free new-inst-formula)))
	       (list prem-avar
		     (apply mk-proof-in-elim-form
			    (permutative-aconst-proof-to-eta-expansion
			     (make-proof-in-aconst-form new-aconst))
			    (append (map make-term-in-var-form new-free)
				    args-left)))))
	    ((impnc)
	     (let* ((prem (impnc-form-to-premise formula))
		    (concl (impnc-form-to-conclusion formula))
		    (prem-avar (car possible-avar))
		    (cterm (make-cterm concl))
		    (new-tpsubst (if (pvar-cterm-equal? pvar cterm)
				     tpsubst-without-pvar
				     (append tpsubst-without-pvar
					     (list (list pvar cterm)))))
		    (new-aconst
		     (let ((aconst-without-repro-formulas
			    (make-aconst
			     name kind uninst-formula new-tpsubst)))
		       (apply
			make-aconst
			name kind uninst-formula new-tpsubst
			(aconst-to-computed-repro-data
			 aconst-without-repro-formulas))))
		    (new-inst-formula (aconst-to-inst-formula new-aconst))
		    (new-free (formula-to-free new-inst-formula)))
	       (list prem-avar
		     (apply mk-proof-in-elim-form
			    (permutative-aconst-proof-to-eta-expansion
			     (make-proof-in-aconst-form new-aconst))
			    (append (map make-term-in-var-form new-free)
				    args-left)))))
	    ((and)
	     (let* ((left (and-form-to-left formula))
		    (right (and-form-to-right formula))
		    (cterm-left (make-cterm left))
		    (cterm-right (make-cterm right))
		    (new-tpsubst-left
		     (if (pvar-cterm-equal? pvar cterm-left)
			 tpsubst-without-pvar
			 (append tpsubst-without-pvar
				 (list (list pvar cterm-left)))))
		    (new-tpsubst-right
		     (if (pvar-cterm-equal? pvar cterm-right)
			 tpsubst-without-pvar
			 (append tpsubst-without-pvar
				 (list (list pvar cterm-right)))))
		    (new-aconst-left
		     (let ((aconst-without-repro-formulas
			    (make-aconst
			     name kind uninst-formula new-tpsubst-left)))
		       (apply make-aconst
			      name kind uninst-formula new-tpsubst-left
			      (aconst-to-computed-repro-data
			       aconst-without-repro-formulas))))
		    (new-aconst-right
		     (let ((aconst-without-repro-formulas
			    (make-aconst
			     name kind uninst-formula new-tpsubst-right)))
		       (apply make-aconst
			      name kind uninst-formula new-tpsubst-right
			      (aconst-to-computed-repro-data
			       aconst-without-repro-formulas))))
		    (new-inst-formula-left
		     (aconst-to-inst-formula new-aconst-left))
		    (new-free-left (formula-to-free new-inst-formula-left))
		    (new-inst-formula-right
		     (aconst-to-inst-formula new-aconst-right))
		    (new-free-right (formula-to-free new-inst-formula-right)))
	       (list (apply
		      mk-proof-in-elim-form
		      (permutative-aconst-proof-to-eta-expansion
		       (make-proof-in-aconst-form new-aconst-left))
		      (append (map make-term-in-var-form new-free-left)
			      args-left))
		     (apply
		      mk-proof-in-elim-form
		      (permutative-aconst-proof-to-eta-expansion
		       (make-proof-in-aconst-form new-aconst-right))
		      (append (map make-term-in-var-form new-free-right)
			      args-right)))))
	    ((all)
	     (let* ((var (all-form-to-var formula))
		    (kernel (all-form-to-kernel formula))
		    (cterm (make-cterm kernel))
		    (new-tpsubst (if (pvar-cterm-equal? pvar cterm)
				     tpsubst-without-pvar
				     (append tpsubst-without-pvar
					     (list (list pvar cterm)))))
		    (new-aconst
		     (let ((aconst-without-repro-formulas
			    (make-aconst
			     name kind uninst-formula new-tpsubst)))
		       (apply
			make-aconst
			name kind uninst-formula new-tpsubst
			(aconst-to-computed-repro-data
			 aconst-without-repro-formulas))))
		    (new-inst-formula (aconst-to-inst-formula new-aconst))
		    (new-free (formula-to-free new-inst-formula)))
	       (list var
		     (apply mk-proof-in-elim-form
			    (permutative-aconst-proof-to-eta-expansion
			     (make-proof-in-aconst-form new-aconst))
			    (append (map make-term-in-var-form new-free)
				    args-left)))))
	    ((allnc)
	     (let* ((var (allnc-form-to-var formula))
		    (kernel (allnc-form-to-kernel formula))
		    (cterm (make-cterm kernel))
		    (new-tpsubst (if (pvar-cterm-equal? pvar cterm)
				     tpsubst-without-pvar
				     (append tpsubst-without-pvar
					     (list (list pvar cterm)))))
		    (new-aconst
		     (let ((aconst-without-repro-formulas
			    (make-aconst
			     name kind uninst-formula new-tpsubst)))
		       (apply make-aconst
			      name kind uninst-formula new-tpsubst
			      (aconst-to-computed-repro-data
			       aconst-without-repro-formulas))))
		    (new-inst-formula (aconst-to-inst-formula new-aconst))
		    (new-free (formula-to-free new-inst-formula)))
	       (list var
		     (apply mk-proof-in-elim-form
			    (permutative-aconst-proof-to-eta-expansion
			     (make-proof-in-aconst-form new-aconst))
			    (append (map make-term-in-var-form new-free)
				    args-left))))))))
    (apply mk-proof-in-intro-form
	   (append free vars (list (apply make-intro intro-items))))))

;; A permutative redex occurs if the conclusion of a permutative
;; assumption constant (example: "Ex-Elim"), applied to parameters and
;; all side premises, is the main premise of an elimination.  We assume
;; that this conclusion is a prime or existential formula, since this
;; will be the case when normalize-proof-pi is used in normalize-proof.
;; Hence the final elimination must be an elimination axiom for an
;; inductively defined predicate or else "Ex-Elim".

(define (permutative-aconst? aconst)
  (let ((name (aconst-to-name aconst)))
    (or
     (string=? "Ex-Elim" name)
     (string=? "If" name)
     (let* ((uninst-formula (aconst-to-uninst-formula aconst))
	    (final-concl (imp-impnc-all-allnc-form-to-final-conclusion
			  uninst-formula)))
       (and
	(predicate-form? final-concl)
	(pvar-form? (predicate-form-to-predicate final-concl))
	(let ((pvar (predicate-form-to-predicate final-concl)))
	  (and
	   (or
	    (null? (arity-to-types (predicate-to-arity pvar)))
	    (let* ((tpsubst (aconst-to-tpsubst aconst))
		   (info (assoc pvar tpsubst)))
	      (and info
		   (let* ((cterm (cadr info))
			  (vars (cterm-to-vars cterm))
			  (formula (cterm-to-formula cterm)))
		     (null? (intersection vars (formula-to-free formula)))))))
	   (let* ((prems (imp-impnc-all-allnc-form-to-premises uninst-formula))
		  (prems-with-pvar
		   (list-transform-positive prems
		     (lambda (x) (member pvar (formula-to-pvars x))))))
	     (apply
	      and-op
	      (append
	       (list (pair? prems-with-pvar))
	       (map (lambda (prem)
		      (let ((prem-final-concl
			     (imp-impnc-all-allnc-form-to-final-conclusion
			      prem)))
			(and
			 (predicate-form? prem-final-concl)
			 (equal? pvar (predicate-form-to-predicate
				       prem-final-concl))
			 (let ((prem-prems
				(imp-impnc-all-allnc-form-to-premises prem)))
			   (apply and-op
				  (map (lambda (prem-prem)
					 (not (member pvar (formula-to-pvars
							    prem-prem))))
				       prem-prems))))))
		    prems)))))))))))

(define (permutative-redex? proof)
  (and (proof-in-ex-elim-rule-form? proof)
       (let* ((main-premise (car (proof-to-imp-elim-args proof)))
	      (op (proof-in-elim-form-to-final-op main-premise)))
	 (and (proof-in-aconst-form? op)
	      (permutative-aconst? (proof-in-aconst-form-to-aconst op))))))

;; Now we define permutative conversions

;; We assume that proof is in long normal form, and every variable
;; bound in proof by all-intro or imp-intro is not free elsewhere (to
;; avoid renaming after permutation).  This is the case for proofs
;; obtained by nbe-normalize-proof-without-eta.

;; For permutative conversion we use an auxiliary function
;; (normalize-proof-pi-aux proof extraction-flag content-flag).  The
;; extraction-flag indicates whether we are interested in extraction
;; only.  If so, we can disregard (maximal) parts of the proof without
;; computational content.  The content-flag indicates whether the
;; formula of the proof has computational content.  This is for
;; efficiency only, since it avoids recomputation.  When
;; extraction-flag is #f content-flag is irrelevant.

(define (normalize-proof-pi proof)
  (normalize-proof-pi-aux proof #f #t))

(define (normalize-proof-pi-for-extraction proof)
  (normalize-proof-pi-aux
   proof #t (not (formula-of-nulltype? (proof-to-formula proof)))))

(define (normalize-proof-pi-aux proof extraction-flag content-flag)
  (if
   (and extraction-flag (not content-flag))
   proof
   (if
    (permutative-redex? proof)
    (let* ((imp-elim-args (proof-to-imp-elim-args proof))
	   (main-premise (car imp-elim-args))
	   (side-premise (cadr imp-elim-args))
	   (op2 (proof-in-elim-form-to-final-op proof)) ;Ex-Elim
	   (op1 (proof-in-elim-form-to-final-op main-premise))
	   (aconst1
	    (begin
	      (display (aconst-to-name
			(proof-in-aconst-form-to-aconst op1)))
	      (display "/")
	      (display (aconst-to-name
			(proof-in-aconst-form-to-aconst op2)))
	      (display " ")
	      (proof-in-aconst-form-to-aconst op1))) ;permutative aconst
	   (inst-formula1 (aconst-to-inst-formula aconst1))
	   (free1 (formula-to-free inst-formula1))
	   (args1 (proof-in-elim-form-to-args main-premise))
	   (params1 (list-head args1 (length free1)))
	   (rest-args1 (list-tail args1 (length free1)))
	   (end-formula (proof-to-formula proof))
	   (uninst-formula1 (aconst-to-uninst-formula aconst1))
	   (var-or-prem-list
	    (imp-impnc-all-allnc-form-to-vars-and-premises uninst-formula1))
	   (pvar (predicate-form-to-predicate
		  (imp-impnc-all-allnc-form-to-final-conclusion
		   uninst-formula1)))
	   (tpsubst (aconst-to-tpsubst aconst1))
	   (info (assoc pvar tpsubst))
	   (tpsubst-without-pvar
	    (if info
		(list-transform-positive tpsubst
		  (lambda (x) (not (equal? (car x) pvar))))
		tpsubst))
	   (subst-tpsubst-without-pvar
	    (if (equal? (map make-term-in-var-form free1) params1)
		tpsubst-without-pvar
		(let ((subst1 (map list free1 params1)))
		  (map (lambda (x)
			 (if (pvar? (car x))
			     (list (car x) (cterm-substitute (cadr x) subst1))
			     x))
		       tpsubst-without-pvar))))
	   (cterm (make-cterm end-formula))
	   (new-tpsubst
	    (if (pvar-cterm-equal? pvar cterm)
		subst-tpsubst-without-pvar
		(append subst-tpsubst-without-pvar (list (list pvar cterm)))))
	   (new-aconst1
	    (let* ((name (aconst-to-name aconst1))
		   (kind (aconst-to-kind aconst1))
		   (aconst-without-repro-formulas
		    (make-aconst name kind uninst-formula1 new-tpsubst)))
	      (apply make-aconst
		     name kind uninst-formula1 new-tpsubst
		     (aconst-to-computed-repro-data
		      aconst-without-repro-formulas))))
	   (new-free1 (formula-to-free (aconst-to-inst-formula new-aconst1)))
	   (rest-args1-pi
	    (do ((l1 var-or-prem-list (cdr l1))
		 (l2 rest-args1 (cdr l2))
		 (res
		  '()
		  (let ((uninst-arg (car l1))
			(arg1 (car l2)))
		    (if
		     (or (term-form? arg1)
			 (not (member pvar (formula-to-pvars uninst-arg))))
		     (cons arg1 res)
		     (let* ((l (length
				(imp-impnc-all-allnc-form-to-vars-and-premises
				 uninst-arg)))
			    (side-proof-kernel1
			     (proof-in-intro-form-to-final-kernel arg1 l))
			    (new-aconst2
			     (ex-formula-and-concl-to-ex-elim-aconst
			      (proof-to-formula side-proof-kernel1)
			      end-formula))
			    (new-free2 (formula-to-free
					(aconst-to-inst-formula new-aconst2)))
			    (new-side-proof-kernel1
			     (apply
			      mk-proof-in-elim-form
			      (make-proof-in-aconst-form new-aconst2)
			      (append
			       (map make-term-in-var-form new-free2)
			       (list side-proof-kernel1 side-premise))))
			    (abst-new-side-proof-kernel1
			     (intro-proof-and-new-kernel-and-depth-to-proof
			      arg1 new-side-proof-kernel1 l)))
		       (cons abst-new-side-proof-kernel1 res))))))
		((null? l1) (reverse res)))))
      (normalize-proof-pi-aux
       (apply mk-proof-in-elim-form
	      (make-proof-in-aconst-form new-aconst1)
	      (append (map make-term-in-var-form new-free1)
		      rest-args1-pi))
       extraction-flag content-flag))
					;proof is not a permutative redex:
    (case (tag proof)
      ((proof-in-avar-form proof-in-aconst-form) proof)
      ((proof-in-imp-intro-form)
       (let ((avar (proof-in-imp-intro-form-to-avar proof))
	     (kernel (proof-in-imp-intro-form-to-kernel proof)))
	 (make-proof-in-imp-intro-form
	  avar (normalize-proof-pi-aux kernel extraction-flag content-flag))))
      ((proof-in-imp-elim-form)
       (let ((op (proof-in-imp-elim-form-to-op proof))
	     (arg (proof-in-imp-elim-form-to-arg proof)))
	 (make-proof-in-imp-elim-form
	  (normalize-proof-pi-aux op extraction-flag content-flag)
	  (normalize-proof-pi-aux
	   arg extraction-flag
	   (not (formula-of-nulltype? (proof-to-formula arg)))))))
      ((proof-in-impnc-intro-form)
       (let ((avar (proof-in-impnc-intro-form-to-avar proof))
	     (kernel (proof-in-impnc-intro-form-to-kernel proof)))
	 (make-proof-in-impnc-intro-form
	  avar (normalize-proof-pi-aux kernel extraction-flag content-flag))))
      ((proof-in-impnc-elim-form)
       (let ((op (proof-in-impnc-elim-form-to-op proof))
	     (arg (proof-in-impnc-elim-form-to-arg proof)))
	 (make-proof-in-impnc-elim-form
	  (normalize-proof-pi-aux op extraction-flag content-flag)
	  (if (not extraction-flag)
	      (normalize-proof-pi-aux arg #f #t) ;content flag irrelevant here
	      arg))))
      ((proof-in-and-intro-form)
       (let ((left (proof-in-and-intro-form-to-left proof))
	     (right (proof-in-and-intro-form-to-right proof)))
	 (make-proof-in-and-intro-form
	  (normalize-proof-pi-aux
	   left extraction-flag
	   (not (formula-of-nulltype? (proof-to-formula left))))
	  (normalize-proof-pi-aux
	   right extraction-flag
	   (not (formula-of-nulltype? (proof-to-formula right)))))))
      ((proof-in-and-elim-left-form)
       (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
	 (make-proof-in-and-elim-left-form
	  (normalize-proof-pi-aux kernel extraction-flag #t))))
      ((proof-in-and-elim-right-form)
       (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
	 (make-proof-in-and-elim-right-form
	  (normalize-proof-pi-aux kernel extraction-flag #t))))
      ((proof-in-all-intro-form)
       (let ((var (proof-in-all-intro-form-to-var proof))
	     (kernel (proof-in-all-intro-form-to-kernel proof)))
	 (make-proof-in-all-intro-form
	  var (normalize-proof-pi-aux kernel extraction-flag content-flag))))
      ((proof-in-all-elim-form)
       (let ((op (proof-in-all-elim-form-to-op proof))
	     (arg (proof-in-all-elim-form-to-arg proof)))
	 (make-proof-in-all-elim-form
	  (normalize-proof-pi-aux op extraction-flag content-flag) arg)))
      ((proof-in-allnc-intro-form)
       (let ((var (proof-in-allnc-intro-form-to-var proof))
	     (kernel (proof-in-allnc-intro-form-to-kernel proof)))
	 (make-proof-in-allnc-intro-form
	  var (normalize-proof-pi-aux kernel extraction-flag content-flag))))
      ((proof-in-allnc-elim-form)
       (let ((op (proof-in-allnc-elim-form-to-op proof))
	     (arg (proof-in-allnc-elim-form-to-arg proof)))
	 (make-proof-in-allnc-elim-form
	  (normalize-proof-pi-aux op extraction-flag content-flag) arg)))
      (else (myerror "normalize-proof-pi-aux" "proof tag expected"
		     (tag proof)))))))

;; Test function to check normalize-proof-pi

(define (proof-in-permutative-normal-form? proof)
  (null? (proof-to-permutative-redexes proof)))

(define (proof-to-permutative-redexes proof)
  (if
   (permutative-redex? proof)
   (let* ((imp-elim-args (proof-to-imp-elim-args proof))
	  (main-premise (car imp-elim-args))
	  (side-premise (cadr imp-elim-args))
	  (op2 (proof-in-elim-form-to-final-op proof)) ;Ex-Elim
	  (op1 (proof-in-elim-form-to-final-op main-premise))
	  (aconst1 (proof-in-aconst-form-to-aconst op1))
	  (aconst2 (proof-in-aconst-form-to-aconst op2)))
     (append (list (string-append (aconst-to-name aconst1) "/"
				  (aconst-to-name aconst2)))
	     (proof-to-permutative-redexes main-premise)
	     (proof-to-permutative-redexes side-premise)))
   (case (tag proof)
     ((proof-in-avar-form proof-in-aconst-form) '())
     ((proof-in-imp-intro-form)
      (let ((kernel (proof-in-imp-intro-form-to-kernel proof)))
	(proof-to-permutative-redexes kernel)))
     ((proof-in-imp-elim-form)
      (let ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof)))
	(append (proof-to-permutative-redexes op)
		(proof-to-permutative-redexes arg))))
     ((proof-in-impnc-intro-form)
      (let ((kernel (proof-in-impnc-intro-form-to-kernel proof)))
	(proof-to-permutative-redexes kernel)))
     ((proof-in-impnc-elim-form)
      (let ((op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof)))
	(append (proof-to-permutative-redexes op)
		(proof-to-permutative-redexes arg))))
     ((proof-in-and-intro-form)
      (let ((left (proof-in-and-intro-form-to-left proof))
	    (right (proof-in-and-intro-form-to-right proof)))
	(append (proof-to-permutative-redexes left)
		(proof-to-permutative-redexes right))))
     ((proof-in-and-elim-left-form)
      (proof-to-permutative-redexes
       (proof-in-and-elim-left-form-to-kernel proof)))
     ((proof-in-and-elim-right-form)
      (proof-to-permutative-redexes
       (proof-in-and-elim-right-form-to-kernel proof)))
     ((proof-in-all-intro-form)
      (let ((kernel (proof-in-all-intro-form-to-kernel proof)))
	(proof-to-permutative-redexes kernel)))
     ((proof-in-all-elim-form)
      (let ((op (proof-in-all-elim-form-to-op proof)))
	(proof-to-permutative-redexes op)))
     ((proof-in-allnc-intro-form)
      (let ((kernel (proof-in-allnc-intro-form-to-kernel proof)))
	(proof-to-permutative-redexes kernel)))
     ((proof-in-allnc-elim-form)
      (let ((op (proof-in-allnc-elim-form-to-op proof)))
	(proof-to-permutative-redexes op)))
     (else (myerror "proof-to-permutative-redexes" "proof tag expected"
		    (tag proof))))))

(define (proof-in-normal-form? proof)
  (proof-in-normal-form-aux? proof #f #t))

(define (proof-in-normal-form-for-extraction? proof)
  (proof-in-normal-form-aux?
   proof #t (not (formula-of-nulltype? (proof-to-formula proof)))))

(define (proof-in-normal-form-aux? proof extraction-flag content-flag)
  (if
   (and extraction-flag (not content-flag))
   #t
   (case (tag proof)
     ((proof-in-avar-form proof-in-aconst-form) #t)
     ((proof-in-imp-intro-form)
      (let ((kernel (proof-in-imp-intro-form-to-kernel proof)))
	(proof-in-normal-form-aux?
	 kernel extraction-flag content-flag)))
     ((proof-in-imp-elim-form)
      (let ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof)))
	(cond
	 ((proof-in-imp-intro-form? op) #f)
	 ((and
	   (proof-in-imp-elim-form? op)
	   (let ((op1 (proof-in-imp-elim-form-to-op op)))
	     (and
	      (proof-in-aconst-form? op1)
	      (string=? "Ex-Elim" (aconst-to-name
				   (proof-in-aconst-form-to-aconst op1)))
	      (let ((arg1 (proof-in-imp-elim-form-to-arg op)))
		(and (proof-in-imp-elim-form? arg1)
		     (let ((op2 (proof-in-imp-elim-form-to-op arg1)))
		       (and (proof-in-all-elim-form? op2)
			    (let ((op3 (proof-in-all-elim-form-to-op op2)))
			      (and (proof-in-aconst-form? op3)
				   (string=? "Ex-Intro"
					     (aconst-to-name
					      (proof-in-aconst-form-to-aconst
					       op3))))))))))))
	  #f)
	 ((proof-in-idpredconst-elim-intro-redex-form? proof) #f)
	 (else (and (proof-in-normal-form-aux?
		     op extraction-flag content-flag)
		    (proof-in-normal-form-aux?
		     arg extraction-flag
		     (not (formula-of-nulltype? (proof-to-formula arg)))))))))
     ((proof-in-impnc-intro-form)
      (let ((kernel (proof-in-impnc-intro-form-to-kernel proof)))
	(proof-in-normal-form-aux? kernel extraction-flag content-flag)))
     ((proof-in-impnc-elim-form)
      (let ((op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof)))
	(if
	 (proof-in-impnc-intro-form? op)
	 #f
	 (proof-in-normal-form-aux? op extraction-flag content-flag))))
     ((proof-in-and-intro-form)
      (let ((left (proof-in-and-intro-form-to-left proof))
	    (right (proof-in-and-intro-form-to-right proof)))
	(and (proof-in-normal-form-aux?
	      left extraction-flag
	      (not (formula-of-nulltype? (proof-to-formula left))))
	     (proof-in-normal-form-aux?
	      right extraction-flag
	      (not (formula-of-nulltype? (proof-to-formula right)))))))
     ((proof-in-and-elim-left-form)
      (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
	(and (not (proof-in-and-intro-form? kernel))
	     (proof-in-normal-form-aux?
	      kernel extraction-flag content-flag))))
     ((proof-in-and-elim-right-form)
      (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
	(and (not (proof-in-and-intro-form? kernel))
	     (proof-in-normal-form-aux?
	      kernel extraction-flag content-flag))))
     ((proof-in-all-intro-form)
      (let ((kernel (proof-in-all-intro-form-to-kernel proof)))
	(proof-in-normal-form-aux? kernel extraction-flag content-flag)))
     ((proof-in-all-elim-form)
      (let ((op (proof-in-all-elim-form-to-op proof)))
	(and
	 (not (proof-in-all-intro-form? op))
	 (proof-in-normal-form-aux? op extraction-flag content-flag))))
     ((proof-in-allnc-intro-form)
      (let ((kernel (proof-in-allnc-intro-form-to-kernel proof)))
	(proof-in-normal-form-aux? kernel extraction-flag content-flag)))
     ((proof-in-allnc-elim-form)
      (let ((op (proof-in-allnc-elim-form-to-op proof)))
	(and
	 (not (proof-in-allnc-intro-form? op))
	 (proof-in-normal-form-aux? op extraction-flag content-flag))))
     (else (myerror "proof-in-normal-form-aux?" "proof tag expected"
		    (tag proof))))))

;; Normalization of proofs is made more efficient by allowing to know
;; whether one is interested in extraction, and if so, disregard parts
;; of the proof without computational content.  The extraction-flag
;; indicates whether we are interested in extraction only.  If so, we
;; can disregard (maximal) parts of the proof without computational
;; content.  The content-flag indicates whether the formula of the
;; proof has computational content.  This is for efficiency only, since
;; it avoids recomputation.  When extraction-flag is #f content-flag is
;; irrelevant.

(define (nbe-normalize-proof proof)
  (nbe-normalize-proof-aux proof #f #t))

(define (nbe-normalize-proof-for-extraction proof)
  (nbe-normalize-proof-aux
   proof #t (not (formula-of-nulltype? (proof-to-formula proof)))))

(define (nbe-normalize-proof-aux proof extraction-flag content-flag)
  (let ((init (normalize-proof-pi-aux
	       (nbe-normalize-proof-without-eta-aux
		(proof-to-proof-with-eta-expanded-permutative-aconsts-aux
		 proof extraction-flag content-flag)
		extraction-flag content-flag)
	       extraction-flag content-flag)))
    (do ((p init (normalize-proof-pi-aux
		  (nbe-normalize-proof-without-eta-aux
		   p extraction-flag content-flag)
		  extraction-flag content-flag)))
	((proof-in-normal-form-aux? p extraction-flag content-flag)
	 (proof-to-eta-nf-aux p extraction-flag content-flag)))))

(define np nbe-normalize-proof)
(define npe nbe-normalize-proof-for-extraction)

;; When normalizing a proof via nbe in the elim case the associated
;; rec constant has to accomodate the free variables in inst-formula
;; of the elim-aconst.  The tvars in their types may be affected by
;; the tpsubst of the elim-aconst.  When such a type clash occurs, we
;; rename type variables implicitly bound by tsubst away from tvars.

(define (aconst-rename aconst tvars)
  (let* ((tpsubst (aconst-to-tpsubst aconst))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (fla-tvars (formula-to-tvars uninst-formula))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		   (lambda (x) (pvar-form? (car x)))))
	 (crit-tvars (intersection (map car tsubst) fla-tvars))
	 (rest-tvars (set-minus (map car tsubst) crit-tvars))
	 (renaming-tsubst (map (lambda (tvar) (list tvar (new-tvar)))
			       crit-tvars))
	 (crit-pvars (list-transform-positive (map car psubst)
		       (lambda (pvar)
			 (pair? (intersection
				 tvars (apply
					union (map type-to-tvars
						   (arity-to-types
						    (predicate-to-arity
						     pvar)))))))))
	 (rest-pvars (set-minus (map car psubst) crit-pvars))
	 (renaming-psubst
	  (map (lambda (pvar)
		 (list pvar
		       (predicate-to-cterm
			(arity-to-new-general-pvar
			 (apply make-arity
				(map (lambda (type)
				       (type-substitute type renaming-tsubst))
				     (arity-to-types
				      (predicate-to-arity pvar))))))))
	       crit-pvars))
	 (renaming-tpsubst (append renaming-tsubst renaming-psubst))
	 (renamed-uninst-formula
	  (formula-substitute uninst-formula renaming-tpsubst))
	 (rev-renaming-tsubst (map reverse renaming-tsubst))
	 (rev-renaming-psubst
	  (map (lambda (x)
		 (let* ((pvar (car x))
			(cterm (cadr x)))
		   (list (predicate-form-to-predicate (cterm-to-formula cterm))
			 (predicate-to-cterm pvar))))
	       renaming-psubst))
	 (rev-renaming-tpsubst (append rev-renaming-tsubst
				       rev-renaming-psubst))
	 (composed-tpsubst (compose-substitutions rev-renaming-tpsubst tpsubst))
	 ;; first rev-renaming-tpsubst, then tpsubst
	 (restricted-composed-tpsubst
	  (list-transform-positive composed-tpsubst
	    (lambda (x) (member (car x)
				(append (map car rev-renaming-tpsubst)
					rest-tvars rest-pvars))))))
    (apply
     make-aconst
     (aconst-to-name aconst)
     (aconst-to-kind aconst)
     (formula-substitute uninst-formula renaming-tpsubst)
     restricted-composed-tpsubst
     (aconst-to-repro-data aconst))))

;; Now proof transformations (Prawitz' simplification, removal of
;; predecided avars, removal of predecided if theorems, generalized
;; pruning).

;; Simplification conversions (Prawitz) make use of the concept of a
;; permutative aconst.  It is checked whether one side-proof-kernel has
;; no free occurrence of any avar bound in this side-proof.

(define (normalize-proof-simp proof)
  (case (tag proof)
    ((proof-in-avar-form proof-in-aconst-form) proof)
    ((proof-in-imp-intro-form)
     (let ((avar (proof-in-imp-intro-form-to-avar proof))
	   (kernel (proof-in-imp-intro-form-to-kernel proof)))
       (make-proof-in-imp-intro-form avar (normalize-proof-simp kernel))))
    ((proof-in-impnc-intro-form)
     (let ((avar (proof-in-impnc-intro-form-to-avar proof))
	   (kernel (proof-in-impnc-intro-form-to-kernel proof)))
       (make-proof-in-impnc-intro-form avar (normalize-proof-simp kernel))))
    ((proof-in-and-intro-form)
     (let ((left (proof-in-and-intro-form-to-left proof))
	   (right (proof-in-and-intro-form-to-right proof)))
       (make-proof-in-and-intro-form (normalize-proof-simp left)
				     (normalize-proof-simp right))))
    ((proof-in-and-elim-left-form)
     (make-proof-in-and-elim-left-form
      (normalize-proof-simp (proof-in-and-elim-left-form-to-kernel proof))))
    ((proof-in-and-elim-right-form)
     (make-proof-in-and-elim-right-form
      (normalize-proof-simp (proof-in-and-elim-right-form-to-kernel proof))))
    ((proof-in-all-intro-form)
     (let ((var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-proof-in-all-intro-form var (normalize-proof-simp kernel))))
    ((proof-in-allnc-intro-form)
     (let ((var (proof-in-allnc-intro-form-to-var proof))
	   (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-proof-in-allnc-intro-form var (normalize-proof-simp kernel))))
    ((proof-in-imp-elim-form
      proof-in-impnc-elim-form
      proof-in-all-elim-form
      proof-in-allnc-elim-form)
     (let* ((op (proof-in-elim-form-to-final-op proof))
	    (args (proof-in-elim-form-to-args proof))
	    (simp-args (map (lambda (arg)
			      (if (proof-form? arg)
				  (normalize-proof-simp arg)
				  arg))
			    args)))
       (if
	(not (proof-in-aconst-form? op))
	(apply mk-proof-in-elim-form op simp-args)
	(let ((aconst (proof-in-aconst-form-to-aconst op)))
	  (if
	   (not (permutative-aconst? aconst))
	   (apply mk-proof-in-elim-form op simp-args)
	   (let* ((uninst-formula (aconst-to-uninst-formula aconst))
		  (var-or-prem-list
		   (imp-impnc-all-allnc-form-to-vars-and-premises
		    uninst-formula))
		  (inst-formula (aconst-to-inst-formula aconst))
		  (free (formula-to-free inst-formula)))
	     (if
	      (< (length args) (length free))
	      (apply mk-proof-in-elim-form op simp-args)
	      (let ((params (list-head args (length free)))
		    (rest-args (list-tail simp-args (length free))))
		(if
		 (< (length rest-args) (length var-or-prem-list))
		 (apply mk-proof-in-elim-form op simp-args)
		 (let*
		     ((further-rest-args
		       (list-tail rest-args (length var-or-prem-list)))
		      (final-concl
		       (imp-impnc-all-allnc-form-to-final-conclusion
			uninst-formula))
		      (pvar (predicate-form-to-predicate final-concl))
		      (prems
		       (imp-impnc-all-allnc-form-to-premises uninst-formula))
		      (prems-with-pvar
		       (list-transform-positive prems
			 (lambda (x) (member pvar (formula-to-pvars x)))))
		      (args-for-simplification
		       (do ((l1 var-or-prem-list (cdr l1))
			    (l2 rest-args (cdr l2))
			    (res
			     '()
			     (let ((var-or-prem (car l1))
				   (arg (car l2)))
			       (if
				(or
				 (var-form? var-or-prem)
				 (not (member
				       pvar (formula-to-pvars var-or-prem))))
				res
				(let*
				    ((prem-var-or-prem-list
				      (imp-impnc-all-allnc-form-to-vars-and-premises
				       var-or-prem))
				     (l (length prem-var-or-prem-list))
				     (side-proof-kernel
				      (proof-in-intro-form-to-final-kernel
				       arg l))
				     (side-proof-vars
				      (proof-in-intro-form-to-vars arg l)))
				  (if (pair?
				       (intersection-wrt
					avar=?
					(proof-to-free-avars side-proof-kernel)
					side-proof-vars))
				      res
				      (cons side-proof-kernel res)))))))
			   ((null? l1) (reverse res)))))
		   (cond
		    ((null? args-for-simplification)
		     (apply mk-proof-in-elim-form op simp-args))
		    ((null? further-rest-args)
		     (car args-for-simplification))
		    (else (normalize-proof-simp
			   (apply mk-proof-in-elim-form
				  (car args-for-simplification)
				  further-rest-args))))))))))))))
    (else (myerror "normalize-proof-simp" "proof tag expected"
		   (tag proof)))))

;; proof-to-proof-without-predecided-avars removes dependencies on
;; avars, and in this way helps to make normalize-proof-simp useful.

(define (proof-to-proof-without-predecided-avars proof)
  (proof-and-context-to-proof-without-predecided-avars proof '()))

(define (proof-and-context-to-proof-without-predecided-avars proof context)
  (case (tag proof)
    ((proof-in-avar-form proof-in-aconst-form) proof)
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (avars (context-to-avars context))
	    (previous-avar (do ((l avars (cdr l))
				(res #f (if (classical-formula=?
					     (avar-to-formula (car l))
					     (avar-to-formula avar))
					    (car l)
					    #f)))
			       ((or res (null? l)) res))))
       (make-proof-in-imp-intro-form
	avar (proof-and-context-to-proof-without-predecided-avars
	      (if previous-avar
		  (proof-subst kernel avar (make-proof-in-avar-form
					    previous-avar))
		  kernel)
	      (append context (list avar))))))
    ((proof-in-imp-elim-form)
     (let ((op (proof-in-imp-elim-form-to-op proof))
	   (arg (proof-in-imp-elim-form-to-arg proof)))
       (make-proof-in-imp-elim-form
	(proof-and-context-to-proof-without-predecided-avars op context)
	(proof-and-context-to-proof-without-predecided-avars arg context))))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (avars (context-to-avars context))
	    (previous-avar (do ((l avars (cdr l))
				(res #f (if (classical-formula=?
					     (avar-to-formula (car l))
					     (avar-to-formula avar))
					    (car l)
					    #f)))
			       ((or res (null? l)) res))))
       (make-proof-in-impnc-intro-form
	avar (proof-and-context-to-proof-without-predecided-avars
	      (if previous-avar
		  (proof-subst kernel avar (make-proof-in-avar-form
					    previous-avar))
		  kernel)
	      (append context (list avar))))))
    ((proof-in-impnc-elim-form)
     (let ((op (proof-in-impnc-elim-form-to-op proof))
	   (arg (proof-in-impnc-elim-form-to-arg proof)))
       (make-proof-in-impnc-elim-form
	(proof-and-context-to-proof-without-predecided-avars op context)
	(proof-and-context-to-proof-without-predecided-avars arg context))))
    ((proof-in-and-intro-form)
     (let ((left (proof-in-and-intro-form-to-left proof))
	   (right (proof-in-and-intro-form-to-right proof)))
       (make-proof-in-and-intro-form
	(proof-and-context-to-proof-without-predecided-avars left context)
	(proof-and-context-to-proof-without-predecided-avars right context))))
    ((proof-in-and-elim-left-form)
     (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (make-proof-in-and-elim-left-form
	(proof-and-context-to-proof-without-predecided-avars kernel context))))
    ((proof-in-and-elim-right-form)
     (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (make-proof-in-and-elim-right-form
	(proof-and-context-to-proof-without-predecided-avars kernel context))))
    ((proof-in-all-intro-form)
     (let ((var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-proof-in-all-intro-form
	var (proof-and-context-to-proof-without-predecided-avars
	     kernel (append context (list var))))))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
       (make-proof-in-all-elim-form
	(proof-and-context-to-proof-without-predecided-avars op context)
	arg)))
    ((proof-in-allnc-intro-form)
     (let ((var (proof-in-allnc-intro-form-to-var proof))
	   (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-proof-in-allnc-intro-form
	var (proof-and-context-to-proof-without-predecided-avars
	     kernel (append context (list var))))))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof))
	   (arg (proof-in-allnc-elim-form-to-arg proof)))
       (make-proof-in-allnc-elim-form
	(proof-and-context-to-proof-without-predecided-avars op context)
	arg)))
    (else
     (myerror "proof-and-context-to-proof-without-predecided-avars"
	      "unexpected proof tag" (tag proof)))))

;; Removal of predecided If's (special for pruning), including those
;; with True or False as boolean arguments.  negatom-context consists
;; of all atomic or negated avars in the present context.

(define (remove-predecided-if-theorems proof)
  (remove-predecided-if-theorems-aux proof '()))

(define (remove-predecided-if-theorems-aux proof negatom-context)
  (case (tag proof)
    ((proof-in-avar-form proof-in-aconst-form) proof)
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (formula (avar-to-formula avar))
	    (new-negatom-context ;add avar if a (possibly negated) atom
	     (if (or (atom-form? formula)
		     (and (imp-form? formula)
			  (atom-form? (imp-form-to-premise formula))
			  (formula=? (imp-form-to-conclusion formula)
				     falsity)))
		 (cons avar negatom-context)
		 negatom-context))
	    (prev (remove-predecided-if-theorems-aux
		   kernel new-negatom-context)))
       (make-proof-in-imp-intro-form avar prev)))
    ((proof-in-imp-elim-form)
     (let* ((final-op (proof-in-elim-form-to-final-op proof))
	    (args (proof-in-elim-form-to-args proof)))
       (if ;If-theorem with exactly 3 non-parameter args
	(and
	 (proof-in-aconst-form? final-op)
	 (let* ((aconst (proof-in-aconst-form-to-aconst final-op))
		(name (aconst-to-name aconst)))
	   (and
	    (string=? "If" name)
	    (let* ((term-args (do ((l args (cdr l))
				   (res '() (if (term-form? (car l))
						(cons (car l) res)
						(cons #f res))))
				  ((not (term-form? (car l))) (reverse res))))
		   (rest-args (list-tail args (length term-args))))
	      (and (= 2 (length rest-args))
		   (proof-in-imp-intro-form? (car rest-args))
		   (proof-in-imp-intro-form? (cadr rest-args)))))))
	(let* ((term-args (do ((l args (cdr l))
			       (res '() (if (term-form? (car l))
					    (cons (car l) res)
					    (cons #f res))))
			      ((not (term-form? (car l))) (reverse res))))
	       (boolean-arg (car (last-pair term-args)))
	       (rest-args (list-tail args (length term-args))))
	  (cond
	   ((term=? (make-term-in-const-form true-const) boolean-arg)
	    (let* ((arg1 (car rest-args))
		   (avar1 (proof-in-imp-intro-form-to-avar arg1))
		   (kernel1 (proof-in-imp-intro-form-to-kernel arg1))
		   (subst-kernel (proof-subst
				  kernel1 avar1
				  (make-proof-in-aconst-form truth-aconst))))
	      (remove-predecided-if-theorems-aux subst-kernel negatom-context)))
	   ((term=? (make-term-in-const-form false-const) boolean-arg)
	    (let* ((arg2 (cadr rest-args))
		   (avar2 (proof-in-imp-intro-form-to-avar arg2))
		   (kernel2 (proof-in-imp-intro-form-to-kernel arg2))
		   (false-avar (formula-to-new-avar falsity))
		   (subst-kernel (proof-subst
				  kernel2 avar2
				  (make-proof-in-imp-intro-form
				   false-avar
				   (make-proof-in-avar-form false-avar)))))
	      (remove-predecided-if-theorems-aux
	       subst-kernel negatom-context)))
	   (else
	    (let ((proof (negatom-context-and-bterm-to-proof
			  negatom-context boolean-arg)))
	      (if ;proof is found
	       proof
	       (if ;proof of (atom boolean-arg)
		(atom-form? (proof-to-formula proof))
		(let* ((arg1 (car rest-args))
		       (avar1 (proof-in-imp-intro-form-to-avar arg1))
		       (kernel1 (proof-in-imp-intro-form-to-kernel arg1))
		       (subst-kernel1 (proof-subst kernel1 avar1 proof)))
		  (remove-predecided-if-theorems-aux
		   subst-kernel1 negatom-context))
					;or proof of (atom boolean-arg) -> F
		(let* ((arg2 (cadr rest-args))
		       (avar2 (proof-in-imp-intro-form-to-avar arg2))
		       (kernel2 (proof-in-imp-intro-form-to-kernel arg2))
		       (subst-kernel2 (proof-subst kernel2 avar2 proof)))
		  (remove-predecided-if-theorems-aux
		   subst-kernel2 negatom-context)))
	       (apply
		mk-proof-in-elim-form
		final-op
		(append term-args
			(list (remove-predecided-if-theorems-aux
			       (car rest-args) negatom-context)
			      (remove-predecided-if-theorems-aux
			       (cadr rest-args) negatom-context)))))))))
	(let* ((op (proof-in-imp-elim-form-to-op proof))
	       (arg (proof-in-imp-elim-form-to-arg proof))
	       (prev1 (remove-predecided-if-theorems-aux
		       op negatom-context))
	       (prev2 (remove-predecided-if-theorems-aux
		       arg negatom-context)))
	  (make-proof-in-imp-elim-form prev1 prev2)))))
    ((proof-in-and-intro-form)
     (let* ((left (proof-in-and-intro-form-to-left proof))
	    (right (proof-in-and-intro-form-to-right proof))
	    (prev1 (remove-predecided-if-theorems-aux left negatom-context))
	    (prev2 (remove-predecided-if-theorems-aux right negatom-context)))
       (make-proof-in-and-intro-form prev1 prev2)))
    ((proof-in-and-elim-left-form)
     (let* ((kernel (proof-in-and-elim-left-form-to-kernel proof))
	    (prev (remove-predecided-if-theorems-aux kernel negatom-context)))
       (make-proof-in-and-elim-left-form prev)))
    ((proof-in-and-elim-right-form)
     (let* ((kernel (proof-in-and-elim-right-form-to-kernel proof))
	    (prev (remove-predecided-if-theorems-aux kernel negatom-context)))
       (make-proof-in-and-elim-right-form prev)))
    ((proof-in-all-intro-form)
     (let* ((var (proof-in-all-intro-form-to-var proof))
	    (kernel (proof-in-all-intro-form-to-kernel proof))
	    (prev (remove-predecided-if-theorems-aux kernel negatom-context)))
       (make-proof-in-all-intro-form var prev)))
    ((proof-in-all-elim-form)
     (let* ((op (proof-in-all-elim-form-to-op proof))
	    (arg (proof-in-all-elim-form-to-arg proof))
	    (prev (remove-predecided-if-theorems-aux op negatom-context)))
       (make-proof-in-all-elim-form prev arg)))
    ((proof-in-allnc-intro-form)
     (let* ((var (proof-in-allnc-intro-form-to-var proof))
	    (kernel (proof-in-allnc-intro-form-to-kernel proof))
	    (prev (remove-predecided-if-theorems-aux kernel negatom-context)))
       (make-proof-in-allnc-intro-form var prev)))
    ((proof-in-allnc-elim-form)
     (let* ((op (proof-in-allnc-elim-form-to-op proof))
	    (arg (proof-in-allnc-elim-form-to-arg proof))
	    (prev (remove-predecided-if-theorems-aux op negatom-context)))
       (make-proof-in-allnc-elim-form prev arg)))
    (else (myerror "remove-predecided-if-theorems-aux"
		   "not implemented for" (tag proof)))))

;; term-to-minuend-and-subtrahends writes the term in the form
;; j--i0--i1..--in and returns j and the list (i0 i1 .. in) (the
;; minuend and the subtrahends).

(define (term-to-minuend-and-subtrahends term)
  (let ((op (term-in-app-form-to-final-op term)))
    (if
     (and
      (term-in-const-form? op)
      (string=? (const-to-name (term-in-const-form-to-const op)) "NatMinus"))
     (let* ((args (term-in-app-form-to-args term))
	    (lhs (car args))
	    (rhs (cadr args))
	    (prev (term-to-minuend-and-subtrahends lhs))
	    (minuend (car prev))
	    (subtrahends (cadr prev)))
       (list minuend (append subtrahends (list rhs))))
     (list term '()))))

;; (pp (car (term-to-minuend-and-subtrahends (pt "j--i1--i2"))))
;; (for-each pp (cadr (term-to-minuend-and-subtrahends (pt "j--i1--i2"))))

;; Consider avar:i<=j--i0--i1--i2 and subtrahends (i1 i2).  Then j--i0
;; is the minuend.  We construct a proof of i<=j--i0 from avar.

(define (le-minuend-minus-subtrahends-avar-and-subtrahends-to-proof
	 avar subtrahends)
  (if
   (null? subtrahends)
   (make-proof-in-avar-form avar)
   (let* ((init-subtrahend (car subtrahends)) ;not used!
	  (rest-subtrahends (cdr subtrahends))
	  (prev (le-minuend-minus-subtrahends-avar-and-subtrahends-to-proof
		 avar rest-subtrahends))
	  (formula (proof-to-formula prev))
	  (kernel (atom-form-to-kernel formula))
	  (args (term-in-app-form-to-args kernel))
	  (lhs (car args))
	  (minuend (cadr args))
	  (new-minuend (car (term-in-app-form-to-args minuend))))
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form (theorem-name-to-aconst "NatLeTrans"))
      lhs minuend new-minuend
      prev
      (make-proof-in-aconst-form truth-aconst)))))

;; (cdp (le-minuend-minus-subtrahends-avar-and-subtrahends-to-proof
;;       (formula-to-new-avar (pf "i<=j--i0--i1--i2"))
;;       (list (pt "i0") (pt "i1")  (pt "i2"))))

;; negatom-context-and-bterm-to-proof returns either a proof of bterm
;; from the positive context or else a proof of the negation of bterm
;; from the negative context if it finds one of them, and #f otherwise.
;; Because of its usage of term-to-minuend-and-subtrahends and
;; le-minuend-minus-subtrahends-avar-and-subtrahends-to-proof it is
;; designed for use in the binpack case study, where the boolean terms
;; are of the form i<=j--i0--...--in.  It would be better if a more
;; general decision procedure is used (simplex-algorithm?).

(define (negatom-context-and-bterm-to-proof negatom-context bterm)
  (let ((op (term-in-app-form-to-final-op bterm)))
    (and
     (term-in-const-form? op)
     (string=? (const-to-name (term-in-const-form-to-const op)) "NatLe")
     (let* ((args (term-in-app-form-to-args bterm))
	    (lhs (car args))
	    (rhs (cadr args))
	    (minuend-and-subtrahends (term-to-minuend-and-subtrahends rhs))
	    (minuend (car minuend-and-subtrahends))
	    (subtrahends (cadr minuend-and-subtrahends))
	    (pos-fitting-context
	     (list-transform-positive negatom-context
	       (lambda (avar)
		 (let ((avar-fla (avar-to-formula avar)))
		   (and
		    (atom-form? avar-fla)
		    (let* ((avar-kernel (atom-form-to-kernel avar-fla))
			   (avar-op
			    (term-in-app-form-to-final-op avar-kernel)))
		      (and
		       (term-in-const-form? avar-op)
		       (string=?
			(const-to-name (term-in-const-form-to-const avar-op))
			"NatLe")
		       (let* ((avar-args
			       (term-in-app-form-to-args avar-kernel))
			      (avar-lhs (car avar-args))
			      (avar-rhs (cadr avar-args))
			      (avar-minuend-and-subtrahends
			       (term-to-minuend-and-subtrahends avar-rhs))
			      (avar-minuend (car avar-minuend-and-subtrahends))
			      (avar-subtrahends
			       (cadr avar-minuend-and-subtrahends)))
			 (and
			  (term=? lhs avar-lhs)
			  (term=? minuend avar-minuend)
			  (<= (length subtrahends) (length avar-subtrahends))
			  (apply and-op
				 (map term=?
				      subtrahends
				      (list-head
				       avar-subtrahends
				       (length subtrahends)))))))))))))
	    (neg-fitting-context
	     (list-transform-positive negatom-context
	       (lambda (avar)
		 (let ((avar-fla (avar-to-formula avar)))
		   (and
		    (imp-impnc-form? avar-fla)
		    (formula=? (imp-impnc-form-to-conclusion avar-fla)
			       falsity)
		    (atom-form? (imp-impnc-form-to-premise avar-fla))
		    (let* ((avar-atom (imp-impnc-form-to-premise avar-fla))
			   (avar-kernel (atom-form-to-kernel avar-atom))
			   (avar-op
			    (term-in-app-form-to-final-op avar-kernel)))
		      (and
		       (term-in-const-form? avar-op)
		       (string=?
			(const-to-name (term-in-const-form-to-const avar-op))
			"NatLe")
		       (let* ((avar-args
			       (term-in-app-form-to-args avar-kernel))
			      (avar-lhs (car avar-args))
			      (avar-rhs (cadr avar-args))
			      (avar-minuend-and-subtrahends
			       (term-to-minuend-and-subtrahends avar-rhs))
			      (avar-minuend (car avar-minuend-and-subtrahends))
			      (avar-subtrahends
			       (cadr avar-minuend-and-subtrahends)))
			 (and
			  (term=? lhs avar-lhs)
			  (term=? minuend avar-minuend)
			  (<= (length avar-subtrahends) (length subtrahends))
			  (apply and-op
				 (map term=?
				      avar-subtrahends
				      (list-head
				       subtrahends
				       (length avar-subtrahends))))))))))))))
       (and
	(or (pair? pos-fitting-context) (pair? neg-fitting-context))
	(if (pair? pos-fitting-context)
	    (let* ((avar (car pos-fitting-context))
		   (avar-fla (avar-to-formula avar))
		   (avar-kernel (atom-form-to-kernel avar-fla))
		   (avar-args (term-in-app-form-to-args avar-kernel))
		   (avar-rhs (cadr avar-args))
		   (avar-minuend-and-subtrahends
		    (term-to-minuend-and-subtrahends avar-rhs))
		   (avar-subtrahends (cadr avar-minuend-and-subtrahends))
		   (rest-avar-subtrahends
		    (list-tail avar-subtrahends (length subtrahends))))
	      (le-minuend-minus-subtrahends-avar-and-subtrahends-to-proof
	       avar rest-avar-subtrahends))
					;else (pair? neg-fitting-context)
	    (let* ((avar (car neg-fitting-context))
		   (avar-fla (avar-to-formula avar))
		   (avar-atom (imp-impnc-form-to-premise avar-fla))
		   (avar-kernel (atom-form-to-kernel avar-atom))
		   (avar-args (term-in-app-form-to-args avar-kernel))
		   (avar-rhs (cadr avar-args))
		   (avar-minuend-and-subtrahends
		    (term-to-minuend-and-subtrahends avar-rhs))
		   (avar-subtrahends (cadr avar-minuend-and-subtrahends))
		   (rest-subtrahends
		    (list-tail subtrahends (length avar-subtrahends)))
		   (bterm-atom (make-atomic-formula bterm))
		   (bterm-avar (formula-to-new-avar bterm-atom))
		   (proof-of-avar-prem
		    (le-minuend-minus-subtrahends-avar-and-subtrahends-to-proof
		     bterm-avar rest-subtrahends))
		   (proof-of-falsity
		    (mk-proof-in-elim-form
		     (make-proof-in-avar-form avar) proof-of-avar-prem)))
	      (make-proof-in-imp-intro-form
	       bterm-avar proof-of-falsity))))))))

;; Generalization of Prawitz' simplification: pruning.  A problem with
;; prune is that is is slow.  For efficiency the proof is first turned
;; into an acproof, to avoid recomputation of avar-contexts when
;; pruning.

(define (prune proof)
  (acproof-to-pruned-proof (proof-to-acproof proof)))

(define (acproof-to-pruned-proof acproof)
  (let ((formula (proof-to-formula acproof)))
    (case (tag acproof)
      ((proof-in-avar-form proof-in-aconst-form) acproof)
      ((proof-in-imp-intro-form)
       (let* ((avar (proof-in-imp-intro-form-to-avar acproof))
	      (kernel (proof-in-imp-intro-form-to-kernel acproof))
	      (proof-of-formula-or-f (prune-aux formula (list avar) kernel)))
	 (if proof-of-formula-or-f
	     (acproof-to-pruned-proof proof-of-formula-or-f)
	     (make-proof-in-imp-intro-form
	      avar (acproof-to-pruned-proof kernel)))))
      ((proof-in-imp-elim-form)
       (let* ((op (proof-in-imp-elim-form-to-op acproof))
	      (arg (proof-in-imp-elim-form-to-arg acproof))
	      (proof-of-formula-or-f1 (prune-aux formula '() op)))
	 (if
	  proof-of-formula-or-f1
	  (acproof-to-pruned-proof proof-of-formula-or-f1)
	  (let ((proof-of-formula-or-f2 (prune-aux formula '() arg)))
	    (if
	     proof-of-formula-or-f2
	     (acproof-to-pruned-proof proof-of-formula-or-f2)
	     (make-proof-in-imp-elim-form
	      (acproof-to-pruned-proof op) (acproof-to-pruned-proof arg)))))))
      ((proof-in-impnc-intro-form)
       (let* ((avar (proof-in-impnc-intro-form-to-avar acproof))
	      (kernel (proof-in-impnc-intro-form-to-kernel acproof))
	      (proof-of-formula-or-f (prune-aux formula (list avar) kernel)))
	 (if proof-of-formula-or-f
	     (acproof-to-pruned-proof proof-of-formula-or-f)
	     (make-proof-in-impnc-intro-form
	      avar (acproof-to-pruned-proof kernel)))))
      ((proof-in-impnc-elim-form)
       (let* ((op (proof-in-impnc-elim-form-to-op acproof))
	      (arg (proof-in-impnc-elim-form-to-arg acproof))
	      (proof-of-formula-or-f1 (prune-aux formula '() op)))
	 (if
	  proof-of-formula-or-f1
	  (acproof-to-pruned-proof proof-of-formula-or-f1)
	  (let ((proof-of-formula-or-f2 (prune-aux formula '() arg)))
	    (if
	     proof-of-formula-or-f2
	     (acproof-to-pruned-proof proof-of-formula-or-f2)
	     (make-proof-in-impnc-elim-form
	      (acproof-to-pruned-proof op) (acproof-to-pruned-proof arg)))))))
      ((proof-in-and-intro-form)
       (let* ((left (proof-in-and-intro-form-to-left acproof))
	      (right (proof-in-and-intro-form-to-right acproof))
	      (proof-of-formula-or-f1 (prune-aux formula '() left)))
	 (if
	  proof-of-formula-or-f1
	  (acproof-to-pruned-proof proof-of-formula-or-f1)
	  (let ((proof-of-formula-or-f2 (prune-aux formula '() right)))
	    (if
	     proof-of-formula-or-f2
	     (acproof-to-pruned-proof proof-of-formula-or-f2)
	     (make-proof-in-and-intro-form
	      (acproof-to-pruned-proof left)
	      (acproof-to-pruned-proof right)))))))
      ((proof-in-and-elim-left-form)
       (let* ((kernel (proof-in-and-elim-left-form-to-kernel acproof))
	      (proof-of-formula-or-f (prune-aux formula '() kernel)))
	 (if proof-of-formula-or-f
	     (acproof-to-pruned-proof proof-of-formula-or-f)
	     (make-proof-in-and-elim-left-form
	      (acproof-to-pruned-proof kernel)))))
      ((proof-in-and-elim-right-form)
       (let* ((kernel (proof-in-and-elim-right-form-to-kernel acproof))
	      (proof-of-formula-or-f (prune-aux formula '() kernel)))
	 (if proof-of-formula-or-f
	     (acproof-to-pruned-proof proof-of-formula-or-f)
	     (make-proof-in-and-elim-right-form
	      (acproof-to-pruned-proof kernel)))))
      ((proof-in-all-intro-form)
       (let* ((var (proof-in-all-intro-form-to-var acproof))
	      (kernel (proof-in-all-intro-form-to-kernel acproof))
	      (proof-of-formula-or-f (prune-aux formula '() kernel)))
	 (if proof-of-formula-or-f
	     (acproof-to-pruned-proof proof-of-formula-or-f)
	     (make-proof-in-all-intro-form
	      var (acproof-to-pruned-proof kernel)))))
      ((proof-in-all-elim-form)
       (let* ((op (proof-in-all-elim-form-to-op acproof))
	      (arg (proof-in-all-elim-form-to-arg acproof))
	      (proof-of-formula-or-f (prune-aux formula '() op)))
	 (if proof-of-formula-or-f
	     (acproof-to-pruned-proof proof-of-formula-or-f)
	     (make-proof-in-all-elim-form
	      (acproof-to-pruned-proof op) arg))))
      ((proof-in-allnc-intro-form)
       (let* ((var (proof-in-allnc-intro-form-to-var acproof))
	      (kernel (proof-in-allnc-intro-form-to-kernel acproof))
	      (proof-of-formula-or-f (prune-aux formula '() kernel)))
	 (if proof-of-formula-or-f
	     (acproof-to-pruned-proof proof-of-formula-or-f)
	     (make-proof-in-allnc-intro-form
	      var (acproof-to-pruned-proof kernel)))))
      ((proof-in-allnc-elim-form)
       (let* ((op (proof-in-allnc-elim-form-to-op acproof))
	      (arg (proof-in-allnc-elim-form-to-arg acproof))
	      (proof-of-formula-or-f (prune-aux formula '() op)))
	 (if proof-of-formula-or-f
	     (acproof-to-pruned-proof proof-of-formula-or-f)
	     (make-proof-in-allnc-elim-form
	      (acproof-to-pruned-proof op) arg))))
      (else (myerror "acproof-to-pruned-proof"
		     "proof tag expected"
		     (tag proof))))))

;; prune-aux returns #f or the shorter acproof of formula

(define (prune-aux formula bound-avars acproof)
  (if
   (and
    (classical-formula=? formula (proof-to-formula acproof))
    (null? (intersection-wrt avar=? bound-avars (proof-to-context acproof))))
   acproof
   (case (tag acproof)
     ((proof-in-avar-form proof-in-aconst-form) #f)
     ((proof-in-imp-intro-form)
      (let ((avar (proof-in-imp-intro-form-to-avar acproof))
	    (kernel (proof-in-imp-intro-form-to-kernel acproof)))
	(prune-aux formula (adjoin-wrt avar=? avar bound-avars) kernel)))
     ((proof-in-imp-elim-form)
      (let ((op (proof-in-imp-elim-form-to-op acproof))
	    (arg (proof-in-imp-elim-form-to-arg acproof)))
	(or (prune-aux formula bound-avars op)
	    (prune-aux formula bound-avars arg))))
     ((proof-in-impnc-intro-form)
      (let ((avar (proof-in-impnc-intro-form-to-avar acproof))
	    (kernel (proof-in-impnc-intro-form-to-kernel acproof)))
	(prune-aux formula (adjoin-wrt avar=? avar bound-avars) kernel)))
     ((proof-in-impnc-elim-form)
      (let ((op (proof-in-impnc-elim-form-to-op acproof))
	    (arg (proof-in-impnc-elim-form-to-arg acproof)))
	(or (prune-aux formula bound-avars op)
	    (prune-aux formula bound-avars arg))))
     ((proof-in-and-intro-form)
      (let ((left (proof-in-and-intro-form-to-left acproof))
	    (right (proof-in-and-intro-form-to-right acproof)))
	(or (prune-aux formula bound-avars left)
	    (prune-aux formula bound-avars right))))
     ((proof-in-and-elim-left-form)
      (let ((kernel (proof-in-and-elim-left-form-to-kernel acproof)))
	(prune-aux formula bound-avars kernel)))
     ((proof-in-and-elim-right-form)
      (let ((kernel (proof-in-and-elim-right-form-to-kernel acproof)))
	(prune-aux formula bound-avars kernel)))
     ((proof-in-all-intro-form)
      (let ((kernel (proof-in-all-intro-form-to-kernel acproof)))
	(prune-aux formula bound-avars kernel)))
     ((proof-in-all-elim-form)
      (let ((op (proof-in-all-elim-form-to-op acproof)))
	(prune-aux formula bound-avars op)))
     ((proof-in-allnc-intro-form)
      (let ((kernel (proof-in-allnc-intro-form-to-kernel acproof)))
	(prune-aux formula bound-avars kernel)))
     ((proof-in-allnc-elim-form)
      (let ((op (proof-in-allnc-elim-form-to-op acproof)))
	(prune-aux formula bound-avars op)))
     (else (myerror "prune-aux" "proof tag expected" (tag acproof))))))

;; For tests it might generally be useful to have a level-wise
;; decomposition of proofs into subproofs: one level transforms a proof
;; lambda us.v Ms into the list [v M1 ... Mn]

(define (proof-in-intro-form-to-final-kernels proof)
  (cond
   ((proof-in-imp-intro-form? proof)
    (proof-in-intro-form-to-final-kernels
     (proof-in-imp-intro-form-to-kernel proof)))
   ((proof-in-impnc-intro-form? proof)
    (proof-in-intro-form-to-final-kernels
     (proof-in-impnc-intro-form-to-kernel proof)))
   ((proof-in-and-intro-form? proof)
    (append (proof-in-intro-form-to-final-kernels
	     (proof-in-and-intro-form-to-left proof))
	    (proof-in-intro-form-to-final-kernels
	     (proof-in-and-intro-form-to-right proof))))
   ((proof-in-all-intro-form? proof)
    (proof-in-intro-form-to-final-kernels
     (proof-in-all-intro-form-to-kernel proof)))
   ((proof-in-allnc-intro-form? proof)
    (proof-in-intro-form-to-final-kernels
     (proof-in-allnc-intro-form-to-kernel proof)))
   (else (list proof))))

(define (proof-in-elim-form-to-final-op-and-args proof)
  (case (tag proof)
    ((proof-in-imp-elim-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-imp-elim-form-to-op proof))
	     (proof-in-imp-elim-form-to-arg proof)))
    ((proof-in-impnc-elim-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-impnc-elim-form-to-op proof))
	     (proof-in-impnc-elim-form-to-arg proof)))
    ((proof-in-and-elim-left-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-and-elim-left-form-to-kernel proof))
	     (list 'left)))
    ((proof-in-and-elim-right-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-and-elim-right-form-to-kernel proof))
	     (list 'right)))
    ((proof-in-all-elim-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-all-elim-form-to-op proof))
	     (proof-in-all-elim-form-to-arg proof)))
    ((proof-in-allnc-elim-form)
     (append (proof-in-elim-form-to-final-op-and-args
	      (proof-in-allnc-elim-form-to-op proof))
	     (proof-in-allnc-elim-form-to-arg proof)))
    (else (list proof))))

(define (proof-to-parts-of-level-one proof)
  (let* ((final-kernels (proof-in-intro-form-to-final-kernels proof))
	 (lists (map proof-in-elim-form-to-final-op-and-args final-kernels)))
    (apply append lists)))

(define (proof-to-parts proof . opt-level)
  (if
   (null? opt-level)
   (proof-to-parts-of-level-one proof)
   (let ((l (car opt-level)))
     (if (and (integer? l) (not (negative? l)))
	 (if (zero? l)
	     (list proof)
	     (let* ((parts (proof-to-parts-of-level-one proof))
		    (proofs (list-transform-positive parts
			      proof-form?)))
	       (apply append (map (lambda (x) (proof-to-parts x (- l 1)))
				  proofs))))
   	 (myerror "proof-to-parts" "non-negative integer expected" l)))))

(define (proof-to-proof-parts proof)
  (list-transform-positive (proof-to-parts proof)
    proof-form?))

(define (proof-to-depth proof)
  (if
   (or (proof-in-avar-form? proof)
       (proof-in-aconst-form? proof))
   0
   (let* ((final-kernels (proof-in-intro-form-to-final-kernels proof))
	  (lists (map proof-in-elim-form-to-final-op-and-args final-kernels))
	  (proofs (list-transform-positive (apply append lists) proof-form?)))
     (+ 1 (apply max (map proof-to-depth proofs))))))

;; Hand normalization of proofs, including beta conversion and
;; idpredconst-elim-intro conversion.  The latter uses for nested
;; idpredconstants formula-and-psubsts-to-mon-proof.  An elim-intro
;; redex occurs when an elim aconst is applied to terms and the result
;; of applying an intro-aconst to terms and an idpc-proof.

(define (proof-in-idpredconst-elim-intro-redex-form? proof)
  (let* ((op (proof-in-elim-form-to-final-op proof))
	 (args (proof-in-elim-form-to-args proof))
	 (proof-args (list-transform-positive args proof-form?)))
    (and
     (proof-in-aconst-form? op)
     (string=? (aconst-to-name (proof-in-aconst-form-to-aconst op)) "Elim")
     (pair? proof-args)
     (let ((arg-op (proof-in-elim-form-to-final-op (car proof-args))))
       (and
	(proof-in-aconst-form? arg-op)
	(string=?  (aconst-to-name (proof-in-aconst-form-to-aconst arg-op))
		   "Intro"))))))

(define (proof-to-one-step-idpredconst-elim-intro-reduct proof)
  (let* ((op (proof-in-elim-form-to-final-op proof))
	 (args (proof-in-elim-form-to-args proof))
	 (elim-aconst (proof-in-aconst-form-to-aconst op))
	 (inst-formula (aconst-to-inst-formula elim-aconst))
	 (free (formula-to-free inst-formula))
	 (f (length free))
	 (terms (list-head args f))
	 (intro-proof (car (list-tail args f)))
	 (s-plus-1 (length (imp-impnc-form-to-premises
			    (aconst-to-uninst-formula elim-aconst))))
	 (step-proofs (list-head (cdr (list-tail args f)) (- s-plus-1 1)))
	 (intro-op (proof-in-elim-form-to-final-op intro-proof))
	 (intro-args (proof-in-elim-form-to-args intro-proof))
	 (intro-aconst (proof-in-aconst-form-to-aconst intro-op))
	 (repro-data (aconst-to-repro-data intro-aconst))
	 (i (car repro-data))
	 (idpc (cadr repro-data))
	 (idpc-params (idpredconst-to-free idpc))
	 (intro-args-wo-idpc-params (list-tail intro-args (length idpc-params)))
	 (step-proof (list-ref step-proofs i))
	 (idpc-name (idpredconst-to-name idpc))
	 (simidpc-names (idpredconst-name-to-simidpc-names idpc-name))
	 (orig-simidpc-pvars (map idpredconst-name-to-pvar simidpc-names))
	 (orig-clauses (idpredconst-name-to-clauses idpc-name))
	 (orig-clause (list-ref orig-clauses i))
	 (types (idpredconst-to-types idpc))
	 (tsubst (idpredconst-name-and-types-to-tsubst idpc-name types))
	 (orig-param-pvars (idpredconst-name-to-param-pvars idpc-name))
	 (tsubst-param-pvars
	  (map (lambda (orig-param-pvar)
	 	 (let* ((arity (predicate-to-arity orig-param-pvar))
	 		(subst-arity
	 		 (apply make-arity
	 			(map (lambda (type)
	 			       (type-substitute type tsubst))
	 			     (arity-to-types arity)))))
	 	   (arity-to-new-general-pvar subst-arity)))
	       orig-param-pvars))
	 (orig-simidpc-pvars (map idpredconst-name-to-pvar simidpc-names))
	 (tsubst-simidpc-pvars
	  (map (lambda (orig-simidpc-pvar)
	 	 (let* ((arity (predicate-to-arity orig-simidpc-pvar))
	 		(subst-arity
	 		 (apply make-arity
	 			(map (lambda (type)
	 			       (type-substitute type tsubst))
	 			     (arity-to-types arity)))))
	 	   (arity-to-new-general-pvar subst-arity)))
	       orig-simidpc-pvars))
	 (tsubst-clause
	  (rename-variables ;ensures that all bound variables are distinct
	   (formula-substitute
	    orig-clause
	    (append tsubst
		    (make-substitution-wrt
		     pvar-cterm-equal?
		     (append orig-param-pvars orig-simidpc-pvars)
		     (map predicate-to-cterm
			  (append tsubst-param-pvars tsubst-simidpc-pvars)))))))
	 (tsubst-vars-and-prems (imp-impnc-all-allnc-form-to-vars-and-premises
				 tsubst-clause))
	 (step-arg-lists ;of 1 or 2 elements
	  (map
	   (lambda (intro-arg tsubst-var-or-prem)
	     (cond
	      (;param-arg: take original arg
	       (or (term-form? intro-arg)
		   (null? (intersection (formula-to-idpredconst-names
					 (proof-to-formula intro-arg))
					simidpc-names)))
	       (list intro-arg))
	      (;unnested prem: take orig arg and rec call (duplication)
	       (and (predicate-form? (proof-to-formula intro-arg))
		    (let ((pred (predicate-form-to-predicate
				 (proof-to-formula intro-arg))))
		      (and (idpredconst-form? pred)
			   (member (idpredconst-to-name pred) simidpc-names))))
	       (list intro-arg ;now the rec call
		     (apply mk-proof-in-elim-form
			    (make-proof-in-aconst-form elim-aconst)
			    (append terms (cons intro-arg step-proofs)))))
	      (else ;nested case.  Use formula-and-psubsts-to-mon-proof
	       (let* ((tsubst-idpc-pvar (list-ref tsubst-simidpc-pvars i))
		      (simidpc-name (list-ref simidpc-names i))
		      (simidpc (make-idpredconst
				simidpc-name types tsubst-param-pvars))
		      (simidpc-cterm (predicate-to-cterm simidpc))
		      (psubst1 (make-subst-wrt
				pvar-cterm-equal?
				tsubst-idpc-pvar simidpc-cterm))
		      (idpc-formula (imp-form-to-premise inst-formula))
		      (concl (imp-form-to-final-conclusion inst-formula))
		      (idpc-argvars (map term-in-var-form-to-var
					 (predicate-form-to-args idpc-formula)))
		      (conj (make-andd idpc-formula concl))
		      (conj-idpc (predicate-form-to-predicate conj))
		      (conj-cterm (apply make-cterm
					 (append idpc-argvars (list conj))))
		      (psubst2 (make-subst-wrt
				pvar-cterm-equal?
				tsubst-idpc-pvar conj-cterm))
		      (subst (make-substitution-wrt
			      var-term-equal?
			      (imp-impnc-all-allnc-form-to-vars tsubst-clause)
			      (list-transform-positive intro-args-wo-idpc-params
				term-form?)))
		      (mon-formula (formula-substitute
				    tsubst-var-or-prem subst))
		      (mon-proof (formula-and-psubsts-to-mon-proof
				  mon-formula psubst1 psubst2))
		      (u (formula-to-new-avar idpc-formula))
		      (conj-intro-aconst
		       (number-and-idpredconst-to-intro-aconst 0 conj-idpc))
		      (conj-sub-proof
		       (apply
			mk-proof-in-nc-intro-form
			(append
			 idpc-argvars
			 (list
			  (make-proof-in-imp-intro-form
			   u (apply
			      mk-proof-in-elim-form
			      (make-proof-in-aconst-form conj-intro-aconst)
			      (append
			       (map make-term-in-var-form free)
			       (list (make-proof-in-avar-form u)
				     (apply
				      mk-proof-in-elim-form
				      (make-proof-in-aconst-form elim-aconst)
				      (append
				       (map make-term-in-var-form free)
				       (list (make-proof-in-avar-form u))
				       step-proofs)))))))))))
		 (list (mk-proof-in-elim-form
			mon-proof intro-arg conj-sub-proof))))))
	   intro-args-wo-idpc-params tsubst-vars-and-prems))
	 (step-args (apply append step-arg-lists)))
    (apply mk-proof-in-elim-form
	   step-proof step-args)))

;; We define a procedure taking a formula A(Xs) and psubsts Xs -> Ps
;; and Xs -> Qs for the same list Xs of pvars which occur at most
;; strictly positive in A(Xs).  It returns a proof of monotonicity
;; A(Ps) -> (allnc xs(P_i xs -> Q_i xs))_i -> A(Qs).

(define (formula-and-psubsts-to-mon-proof formula psubst1 psubst2)
  (let* ((pvars (map car psubst1)) ;Xs
	 (arities (map pvar-to-arity pvars))
	 (type-lists (map arity-to-types arities))
	 (var-lists (map (lambda (types)
			   (map type-to-new-partial-var types))
			 type-lists))
	 (varterm-lists (map (lambda (vars)
			       (map make-term-in-var-form vars))
			     var-lists))
	 (prems ;P xs
	  (map (lambda (pvar varterms)
		 (let* ((cterm (cadr (assoc pvar psubst1)))
			(cterm-vars (cterm-to-vars cterm))
			(cterm-fla (cterm-to-formula cterm))
			(subst (make-substitution-wrt
				var-term-equal? cterm-vars varterms)))
		   (formula-substitute cterm-fla subst)))
	       pvars varterm-lists))
	 (concls ;Q xs
	  (map (lambda (pvar varterms)
		 (let* ((cterm (cadr (assoc pvar psubst2)))
			(cterm-vars (cterm-to-vars cterm))
			(cterm-fla (cterm-to-formula cterm))
			(subst (make-substitution-wrt
				var-term-equal? cterm-vars varterms)))
		   (formula-substitute cterm-fla subst)))
	       pvars varterm-lists))
	 (imps (map make-imp prems concls))
	 (sub-formulas ;allnc xs(P xs -> Q xs)
	  (map (lambda (vars imp)
		 (rename-variables
		  (apply mk-allnc (append vars (list imp)))))
	       var-lists imps))
	 (sub-free ;FV(Ps sub Qs)
	  (apply union (map formula-to-free sub-formulas)))
	 (u (formula-to-new-avar (formula-substitute formula psubst1)))
	 (vs (map formula-to-new-avar sub-formulas))
	 (pvar-v-alist (map list pvars vs)))
    (cond
     ((or (null? (intersection pvars (formula-to-pvars formula)))
	  (atom-form? formula))
      (apply mk-proof-in-intro-form
	     u (append vs (list (make-proof-in-avar-form u)))))
     ((predicate-form? formula)
      (let ((pred (predicate-form-to-predicate formula))
	    (args (predicate-form-to-args formula)))
	(cond
	 ((pvar-form? pred)
	  (if
	   (member pred pvars)
	   (let* ((v (cadr (assoc pred pvar-v-alist)))
		  (elim-proof
		   (apply mk-proof-in-elim-form
			  (make-proof-in-avar-form v)
			  (append args (list (make-proof-in-avar-form u))))))
	     (apply mk-proof-in-intro-form u (append vs (list elim-proof))))
	   (apply mk-proof-in-intro-form
		  u (append vs (list (make-proof-in-avar-form u))))))
	 ((predconst-form? pred)
	  (apply mk-proof-in-intro-form
		 u (append vs (list (make-proof-in-avar-form u)))))
	 ((idpredconst-form? pred) ;I_{Rs(Xs)}
	  (let*
	      ((vars (map type-to-new-partial-var (map term-to-type args))) ;zs
	       (varterms (map make-term-in-var-form vars))
	       (idpc-name (idpredconst-to-name pred))
	       (types (idpredconst-to-types pred))
	       (tsubst (idpredconst-name-and-types-to-tsubst idpc-name types))
	       (cterms (idpredconst-to-cterms pred)) ;Rs(Xs)
	       (cterm-clashs
		(map (lambda (cterm)
		       (pair? (intersection sub-free (cterm-to-vars cterm))))
		     cterms))
	       (new-cterm-var-lists
		(map (lambda (cterm cterm-clash)
		       (if cterm-clash
			   (map var-to-new-var (cterm-to-vars cterm))
			   (cterm-to-vars cterm)))
		     cterms cterm-clashs))
	       (new-cterm-flas ;R(Xs)ys
		(map (lambda (cterm cterm-clash new-cterm-vars)
		       (if cterm-clash
			   (formula-substitute
			    (cterm-to-formula cterm)
			    (make-substitution
			     cterm-vars
			     (map make-term-in-var-form new-cterm-vars)))
			   (cterm-to-formula cterm)))
		     cterms cterm-clashs new-cterm-var-lists))
	       (ih-mon-proofs ;of R(Ps)ys -> (Ps sub Qs) -> R(Qs)ys
		(map (lambda (fla)
		       (formula-and-psubsts-to-mon-proof fla psubst1 psubst2))
		     new-cterm-flas))
	       (cterm1-flas ;list of R(Ps)ys
		(map (lambda (proof)
		       (imp-form-to-premise (proof-to-formula proof)))
		     ih-mon-proofs))
	       (avars (map formula-to-new-avar cterm1-flas))
	       (ih-sub-proofs ;of allnc ys(R(Ps)ys -> R(Qs)ys)
		(map (lambda (new-cterm-vars avar ih-mon-proof)
		       (apply
			mk-proof-in-nc-intro-form
			(append
			 new-cterm-vars
			 (list (make-proof-in-imp-intro-form
				avar
				(apply mk-proof-in-elim-form
				       ih-mon-proof
				       (make-proof-in-avar-form avar)
				       (map make-proof-in-avar-form vs)))))))
		     new-cterm-var-lists avars ih-mon-proofs))
	       (cterm-params
		 (apply union (map formula-to-free
				   (map proof-to-formula ih-sub-proofs))))
	       (cterm2-flas ;list of R(Qs)ys
		(map (lambda (proof)
		       (imp-form-to-conclusion
			(all-allnc-form-to-final-kernel
			 (proof-to-formula proof))))
		     ih-sub-proofs))
	       (cterms1 ;list of R(Ps)
		(map (lambda (new-cterm-vars cterm1-fla)
		       (apply make-cterm
			      (append new-cterm-vars (list cterm1-fla))))
		     new-cterm-var-lists cterm1-flas))
	       (cterms2 ;list of R(Qs)
		(map (lambda (new-cterm-vars cterm2-fla)
		       (apply make-cterm
			      (append new-cterm-vars (list cterm2-fla))))
		     new-cterm-var-lists cterm2-flas))
	       (orig-param-pvars (idpredconst-name-to-param-pvars idpc-name))
	       (param-pvars
		(map (lambda (orig-param-pvar)
		       (let* ((arity (predicate-to-arity orig-param-pvar))
			      (subst-arity
			       (apply make-arity
				      (map (lambda (type)
					     (type-substitute type tsubst))
					   (arity-to-types arity)))))
			 (arity-to-new-general-pvar subst-arity)))
		     orig-param-pvars))
	       (param-psubst1 (make-substitution-wrt
			       pvar-cterm-equal? param-pvars cterms1))
	       (param-psubst2 (make-substitution-wrt
			       pvar-cterm-equal? param-pvars cterms2))
	       (prem ;I_{Rs(Ps)}zs
		(apply make-predicate-formula
		       (make-idpredconst idpc-name types cterms1) varterms))
	       (concl ;I_{Rs(Qs)}zs
		(apply make-predicate-formula
		       (make-idpredconst idpc-name types cterms2) varterms))
	       (imp-formula (make-imp prem concl))
	       (elim-aconst (imp-formulas-to-elim-aconst imp-formula))
	       (simidpc-names (idpredconst-name-to-simidpc-names idpc-name))
	       (orig-simidpc-pvars (map idpredconst-name-to-pvar simidpc-names))
	       (simidpc-pvars
		(map (lambda (orig-simidpc-pvar)
		       (let* ((arity (predicate-to-arity orig-simidpc-pvar))
			      (subst-arity
			       (apply make-arity
				      (map (lambda (type)
					     (type-substitute type tsubst))
					   (arity-to-types arity)))))
			 (arity-to-new-general-pvar subst-arity)))
		     orig-simidpc-pvars))
	       (tpsubst ;needed to apply tsubst to orig-clauses
		(append tsubst
			(make-substitution-wrt
			 pvar-cterm-equal?
			 (append orig-param-pvars orig-simidpc-pvars)
			 (map predicate-to-cterm
			      (append param-pvars simidpc-pvars)))))
	       (concl-idpc (predicate-form-to-predicate concl)) ;I_{Rs(Qs)}
	       (step-proofs
		(apply
		 append
		 (map
		  (lambda (simidpc-name simidpc-pvar)
		    (map
		     (lambda (clause i)
		       (let*
			   ((intro-aconst
			     (number-and-idpredconst-to-intro-aconst
			      i concl-idpc))
			    (vars-and-prems-with-nc-indicator
			     (imp-impnc-all-allnc-form-to-vars-and-prems-with-nc-indicator
			      clause))
			    (vars-and-prems
			     (list-transform-positive
				 vars-and-prems-with-nc-indicator
			       (lambda (x)
				 (or (var-form? x) (formula-form? x)))))
			    (conj (make-andd prem concl))
			    (conj-cterm ;{zs|I_{Rs(Ps)}zs andd I_{Rs(Qs)}zs}
			     (apply make-cterm
				    (append vars (list conj))))
			    (prem-cterm
			     (apply make-cterm (append vars (list prem))))
			    (concl-cterm
			     (apply make-cterm (append vars (list concl))))
			    (ih-prem-psubst1
			     (append param-psubst1
				     (list (list simidpc-pvar conj-cterm))))
			    (ih-prem-psubst2
			     (append param-psubst2
				     (list (list simidpc-pvar concl-cterm))))
			    (ih-prem-psubst0
			     (append param-psubst2
				     (list (list simidpc-pvar prem-cterm))))
			    (vars-and-prem-avar-lists-with-nc-indicators
			     (map
			      (lambda (var-or-prem-or-nc-indicator)
				(cond
				 ((var-form? var-or-prem-or-nc-indicator)
				  var-or-prem-or-nc-indicator)
				 ((formula-form? var-or-prem-or-nc-indicator)
				  (if ;duplication
				   (and
				    (predicate-form?
				     (imp-impnc-all-allnc-form-to-final-conclusion
				      var-or-prem-or-nc-indicator))
				    (equal?
				     (predicate-form-to-predicate
				      (imp-impnc-all-allnc-form-to-final-conclusion
				      var-or-prem-or-nc-indicator))
				     simidpc-pvar))
				   (list
				    (formula-to-new-avar
				     (formula-substitute
				      var-or-prem-or-nc-indicator
				      ih-prem-psubst0))
				    (formula-to-new-avar
				     (formula-substitute
				      var-or-prem-or-nc-indicator
				      ih-prem-psubst2)))
					;else no duplication
				   (list
				    (formula-to-new-avar
				     (formula-substitute
				      var-or-prem-or-nc-indicator
				      ih-prem-psubst1)))))
				 (else var-or-prem-or-nc-indicator)))
			      vars-and-prems-with-nc-indicator))
			    (vars-and-prem-avars-with-nc-indicators
			     (apply
			      append
			      (map
			       (lambda (x)
				 (cond
				  ((and (list? x)
					(avar-form? (car x))
					(= 1 (length x)))
				   x)
				  ((and (list? x)
					(avar-form? (car x))
					(= 2 (length x)))
				   (list (car x) #f (cadr x)))
				  (else (list x))))
			       vars-and-prem-avar-lists-with-nc-indicators)))
			    (vars-and-prem-avar-lists
			     (list-transform-positive
				 vars-and-prem-avar-lists-with-nc-indicators
			       (lambda (x)
				 (or (var-form? x)
				     (and (pair? x) (avar-form? (car x)))))))
			    (varterms-and-premproofs
			     (map
			      (lambda (var-or-prem var-or-prem-avar-list)
				(cond
				 ((var-form? var-or-prem)
				  (make-term-in-var-form var-or-prem))
				 (;duplication
				  (= 2 (length var-or-prem-avar-list))
				  (let
				      ((ih-prem-proof
					(formula-and-psubsts-to-mon-proof
					 (formula-subst
					  var-or-prem simidpc-pvar concl-cterm)
					 param-psubst1 param-psubst2)))
				    (apply mk-proof-in-elim-form
					   ih-prem-proof
					   (make-proof-in-avar-form
					    (cadr var-or-prem-avar-list))
					   ih-sub-proofs)))
				 (;no duplication
				  (= 1 (length var-or-prem-avar-list))
				  (let*
				      ((ih-prem-proof
					(formula-and-psubsts-to-mon-proof
					 var-or-prem
					 ih-prem-psubst1 ih-prem-psubst2))
				       (conj-sub-proof
					(let* ((u3 (formula-to-new-avar conj)))
					  (apply
					   mk-proof-in-nc-intro-form
					   (append
					    vars
					    (list
					     (make-proof-in-imp-intro-form
					      u3
					      (make-proof-in-andd-elim-right-form
					       (make-proof-in-avar-form
						u3)))))))))
				    (apply mk-proof-in-elim-form
					   ih-prem-proof
					   (make-proof-in-avar-form
					    (car var-or-prem-avar-list))
					   (append ih-sub-proofs
						   (list conj-sub-proof)))))
				 (else
				  (myerror "formula-and-psubsts-to-mon-proof"
					   "list of length 1 or 2 expected"
					   var-or-prem-avar-list))))
			      vars-and-prems vars-and-prem-avar-lists)))
			 (apply
			  mk-proof-in-cr-nc-intro-form
			  (append
			   vars-and-prem-avars-with-nc-indicators
			   (list
			    (apply mk-proof-in-elim-form
				   (make-proof-in-aconst-form intro-aconst)
				   (append
				    (map make-term-in-var-form
					 (formula-to-free
					  (aconst-to-inst-formula
					   intro-aconst)))
				    varterms-and-premproofs)))))))
		     (map (lambda (clause)
			    (formula-substitute clause tpsubst))
			  (idpredconst-name-to-clauses simidpc-name))
		     (list-tabulate
		      (length (idpredconst-name-to-clauses simidpc-name))
		      (lambda (x) x))))
		  simidpc-names simidpc-pvars)))
	       (elim-proof ;of I_{Rs(Qs)} rs
		(apply
		 mk-proof-in-elim-form
		 (make-proof-in-aconst-form elim-aconst)
		 (append
		  args (map make-term-in-var-form cterm-params)
		  (list (make-proof-in-avar-form u))
		  step-proofs))))
	    (apply mk-proof-in-intro-form u (append vs (list elim-proof)))))
	 (else (myerror "formula-and-psubsts-to-mon-proof"
			"predicate expected" pred)))))
     ((imp-impnc-form? formula)
      (let ((w (formula-to-new-avar (imp-impnc-form-to-premise formula)))
	    (ih-proof (formula-and-psubsts-to-mon-proof
		       (imp-impnc-form-to-conclusion formula) psubst1 psubst2)))
	(apply mk-proof-in-intro-form
	       u (append
		  vs (list ((if (imp-form? formula)
				make-proof-in-imp-intro-form
				make-proof-in-impnc-intro-form)
			    w (apply mk-proof-in-elim-form
				     ih-proof
				     (mk-proof-in-elim-form
				      (make-proof-in-avar-form u)
				      (make-proof-in-avar-form w))
				     (map make-proof-in-avar-form vs))))))))
     ((and-form? formula)
      (let ((ih-proof1 (formula-and-psubsts-to-mon-proof
			(and-form-to-left formula) psubst1 psubst2))
	    (ih-proof2 (formula-and-psubsts-to-mon-proof
			(and-form-to-right formula) psubst1 psubst2)))
	(apply mk-proof-in-intro-form
	       u (append
		  vs (list (make-proof-in-and-intro-form
			    (apply mk-proof-in-elim-form
				   ih-proof1
				   (make-proof-in-and-elim-left-form
				    (make-proof-in-avar-form u))
				   (map make-proof-in-avar-form vs))
			    (apply mk-proof-in-elim-form
				   ih-proof2
				   (make-proof-in-and-elim-right-form
				    (make-proof-in-avar-form u))
				   (map make-proof-in-avar-form vs))))))))
     ((all-allnc-form? formula)
      (let* ((var (all-allnc-form-to-var formula))
	     (kernel (all-allnc-form-to-kernel formula))
	     (new-var (if (member var sub-free) (var-to-new-var var) var))
	     (new-kernel
	      (if (member var sub-free)
		  (formula-subst kernel var (make-term-in-var-form new-var))
		  kernel))
	     (ih-proof (formula-and-psubsts-to-mon-proof
			new-kernel psubst1 psubst2)))
	(apply mk-proof-in-intro-form
	       u (append
		  vs (list ((if (all-form? formula)
				make-proof-in-all-intro-form
				make-proof-in-allnc-intro-form)
			    new-var
			    (apply mk-proof-in-elim-form
				   ih-proof
				   (mk-proof-in-elim-form
				    (make-proof-in-avar-form u)
				    (make-term-in-var-form new-var))
				   (map make-proof-in-avar-form vs))))))))
     ((ex-form? formula)
      (let* ((var (ex-form-to-var formula))
	     (kernel (ex-form-to-kernel formula))
	     (new-var (if (member var sub-free) (var-to-new-var var) var))
	     (new-kernel
	      (if (member var sub-free)
		  (formula-subst kernel var (make-term-in-var-form new-var))
		  kernel))
	     (ih-proof (formula-and-psubsts-to-mon-proof
			new-kernel psubst1 psubst2))
	     (ih-fla (proof-to-formula ih-proof))
	     (ex-prem (make-ex new-var (imp-form-to-premise ih-fla)))
	     (v (formula-to-new-avar (imp-form-to-premise ih-fla)))
	     (ex-concl (make-ex new-var (imp-form-to-final-conclusion
					 ih-fla (+ 1 (length vs)))))
	     (ex-elim-aconst
	      (ex-formula-and-concl-to-ex-elim-aconst ex-prem ex-concl))
	     (free (union (formula-to-free ex-prem) (formula-to-free ex-concl)))
	     (free-terms (map make-term-in-var-form free)))
	(apply
	 mk-proof-in-intro-form
	 u (append
	    vs (list (apply
		      mk-proof-in-elim-form
		      (make-proof-in-aconst-form ex-elim-aconst)
		      (append
		       free-terms
		       (list (make-proof-in-avar-form u)
			     (apply
			      mk-proof-in-intro-form
			      new-var v
			      (list
			       (make-proof-in-ex-intro-form
				(make-term-in-var-form new-var)
				ex-concl
				(apply mk-proof-in-elim-form
				       ih-proof (map make-proof-in-avar-form
						     (cons v vs))))))))))))))
     (else (myerror "formula-and-psubsts-to-mon-proof"
		    "formula expected" formula)))))

(define (proof-to-one-step-reduct proof)
  (case (tag proof)
    ((proof-in-avar-form proof-in-aconst-form) proof)
    ((proof-in-imp-intro-form)
     (make-proof-in-imp-intro-form
      (proof-in-imp-intro-form-to-avar proof)
      (proof-to-one-step-reduct
       (proof-in-imp-intro-form-to-kernel proof))))
    ((proof-in-imp-elim-form)
     (if (proof-in-idpredconst-elim-intro-redex-form? proof)
	 (proof-to-one-step-idpredconst-elim-intro-reduct proof)
	 (let ((op (proof-in-imp-elim-form-to-op proof))
	       (arg (proof-in-imp-elim-form-to-arg proof)))
	   (if (proof-in-imp-intro-form? op)
	       (proof-subst (proof-in-imp-intro-form-to-kernel op)
			    (proof-in-imp-intro-form-to-avar op)
			    arg)
	       (make-proof-in-imp-elim-form
		(proof-to-one-step-reduct op)
		(proof-to-one-step-reduct arg))))))
    ((proof-in-impnc-intro-form)
     (make-proof-in-impnc-intro-form
      (proof-in-impnc-intro-form-to-avar proof)
      (proof-to-one-step-reduct
       (proof-in-impnc-intro-form-to-kernel proof))))
    ((proof-in-impnc-elim-form)
     (let ((op (proof-in-impnc-elim-form-to-op proof))
	   (arg (proof-in-impnc-elim-form-to-arg proof)))
       (if (proof-in-impnc-intro-form? op)
	   (proof-subst (proof-in-impnc-intro-form-to-kernel op)
			(proof-in-impnc-intro-form-to-avar op)
			arg)
	   (make-proof-in-impnc-elim-form
	    (proof-to-one-step-reduct op)
	    (proof-to-one-step-reduct arg)))))
    ((proof-in-and-intro-form)
     (make-proof-in-and-intro-form
      (proof-to-one-step-reduct (proof-in-and-intro-form-to-left proof))
      (proof-to-one-step-reduct
       (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (if (proof-in-and-intro-form? kernel)
	   (proof-in-and-intro-form-to-left kernel)
	   (make-proof-in-and-elim-left-form
	    (proof-to-one-step-reduct kernel)))))
    ((proof-in-and-elim-right-form)
     (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (if (proof-in-and-intro-form? kernel)
	   (proof-in-and-intro-form-to-right kernel)
	   (make-proof-in-and-elim-right-form
	    (proof-to-one-step-reduct kernel)))))
    ((proof-in-all-intro-form)
     (make-proof-in-all-intro-form
      (proof-in-all-intro-form-to-var proof)
      (proof-to-one-step-reduct
       (proof-in-all-intro-form-to-kernel proof))))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
       (if (proof-in-all-intro-form? op)
	   (proof-subst (proof-in-all-intro-form-to-kernel op)
			(proof-in-all-intro-form-to-var op)
			arg)
	   (make-proof-in-all-elim-form
	    (proof-to-one-step-reduct op)
	    arg))))
    ((proof-in-allnc-intro-form)
     (make-proof-in-allnc-intro-form
      (proof-in-allnc-intro-form-to-var proof)
      (proof-to-one-step-reduct
       (proof-in-allnc-intro-form-to-kernel proof))))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof))
	   (arg (proof-in-allnc-elim-form-to-arg proof)))
       (if (proof-in-allnc-intro-form? op)
	   (proof-subst (proof-in-allnc-intro-form-to-kernel op)
			(proof-in-allnc-intro-form-to-var op)
			arg)
	   (make-proof-in-allnc-elim-form
	    (proof-to-one-step-reduct op)
	    arg))))
    (else (myerror "proof-to-one-step-reduct" "proof tag expected"
		   (tag proof)))))

(define (proof-to-normal-form proof)
  (if (proof-in-normal-form? proof)
      proof
      (proof-to-normal-form (proof-to-one-step-reduct proof))))

;; Useful functions for proofs

(define (proof-to-length proof)
  (case (tag proof)
    ((proof-in-avar-form proof-in-aconst-form) 1)
    ((proof-in-imp-intro-form)
     (+ 1 (proof-to-length (proof-in-imp-intro-form-to-kernel proof))))
    ((proof-in-imp-elim-form)
     (let* ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof)))
       (+ 1 (proof-to-length op) (proof-to-length arg))))
    ((proof-in-impnc-intro-form)
     (+ 1 (proof-to-length (proof-in-impnc-intro-form-to-kernel proof))))
    ((proof-in-impnc-elim-form)
     (let* ((op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof)))
       (+ 1 (proof-to-length op) (proof-to-length arg))))
    ((proof-in-and-intro-form)
     (+ 1
	(proof-to-length (proof-in-and-intro-form-to-left proof))
	(proof-to-length (proof-in-and-intro-form-to-right proof))))
    ((proof-in-and-elim-left-form)
     (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (+ 1 (proof-to-length kernel))))
    ((proof-in-and-elim-right-form)
     (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (+ 1 (proof-to-length kernel))))
    ((proof-in-all-intro-form)
     (+ 1 (proof-to-length (proof-in-all-intro-form-to-kernel proof))))
    ((proof-in-all-elim-form)
     (let* ((op (proof-in-all-elim-form-to-op proof))
	    (arg (proof-in-all-elim-form-to-arg proof)))
       (+ 1 (proof-to-length op) 1)))
    ((proof-in-allnc-intro-form)
     (+ 1 (proof-to-length (proof-in-allnc-intro-form-to-kernel proof))))
    ((proof-in-allnc-elim-form)
     (let* ((op (proof-in-allnc-elim-form-to-op proof))
	    (arg (proof-in-allnc-elim-form-to-arg proof)))
       (+ 1 (proof-to-length op) 1)))
    (else (myerror "proof-to-length" "proof tag expected"
		   (tag proof)))))

;; 10-3. Substitution
;; ==================

;; We define simultaneous substitution for type, object, predicate and
;; assumption variables in a proof.

;; rename-bound-avars replaces all bound avars by new ones with the
;; same name but a new index.  Properties: (i) rename-bound-avars
;; transforms a proof satisfying the avar convention w.r.t. its free
;; avars into a proof satisfying the avar convention completely.  (ii)
;; In every subproof of the result no free avar occurs (w.r.t. avar=?)
;; bound as well.  Property (ii) is assumed in proof-substitute.

(define (rename-bound-avars proof)
  (rename-bound-avars-aux proof '()))

(define (rename-bound-avars-aux proof alist)
  (case (tag proof)
    ((proof-in-avar-form)
     (let* ((avar (proof-in-avar-form-to-avar proof))
	    (info (assoc-wrt avar-full=? avar alist)))
       (if info (cadr info) proof)))
    ((proof-in-aconst-form) proof)
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (formula (avar-to-formula avar))
	    (name (avar-to-name avar))
	    (new-avar (formula-to-new-avar formula name))
	    (new-alist (cons (list avar (make-proof-in-avar-form new-avar))
			     alist)))
       (make-proof-in-imp-intro-form
	new-avar (rename-bound-avars-aux kernel new-alist))))
    ((proof-in-imp-elim-form)
     (let ((op (proof-in-imp-elim-form-to-op proof))
	   (arg (proof-in-imp-elim-form-to-arg proof)))
       (make-proof-in-imp-elim-form
	(rename-bound-avars-aux op alist)
	(rename-bound-avars-aux arg alist))))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (formula (avar-to-formula avar))
	    (name (avar-to-name avar))
	    (new-avar (formula-to-new-avar formula name))
	    (new-alist (cons (list avar (make-proof-in-avar-form new-avar))
			     alist)))
       (make-proof-in-impnc-intro-form
	new-avar (rename-bound-avars-aux kernel new-alist))))
    ((proof-in-impnc-elim-form)
     (let ((op (proof-in-impnc-elim-form-to-op proof))
	   (arg (proof-in-impnc-elim-form-to-arg proof)))
       (make-proof-in-impnc-elim-form
	(rename-bound-avars-aux op alist)
	(rename-bound-avars-aux arg alist))))
    ((proof-in-and-intro-form)
     (make-proof-in-and-intro-form
      (rename-bound-avars-aux (proof-in-and-intro-form-to-left proof) alist)
      (rename-bound-avars-aux (proof-in-and-intro-form-to-right proof) alist)))
    ((proof-in-and-elim-left-form)
     (make-proof-in-and-elim-left-form
      (rename-bound-avars-aux
       (proof-in-and-elim-left-form-to-kernel proof) alist)))
    ((proof-in-and-elim-right-form)
     (make-proof-in-and-elim-right-form
      (rename-bound-avars-aux
       (proof-in-and-elim-right-form-to-kernel proof) alist)))
    ((proof-in-all-intro-form)
     (let ((var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-proof-in-all-intro-form
	var (rename-bound-avars-aux kernel alist))))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
       (make-proof-in-all-elim-form
	(rename-bound-avars-aux op alist) arg)))
    ((proof-in-allnc-intro-form)
     (let ((var (proof-in-allnc-intro-form-to-var proof))
	   (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-proof-in-allnc-intro-form
	var (rename-bound-avars-aux kernel alist))))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof))
	   (arg (proof-in-allnc-elim-form-to-arg proof)))
       (make-proof-in-allnc-elim-form
	(rename-bound-avars-aux op alist) arg)))
    (else (myerror "rename-bound-avars-aux" "proof tag expected"
		   (tag proof)))))

(define (aconst-substitute aconst topsubst . opt-ignore-deco-flag)
  (let* ((uninst-formula0 (aconst-to-uninst-formula aconst))
	 (tpsubst0 (aconst-to-tpsubst aconst))
	 (tsubst0 (list-transform-positive tpsubst0
		    (lambda (x) (tvar-form? (car x)))))
	 (psubst0 (list-transform-positive tpsubst0
		    (lambda (x) (pvar-form? (car x)))))
	 (repro-data0 (aconst-to-repro-data aconst))
	 (tvars0 (formula-to-tvars uninst-formula0))
	 (pvars0 (formula-to-pvars uninst-formula0))
	 (omitted-tvars (set-minus tvars0 (map car tsubst0)))
	 (omitted-pvars (set-minus pvars0 (map car psubst0)))
	 (completed-tsubst0
	  (append tsubst0 (map (lambda (tvar) (list tvar tvar))
			       omitted-tvars)))
	 (completed-psubst0
	  (append psubst0 (map (lambda (pvar)
				 (list pvar (predicate-to-cterm pvar)))
			       omitted-pvars)))
	 (tsubst (list-transform-positive topsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive topsubst
		   (lambda (x) (pvar-form? (car x)))))
	 (composed-tsubst (compose-substitutions completed-tsubst0 tsubst))
	 (reduced-composed-tsubst
	  (list-transform-positive composed-tsubst
	    (lambda (x) (and (not (equal? (car x) (cadr x)))
			     (member (car x) tvars0)))))
	 (pvars (formula-to-pvars (aconst-to-inst-formula aconst)))
	 (composed-psubst (map (lambda (x)
				 (let ((pvar (car x))
				       (cterm (cadr x)))
				   (list pvar
					 (cterm-substitute cterm topsubst))))
			       completed-psubst0))
	 (reduced-composed-psubst
	  (list-transform-positive composed-psubst
	    (lambda (x) (and (not (pvar-cterm-equal? (car x) (cadr x)))
			     (member (car x) pvars0)))))
	 (mr-extended-reduced-composed-psubst
	  (do ((ps reduced-composed-psubst (cdr ps))
	       (res
		'()
		(let* ((pair (car ps))
		       (pvar (car pair))
		       (cterm (cadr pair)))
		  (if (and (h-deg-one? (pvar-to-h-deg pvar))
			   (member pvar pvars)
			   (member (PVAR-TO-MR-PVAR pvar) pvars))
		      (let* ((info (assoc (PVAR-TO-MR-PVAR pvar) psubst))
			     (fla (cterm-to-formula cterm))
			     (type (formula-to-et-type fla))
			     (var (type-to-new-partial-var type))
			     (vars (cterm-to-vars cterm))
			     (varterm (make-term-in-var-form var))
			     (mr-fla (real-and-formula-to-mr-formula
				      varterm fla))
			     (mr-cterm
			      (apply make-cterm
				     var (append vars (list mr-fla)))))
			(if info
			    (if (cterm=? (cadr info) mr-cterm)
				(cons pair res)
				(myerror "aconst-substitute"
					 "equal mr-formulas expected"
					 (cterm-to-formula (cadr info))
					 mr-fla))
			    (cons (list (PVAR-TO-MR-PVAR pvar) mr-cterm)
				  (cons pair res))))
		      (cons pair res)))))
	      ((null? ps) (reverse res))))
	 (repro-data
	  (cond
	   ((string=? "Intro" (aconst-to-name aconst))
	    (let* ((i (car repro-data0))
		   (idpredconst (cadr repro-data0))
		   (name (idpredconst-to-name idpredconst))
		   (types (idpredconst-to-types idpredconst))
		   (cterms (idpredconst-to-cterms idpredconst))
		   (new-idpredconst
		    (make-idpredconst
		     name
		     (map (lambda (x) (type-substitute x tsubst)) types)
		     (map (lambda (x)
			    (cterm-substitute x (append tsubst psubst)))
			  cterms))))
	      (list i new-idpredconst)))
	   ((string=? "Closure" (aconst-to-name aconst))
	    (let* ((idpc (car repro-data0))
		   (name (idpredconst-to-name idpc))
		   (types (idpredconst-to-types idpc))
		   (cterms (idpredconst-to-cterms idpc))
		   (subst-types
		    (map (lambda (x) (type-substitute x tsubst)) types))
		   (subst-cterms
		    (map (lambda (x) (cterm-substitute x topsubst))
			 cterms))
		   (subst-idpredconst
		    (make-idpredconst name subst-types subst-cterms)))
	      (list subst-idpredconst)))
	   (else (map (lambda (x) (formula-substitute x topsubst))
		      repro-data0)))))
    (if (and
	 (or ;ignore-deco-flag is #f
	  (null? opt-ignore-deco-flag)
	  (and (pair? opt-ignore-deco-flag) (not (car opt-ignore-deco-flag))))
	 (string=? "Elim" (aconst-to-name aconst))
	 (let* ((fla (aconst-to-formula aconst))
		(kernel (all-allnc-form-to-final-kernel fla))
		(prems (imp-impnc-form-to-premises kernel))
		(concl (imp-impnc-form-to-final-conclusion kernel)))
	   (and
	    (formula-of-nulltype? (car prems)) ;n.c. idpredconst
	    (<= 3 (length prems)) ;with at least 2 clauses
	    (not (formula-of-nulltype? concl)))))
	(myerror
	 "aconst-substitute"
	 "In case ignore-deco-flag is #f, Elim for the n.c. idpredconst"
	 (car prems)
	 "with at least two clauses can be used for n.c. conclusions only"
	 concl))
    (apply make-aconst
	   (aconst-to-name aconst)
	   (aconst-to-kind aconst)
	   uninst-formula0
	   (append reduced-composed-tsubst
		   mr-extended-reduced-composed-psubst)
	   repro-data)))

;; In proof-substitute substitution of a pvar in an aconst can generate
;; new parameters, which will be generalized.  Hence the result must be
;; applied to their varterms.  Therefore substitution eta expands
;; aconsts such that they are applied to sufficiently many terms.
;; Recall that the Elim and Gfp aconsts are special in that their
;; uninst-formula may have free variables.

(define (proof-substitute proof topasubst . opt-ignore-deco-flag)
  (let* ((tsubst (list-transform-positive topasubst
		   (lambda (x) (tvar-form? (car x)))))
	 (tosubst (list-transform-positive topasubst
		    (lambda (x) (or (type-form? (car x))
				    (var-form? (car x))))))
	 (topsubst (list-transform-positive topasubst
		     (lambda (x) (or (type-form? (car x))
				     (var-form? (car x))
				     (pvar-form? (car x))))))
	 (asubst (list-transform-positive topasubst
		   (lambda (x) (avar-form? (car x))))))
    (case (tag proof)
      ((proof-in-avar-form)
       (let* ((avar (proof-in-avar-form-to-avar proof))
	      (info (assoc-wrt avar=? avar asubst)))
	 (if info
	     (cadr info)
	     (make-proof-in-avar-form avar))))
      ((proof-in-aconst-form proof-in-all-elim-form proof-in-allnc-elim-form)
       (let* ((op-and-args (proof-to-final-all-allnc-elim-op-and-args proof))
	      (op (car op-and-args))
	      (args (cdr op-and-args)))
	 (if
	  (not (proof-in-aconst-form? op))
	  (apply mk-proof-in-elim-form
		 (proof-substitute op topasubst opt-ignore-deco-flag)
		 (map (lambda (arg) (term-substitute arg topasubst))
		      args))
	  (let* ((aconst (proof-in-aconst-form-to-aconst op))
		 (inst-formula (aconst-to-inst-formula aconst))
		 (orig-tpsubst (aconst-to-tpsubst aconst))
		 (orig-tsubst (list-transform-positive orig-tpsubst
				   (lambda (x) (tvar-form? (car x)))))
		 (orig-psubst (list-transform-positive orig-tpsubst
				   (lambda (x) (pvar-form? (car x))))))
	    (if ;uninst-fla closed, i.e., not an elim or gfp aconst
	     (null? (formula-to-free (aconst-to-uninst-formula aconst)))
	     (let* ((new-tsubst (compose-substitutions tsubst orig-tsubst))
		    (free (formula-to-free inst-formula))
		    (n (length free)))
	       (if ;enough args
		(<= n (length args))
		(let* ((param-args (list-head args n))
		       (rest-args (list-tail args n))
		       (param-subst (make-substitution-wrt
				     var-term-equal? free param-args))
		       (new-topsubst (compose-substitutions param-subst
							    topsubst))
		       (new-aconst (aconst-substitute aconst new-topsubst))
		       (new-free (formula-to-free
				  (aconst-to-inst-formula new-aconst))))
		  (apply
		   mk-proof-in-elim-form
		   (make-proof-in-aconst-form new-aconst)
		   (append
		    (map make-term-in-var-form new-free)
		    (map (lambda (arg) (term-substitute arg tosubst))
			 rest-args))))
	     				;else eta expand and recursive call
		(let* ((rest-free (list-tail free (length args)))
		       (eta-expanded-proof
			(apply
			 mk-proof-in-nc-intro-form
			 (append rest-free
				 (list (apply mk-proof-in-elim-form
					      proof
					      (map make-term-in-var-form
						   rest-free)))))))
		  (proof-substitute
		   eta-expanded-proof topasubst opt-ignore-deco-flag))))
					;else elim or gfp aconst
	     (let* ((new-tsubst (compose-substitutions tsubst orig-tsubst))
		    (free (formula-to-free inst-formula))
		    (k (length (formula-to-free
				(aconst-to-uninst-formula aconst)))) ;# fp-vars
		    (fp-vars (list-head free k))
		    (param-vars (list-tail free k))
		    (n (length param-vars)))
	       (if ;enough args
		(<= (+ k n) (length args))
		(let* ((fp-args (list-head args k))
		       (param-and-rest-args (list-tail args k))
		       (param-args (list-head param-and-rest-args n))
		       ;; (rest-args (list-tail param-and-rest-args n))
		       (param-subst (make-substitution-wrt
				     var-term-equal? param-vars param-args))
		       (new-psubst
			(compose-substitutions
			 topsubst
			 (compose-substitutions param-subst orig-psubst)))
		       (new-tpsubst (append new-tsubst new-psubst))
		       (new-aconst (aconst-substitute
				    aconst new-tpsubst opt-ignore-deco-flag)))
		  (apply
		   mk-proof-in-elim-form
		   (make-proof-in-aconst-form new-aconst)
		   (map (lambda (arg) (term-substitute arg tosubst))
			(append fp-args param-and-rest-args))))
	     				;else eta expand and recursive call
		(let* ((rest-free (list-tail free (length args)))
		       (eta-expanded-proof
			(apply
			 mk-proof-in-nc-intro-form
			 (append rest-free
				 (list (apply mk-proof-in-elim-form
					      proof
					      (map make-term-in-var-form
						   rest-free)))))))
		  (proof-substitute
		   eta-expanded-proof topasubst opt-ignore-deco-flag)))))))))
      ((proof-in-imp-intro-form)
       (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	      (kernel (proof-in-imp-intro-form-to-kernel proof))
	      (formula (avar-to-formula avar))
	      (avars (map car asubst))
	      (active-avars (intersection-wrt
			     avar=? avars (proof-to-free-avars proof)))
	      (active-asubst (list-transform-positive asubst
			       (lambda (x)
				 (member-wrt avar=? (car x) active-avars))))
	      (active-proofs (map cadr active-asubst))
	      (new-avar
	       (if ;formula is not changed
		(classical-formula=?
		 formula (formula-substitute formula topsubst))
		(if ;there is no clash
		 (not (member-wrt
		       avar=? avar (apply append (map proof-to-free-avars
						      active-proofs))))
		 avar
		 (formula-to-new-avar formula))
		(formula-to-new-avar (formula-substitute formula topsubst))))
	      (new-asubst (if (avar=? avar new-avar)
			      active-asubst
			      (cons (list avar (make-proof-in-avar-form
						new-avar))
				    active-asubst))))
	 (make-proof-in-imp-intro-form
	  new-avar (proof-substitute
		    kernel (append topsubst new-asubst) opt-ignore-deco-flag))))
      ((proof-in-imp-elim-form)
       (let ((op (proof-in-imp-elim-form-to-op proof))
	     (arg (proof-in-imp-elim-form-to-arg proof)))
	 (make-proof-in-imp-elim-form
	  (proof-substitute op topasubst opt-ignore-deco-flag)
	  (proof-substitute arg topasubst opt-ignore-deco-flag))))
      ((proof-in-impnc-intro-form)
       (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	      (kernel (proof-in-impnc-intro-form-to-kernel proof))
	      (formula (avar-to-formula avar))
	      (avars (map car asubst))
	      (active-avars (intersection-wrt
			     avar=? avars (proof-to-free-avars proof)))
	      (active-asubst (list-transform-positive asubst
			       (lambda (x)
				 (member-wrt avar=? (car x) active-avars))))
	      (active-proofs (map cadr active-asubst))
	      (new-avar
	       (if ;formula is not changed
		(classical-formula=?
		 formula (formula-substitute formula topsubst))
		(if ;there is no clash
		 (not (member-wrt
		       avar=? avar (apply append (map proof-to-free-avars
						      active-proofs))))
		 avar
		 (formula-to-new-avar formula))
		(formula-to-new-avar (formula-substitute formula topsubst))))
	      (new-asubst (if (avar=? avar new-avar)
			      active-asubst
			      (cons (list avar (make-proof-in-avar-form
						new-avar))
				    active-asubst))))
	 (make-proof-in-impnc-intro-form
	  new-avar (proof-substitute
		    kernel (append topsubst new-asubst) opt-ignore-deco-flag))))
      ((proof-in-impnc-elim-form)
       (let ((op (proof-in-impnc-elim-form-to-op proof))
	     (arg (proof-in-impnc-elim-form-to-arg proof)))
	 (make-proof-in-impnc-elim-form
	  (proof-substitute op topasubst opt-ignore-deco-flag)
	  (proof-substitute arg topasubst opt-ignore-deco-flag))))
      ((proof-in-and-intro-form)
       (make-proof-in-and-intro-form
	(proof-substitute
	 (proof-in-and-intro-form-to-left proof) topasubst opt-ignore-deco-flag)
	(proof-substitute
	 (proof-in-and-intro-form-to-right proof)
	 topasubst opt-ignore-deco-flag)))
      ((proof-in-and-elim-left-form)
       (make-proof-in-and-elim-left-form
	(proof-substitute
	 (proof-in-and-elim-left-form-to-kernel proof)
	 topasubst opt-ignore-deco-flag)))
      ((proof-in-and-elim-right-form)
       (make-proof-in-and-elim-right-form
	(proof-substitute
	 (proof-in-and-elim-right-form-to-kernel proof)
	 topasubst opt-ignore-deco-flag)))
      ((proof-in-all-intro-form)
       (let* ((var (proof-in-all-intro-form-to-var proof))
	      (kernel (proof-in-all-intro-form-to-kernel proof))
	      (type (var-to-type var))
	      (tovars (map car tosubst))
	      (active-substvars (intersection tovars (proof-to-free proof)))
	      (active-subst (list-transform-positive tosubst
			      (lambda (x) (member (car x) active-substvars))))
	      (active-terms (map cadr active-subst))
	      (active-psubstvars
	       (intersection (map car topsubst) (proof-to-pvars proof)))
	      (active-psubst (list-transform-positive topsubst
			       (lambda (x)
				 (member (car x) active-psubstvars))))
	      (active-cterms (map cadr active-psubst))
	      (active-asubstvars
	       (intersection-wrt
		avar=? (map car asubst) (proof-to-free-avars proof)))
	      (active-asubst (list-transform-positive asubst
			       (lambda (x)
				 (member (car x) active-asubstvars))))
	      (active-proofs (map cadr active-asubst))
	      (free (apply union (append (map term-to-free active-terms)
					 (map cterm-to-free active-cterms)
					 (map proof-to-free active-proofs))))
	      (new-var
	       (if ;type is not changed
		(null? (intersection (type-to-tvars type) (map car tsubst)))
		(if ;there is no clash
		 (not (member var free))
		 var
		 (var-to-new-var var))
		(if (t-deg-zero? (var-to-t-deg var))
		    (type-to-new-partial-var (type-substitute type tsubst))
		    (type-to-new-var (type-substitute type tsubst)))))
	      (new-subst (compose-substitutions
			  (make-subst var (make-term-in-var-form new-var))
			  active-subst)))
	 (make-proof-in-all-intro-form
	  new-var
	  (proof-substitute
	   kernel (append tsubst new-subst active-psubst active-asubst)
	   opt-ignore-deco-flag))))
      ((proof-in-allnc-intro-form)
       (let* ((var (proof-in-allnc-intro-form-to-var proof))
	      (kernel (proof-in-allnc-intro-form-to-kernel proof))
	      (type (var-to-type var))
	      (tovars (map car tosubst))
	      (active-substvars (intersection tovars (proof-to-free proof)))
	      (active-subst (list-transform-positive tosubst
			      (lambda (x) (member (car x) active-substvars))))
	      (active-terms (map cadr active-subst))
	      (active-psubstvars
	       (intersection (map car topsubst) (proof-to-pvars proof)))
	      (active-psubst (list-transform-positive topsubst
			       (lambda (x)
				 (member (car x) active-psubstvars))))
	      (active-cterms (map cadr active-psubst))
	      (active-asubstvars
	       (intersection-wrt
		avar=? (map car asubst) (proof-to-free-avars proof)))
	      (active-asubst (list-transform-positive asubst
			       (lambda (x)
				 (member (car x) active-asubstvars))))
	      (active-proofs (map cadr active-asubst))
	      (free (apply union (append (map term-to-free active-terms)
					 (map cterm-to-free active-cterms)
					 (map proof-to-free active-proofs))))
	      (new-var
	       (if ;type is not changed
		(null? (intersection (type-to-tvars type) (map car tsubst)))
		(if ;there is no clash
		 (not (member var free))
		 var
		 (var-to-new-var var))
		(if (t-deg-zero? (var-to-t-deg var))
		    (type-to-new-partial-var (type-substitute type tsubst))
		    (type-to-new-var (type-substitute type tsubst)))))
	      (new-subst (compose-substitutions
			  (make-subst var (make-term-in-var-form new-var))
			  active-subst)))
	 (make-proof-in-allnc-intro-form
	  new-var
	  (proof-substitute
	   kernel (append tsubst new-subst active-psubst active-asubst)
	   opt-ignore-deco-flag))))
      (else (myerror "proof-substitute" "proof tag expected" (tag proof))))))

(define (avar-proof-equal? avar proof)
  (and (proof-in-avar-form? proof)
       (avar=? avar (proof-in-avar-form-to-avar proof))))

(define (proof-subst proof arg val)
  (let ((equality?
	 (cond
	  ((and (tvar? arg) (type? val)) equal?)
	  ((and (var-form? arg) (term-form? val)) var-term-equal?)
	  ((and (pvar? arg) (cterm-form? val)) pvar-cterm-equal?)
	  ((and (avar-form? arg) (proof-form? val)) avar-proof-equal?)
	  (else (myerror "proof-subst" "unexpected arg" arg "and val" val)))))
    (proof-substitute proof (make-subst-wrt equality? arg val))))

(define (proof-substitute-and-beta0-nf proof subst)
  (if
   (null? subst)
   proof
   (case (tag proof)
     ((proof-in-avar-form)
      (let* ((avar (proof-in-avar-form-to-avar proof))
	     (formula (avar-to-formula avar))
	     (newavar
	      (if (intersection (map car subst) (formula-to-free formula))
		  (make-avar
		   (formula-substitute-and-beta0-nf
		    (avar-to-formula avar) subst)
		   (avar-to-index avar)
		   (avar-to-name avar))
		  avar)))
	(make-proof-in-avar-form newavar)))
     ((proof-in-aconst-form) proof)
     ((proof-in-imp-intro-form)
      (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	     (formula (avar-to-formula avar))
	     (newavar
	      (if (intersection (map car subst) (formula-to-free formula))
		  (make-avar
		   (formula-substitute-and-beta0-nf formula subst)
		   (avar-to-index avar)
		   (avar-to-name avar))
		  avar))
	     (kernel (proof-in-imp-intro-form-to-kernel proof)))
	(make-proof-in-imp-intro-form newavar
				      (proof-substitute-and-beta0-nf
				       kernel subst))))
     ((proof-in-imp-elim-form)
      (make-proof-in-imp-elim-form
       (proof-substitute-and-beta0-nf
	(proof-in-imp-elim-form-to-op proof) subst)
       (proof-substitute-and-beta0-nf
	(proof-in-imp-elim-form-to-arg proof) subst)))
     ((proof-in-impnc-intro-form)
      (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	     (formula (avar-to-formula avar))
	     (newavar
	      (if (intersection (map car subst) (formula-to-free formula))
		  (make-avar
		   (formula-substitute-and-beta0-nf formula subst)
		   (avar-to-index avar)
		   (avar-to-name avar))
		  avar))
	     (kernel (proof-in-impnc-intro-form-to-kernel proof)))
	(make-proof-in-impnc-intro-form newavar
				      (proof-substitute-and-beta0-nf
				       kernel subst))))
     ((proof-in-impnc-elim-form)
      (make-proof-in-impnc-elim-form
       (proof-substitute-and-beta0-nf
	(proof-in-impnc-elim-form-to-op proof) subst)
       (proof-substitute-and-beta0-nf
	(proof-in-impnc-elim-form-to-arg proof) subst)))
     ((proof-in-and-intro-form)
      (make-proof-in-and-intro-form
       (proof-substitute-and-beta0-nf
	(proof-in-and-intro-form-to-left proof) subst)
       (proof-substitute-and-beta0-nf
	(proof-in-and-intro-form-to-right proof) subst)))
     ((proof-in-and-elim-left-form)
      (make-proof-in-and-elim-left-form
       (proof-substitute-and-beta0-nf
	(proof-in-and-elim-left-form-to-kernel proof) subst)))
     ((proof-in-and-elim-right-form)
      (make-proof-in-and-elim-right-form
       (proof-substitute-and-beta0-nf
	(proof-in-and-elim-right-form-to-kernel proof) subst)))
     ((proof-in-all-intro-form)
      (let* ((var (proof-in-all-intro-form-to-var proof))
	     (kernel (proof-in-all-intro-form-to-kernel proof))
	     (vars (map car subst))
	     (active-vars (intersection vars (proof-to-free proof)))
	     (active-subst
	      (do ((l subst (cdr l))
		   (res '() (if (member (caar l) active-vars)
				(cons (car l) res)
				res)))
		  ((null? l) (reverse res))))
	     (active-terms (map cadr active-subst)))
	(if (member var (apply union (map term-to-free active-terms)))
	    (let ((new-var (var-to-new-var var)))
	      (make-proof-in-all-intro-form
	       new-var
	       (proof-substitute-and-beta0-nf
		kernel (cons (list var (make-term-in-var-form new-var))
			     active-subst))))
	    (make-proof-in-all-intro-form
	     var (proof-substitute-and-beta0-nf kernel active-subst)))))
     ((proof-in-all-elim-form)
      (make-proof-in-all-elim-form
       (proof-substitute-and-beta0-nf
	(proof-in-all-elim-form-to-op proof) subst)
       (term-substitute-and-beta0-nf
	(proof-in-all-elim-form-to-arg proof) subst)))
     ((proof-in-allnc-intro-form)
      (let* ((var (proof-in-allnc-intro-form-to-var proof))
	     (kernel (proof-in-allnc-intro-form-to-kernel proof))
	     (vars (map car subst))
	     (active-vars (intersection vars (proof-to-free proof)))
	     (active-subst
	      (do ((l subst (cdr l))
		   (res '() (if (member (caar l) active-vars)
				(cons (car l) res)
				res)))
		  ((null? l) (reverse res))))
	     (active-terms (map cadr active-subst)))
	(if (member var (apply union (map term-to-free active-terms)))
	    (let ((new-var (var-to-new-var var)))
	      (make-proof-in-allnc-intro-form
	       new-var
	       (proof-substitute-and-beta0-nf
		kernel (cons (list var (make-term-in-var-form new-var))
			     active-subst))))
	    (make-proof-in-allnc-intro-form
	     var (proof-substitute-and-beta0-nf kernel active-subst)))))
     ((proof-in-allnc-elim-form)
      (make-proof-in-allnc-elim-form
       (proof-substitute-and-beta0-nf
	(proof-in-allnc-elim-form-to-op proof) subst)
       (term-substitute-and-beta0-nf
	(proof-in-allnc-elim-form-to-arg proof) subst)))
     (else (myerror "proof-substitute-and-beta0-nf" "proof tag expected"
		    (tag proof))))))

;; (expand-theorems proof) expands all theorems recursively.
;; (expand-theorems proof opt-name-test) expands (non-recursively) the theorems
;; passing the test by instances of their saved proofs.

(define (expand-theorems proof . opt-name-test)
  (case (tag proof)
    ((proof-in-avar-form) proof)
    ((proof-in-aconst-form)
     (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	    (name (aconst-to-name aconst))
	    (kind (aconst-to-kind aconst)))
       (cond ((not (eq? 'theorem kind)) proof)
             ((null? opt-name-test)
	      (let* ((inst-proof (theorem-aconst-to-inst-proof aconst))
		     (free (formula-to-free (proof-to-formula inst-proof))))
		(expand-theorems
		 (apply mk-proof-in-nc-intro-form
			(append free (list inst-proof))))))
	     (((car opt-name-test) name)
	      (let* ((inst-proof (theorem-aconst-to-inst-proof aconst))
		     (free (formula-to-free (proof-to-formula inst-proof))))
		(apply mk-proof-in-nc-intro-form
		       (append free (list inst-proof)))))
	     (else proof))))
    ((proof-in-imp-elim-form)
     (let ((op (proof-in-imp-elim-form-to-op proof))
	   (arg (proof-in-imp-elim-form-to-arg proof)))
       (make-proof-in-imp-elim-form
	(apply expand-theorems op opt-name-test)
	(apply expand-theorems arg opt-name-test))))
    ((proof-in-imp-intro-form)
     (let ((avar (proof-in-imp-intro-form-to-avar proof))
	   (kernel (proof-in-imp-intro-form-to-kernel proof)))
       (make-proof-in-imp-intro-form
	avar (apply expand-theorems kernel opt-name-test))))
    ((proof-in-impnc-elim-form)
     (let ((op (proof-in-impnc-elim-form-to-op proof))
	   (arg (proof-in-impnc-elim-form-to-arg proof)))
       (make-proof-in-impnc-elim-form
	(apply expand-theorems op opt-name-test)
	(apply expand-theorems arg opt-name-test))))
    ((proof-in-impnc-intro-form)
     (let ((avar (proof-in-impnc-intro-form-to-avar proof))
	   (kernel (proof-in-impnc-intro-form-to-kernel proof)))
       (make-proof-in-impnc-intro-form
	avar (apply expand-theorems kernel opt-name-test))))
    ((proof-in-and-intro-form)
     (let ((left (proof-in-and-intro-form-to-left proof))
	   (right (proof-in-and-intro-form-to-right proof)))
       (make-proof-in-and-intro-form
	(apply expand-theorems left opt-name-test)
	(apply expand-theorems right opt-name-test))))
    ((proof-in-and-elim-left-form)
     (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (make-proof-in-and-elim-left-form
	(apply expand-theorems kernel opt-name-test))))
    ((proof-in-and-elim-right-form)
     (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (make-proof-in-and-elim-right-form
	(apply expand-theorems kernel opt-name-test))))
    ((proof-in-all-intro-form)
     (let ((var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-proof-in-all-intro-form
	var (apply expand-theorems kernel opt-name-test))))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
       (make-proof-in-all-elim-form
	(apply expand-theorems op opt-name-test) arg)))
    ((proof-in-allnc-intro-form)
     (let ((var (proof-in-allnc-intro-form-to-var proof))
	   (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-proof-in-allnc-intro-form
	var (apply expand-theorems kernel opt-name-test))))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof))
	   (arg (proof-in-allnc-elim-form-to-arg proof)))
       (make-proof-in-allnc-elim-form
	(apply expand-theorems op opt-name-test) arg)))
    (else (myerror "expand-theorems" "proof tag expected" (tag proof)))))

(define (expand-thm proof thm-name)
  (expand-theorems proof (lambda (name) (string=? name thm-name))))

(define (expand-theorems-with-positive-content proof)
  (case (tag proof)
    ((proof-in-avar-form) proof)
    ((proof-in-aconst-form)
     (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	    (name (aconst-to-name aconst))
	    (kind (aconst-to-kind aconst)))
       (if (and (eq? 'theorem (aconst-to-kind aconst))
		(not (formula-of-nulltypep? (aconst-to-formula aconst))))
	   (let* ((inst-proof (theorem-aconst-to-inst-proof aconst))
		  (free (formula-to-free (proof-to-formula inst-proof))))
	     (expand-theorems-with-positive-content
	      (apply mk-proof-in-nc-intro-form
		     (append free (list inst-proof)))))
	   proof)))
    ((proof-in-imp-elim-form)
     (let ((op (proof-in-imp-elim-form-to-op proof))
	   (arg (proof-in-imp-elim-form-to-arg proof)))
       (make-proof-in-imp-elim-form
	(expand-theorems-with-positive-content op)
	(expand-theorems-with-positive-content arg))))
    ((proof-in-imp-intro-form)
     (let ((avar (proof-in-imp-intro-form-to-avar proof))
	   (kernel (proof-in-imp-intro-form-to-kernel proof)))
       (make-proof-in-imp-intro-form
	avar (expand-theorems-with-positive-content kernel))))
    ((proof-in-impnc-elim-form)
     (let ((op (proof-in-impnc-elim-form-to-op proof))
	   (arg (proof-in-impnc-elim-form-to-arg proof)))
       (make-proof-in-impnc-elim-form
	(expand-theorems-with-positive-content op)
	(expand-theorems-with-positive-content arg))))
    ((proof-in-impnc-intro-form)
     (let ((avar (proof-in-impnc-intro-form-to-avar proof))
	   (kernel (proof-in-impnc-intro-form-to-kernel proof)))
       (make-proof-in-impnc-intro-form
	avar (expand-theorems-with-positive-content kernel))))
    ((proof-in-and-intro-form)
     (let ((left (proof-in-and-intro-form-to-left proof))
	   (right (proof-in-and-intro-form-to-right proof)))
       (make-proof-in-and-intro-form
	(expand-theorems-with-positive-content left)
	(expand-theorems-with-positive-content right))))
    ((proof-in-and-elim-left-form)
     (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (make-proof-in-and-elim-left-form
	(expand-theorems-with-positive-content kernel))))
    ((proof-in-and-elim-right-form)
     (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (make-proof-in-and-elim-right-form
	(expand-theorems-with-positive-content kernel))))
    ((proof-in-all-intro-form)
     (let ((var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-proof-in-all-intro-form
	var (expand-theorems-with-positive-content kernel))))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
       (make-proof-in-all-elim-form
	(expand-theorems-with-positive-content op) arg)))
    ((proof-in-allnc-intro-form)
     (let ((var (proof-in-allnc-intro-form-to-var proof))
	   (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-proof-in-allnc-intro-form
	var (expand-theorems-with-positive-content kernel))))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof))
	   (arg (proof-in-allnc-elim-form-to-arg proof)))
       (make-proof-in-allnc-elim-form
	(expand-theorems-with-positive-content op) arg)))
    (else (myerror "expand-theorems-with-positive-content"
		   "proof tag expected" (tag proof)))))

;; rename-avars similar to rename-variables in formula.scm

(define (rename-avars . opt-proof-or-thm-name)
  (if (null? opt-proof-or-thm-name)
      (rename-avars (current-proof))
      (let* ((proof-or-thm-name (car opt-proof-or-thm-name))
	     (proof (cond ((proof-form? proof-or-thm-name) proof-or-thm-name)
			  ((string? proof-or-thm-name)
			   (theorem-name-to-proof proof-or-thm-name))
			  (else (myerror "rename-avars"
					 "proof or theorem name expected"
					 proof-or-thm-name))))
	     (free-avars (proof-to-free-avars proof))
	     (used-name-index-alist
	      (map (lambda (avar) (list (avar-to-name avar)
					(avar-to-index avar)))
		   free-avars)))
	(rename-avars-aux proof used-name-index-alist))))

(define (rename-avars-aux proof used-name-index-alist)
  (case (tag proof)
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (new-avar (avar-and-used-name-index-alist-to-new-avar
		       avar used-name-index-alist))
	    (asubst (make-subst-wrt avar-proof-equal?
				    avar (make-proof-in-avar-form new-avar)))
	    (subst-kernel (if (null? asubst)
			      kernel
			      (proof-substitute kernel asubst))))
       (make-proof-in-imp-intro-form
	new-avar
	(rename-avars-aux subst-kernel (cons (list (avar-to-name new-avar)
						   (avar-to-index new-avar))
					     used-name-index-alist)))))
    ((proof-in-imp-elim-form)
     (make-proof-in-imp-elim-form
      (rename-avars-aux (proof-in-imp-elim-form-to-op proof)
			used-name-index-alist)
      (rename-avars-aux (proof-in-imp-elim-form-to-arg proof)
			used-name-index-alist)))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (new-avar (avar-and-used-name-index-alist-to-new-avar
		       avar used-name-index-alist))
	    (asubst (make-subst-wrt avar-proof-equal?
				    avar (make-proof-in-avar-form new-avar)))
	    (subst-kernel (if (null? asubst)
			      kernel
			      (proof-substitute kernel asubst))))
       (make-proof-in-impnc-intro-form
	new-avar
	(rename-avars-aux subst-kernel (cons (list (avar-to-name new-avar)
						   (avar-to-index new-avar))
					     used-name-index-alist)))))
    ((proof-in-impnc-elim-form)
     (make-proof-in-impnc-elim-form
      (rename-avars-aux (proof-in-impnc-elim-form-to-op proof)
			used-name-index-alist)
      (rename-avars-aux (proof-in-impnc-elim-form-to-arg proof)
			used-name-index-alist)))
    ((proof-in-and-intro-form)
     (make-proof-in-and-intro-form
      (rename-avars-aux (proof-in-and-intro-form-to-left proof)
			used-name-index-alist)
      (rename-avars-aux (proof-in-and-intro-form-to-right proof)
			used-name-index-alist)))
    ((proof-in-and-elim-left-form)
     (make-proof-in-and-elim-left-form
      (rename-avars-aux
       (proof-in-and-elim-left-form-to-kernel proof) used-name-index-alist)))
    ((proof-in-and-elim-right-form)
     (make-proof-in-and-elim-right-form
      (rename-avars-aux
       (proof-in-and-elim-right-form-to-kernel proof) used-name-index-alist)))
    ((proof-in-all-intro-form)
     (let ((var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-proof-in-all-intro-form
	var (rename-avars-aux kernel used-name-index-alist))))
    ((proof-in-all-elim-form)
     (make-proof-in-all-elim-form
      (rename-avars-aux (proof-in-all-elim-form-to-op proof)
			used-name-index-alist)
      (proof-in-all-elim-form-to-arg proof)))
    ((proof-in-allnc-intro-form)
     (let ((var (proof-in-allnc-intro-form-to-var proof))
	   (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-proof-in-allnc-intro-form
	var (rename-avars-aux kernel used-name-index-alist))))
    ((proof-in-allnc-elim-form)
     (make-proof-in-allnc-elim-form
      (rename-avars-aux (proof-in-allnc-elim-form-to-op proof)
			used-name-index-alist)
      (proof-in-allnc-elim-form-to-arg proof)))
    (else proof)))

(define (avar-and-used-name-index-alist-to-new-avar avar used-name-index-alist)
  (let* ((formula (avar-to-formula avar))
	 (index (avar-to-index avar))
	 (name (avar-to-name avar))
	 (proper-name (if (string=? "" name) DEFAULT-AVAR-NAME name))
	 (info (assoc proper-name used-name-index-alist))
	 (new-index (if info (+ 1 (cadr info)) -1)))
    (make-avar formula new-index proper-name)))

;; 10-4. Display
;; =============

(define (display-proof . opt-proof-or-thm-name)
  (if (null? opt-proof-or-thm-name)
      (display-proof (current-proof))
      (let* ((proof-or-thm-name (car opt-proof-or-thm-name))
	     (proof (cond ((proof-form? proof-or-thm-name) proof-or-thm-name)
			  ((string? proof-or-thm-name)
			   (theorem-name-to-proof proof-or-thm-name))
			  (else (myerror "display-proof"
					 "proof or theorem name expected"
					 proof-or-thm-name)))))
	(display-proof-aux proof 0))))

(define dp display-proof)

(define (display-normalized-proof . opt-proof-or-thm-name)
  (if (null? opt-proof-or-thm-name)
      (display-normalized-proof (current-proof))
      (let* ((proof-or-thm-name (car opt-proof-or-thm-name))
	     (proof (cond ((proof-form? proof-or-thm-name) proof-or-thm-name)
			  ((string? proof-or-thm-name)
			   (theorem-name-to-proof proof-or-thm-name))
			  (else (myerror "display-normalized-proof"
					 "proof or theorem name expected"
					 proof-or-thm-name)))))
	(display-proof-aux (nbe-normalize-proof proof) 0))))

(define dnp display-normalized-proof)

(define (display-proof-aux proof n)
  (if
   COMMENT-FLAG
   (case (tag proof)
     ((proof-in-avar-form)
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by assumption ")
      (display (avar-to-string (proof-in-avar-form-to-avar proof))) (newline))
     ((proof-in-aconst-form)
      (let ((aconst (proof-in-aconst-form-to-aconst proof)))
	(display-comment (make-string n #\.))
	(dff (proof-to-formula proof))
	(case (aconst-to-kind aconst)
	  ((axiom) (display " by axiom "))
	  ((theorem) (display " by theorem "))
	  ((global-assumption) (display " by global assumption "))
	  (else (myerror "display-proof-aux" "kind of aconst expected"
			 (aconst-to-kind aconst))))
	(display (aconst-to-name aconst))
	(newline)))
     ((proof-in-imp-intro-form)
      (display-proof-aux (proof-in-imp-intro-form-to-kernel proof) (+ n 1))
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by imp intro ")
      (display (avar-to-string (proof-in-imp-intro-form-to-avar proof)))
      (newline))
     ((proof-in-imp-elim-form)
      (display-proof-aux (proof-in-imp-elim-form-to-op proof) (+ n 1))
      (display-proof-aux (proof-in-imp-elim-form-to-arg proof) (+ n 1))
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by imp elim") (newline))
     ((proof-in-impnc-intro-form)
      (display-proof-aux (proof-in-impnc-intro-form-to-kernel proof) (+ n 1))
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by impnc intro ")
      (display (avar-to-string (proof-in-impnc-intro-form-to-avar proof)))
      (newline))
     ((proof-in-impnc-elim-form)
      (display-proof-aux (proof-in-impnc-elim-form-to-op proof) (+ n 1))
      (display-proof-aux (proof-in-impnc-elim-form-to-arg proof) (+ n 1))
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by impnc elim") (newline))
     ((proof-in-and-intro-form)
      (display-proof-aux (proof-in-and-intro-form-to-left proof) (+ n 1))
      (display-proof-aux (proof-in-and-intro-form-to-right proof) (+ n 1))
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by and intro") (newline))
     ((proof-in-and-elim-left-form)
      (display-proof-aux
       (proof-in-and-elim-left-form-to-kernel proof) (+ n 1))
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by and elim left") (newline))
     ((proof-in-and-elim-right-form)
      (display-proof-aux
       (proof-in-and-elim-right-form-to-kernel proof) (+ n 1))
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by and elim right") (newline))
     ((proof-in-all-intro-form)
      (display-proof-aux (proof-in-all-intro-form-to-kernel proof) (+ n 1))
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by all intro") (newline))
     ((proof-in-all-elim-form)
      (display-proof-aux (proof-in-all-elim-form-to-op proof) (+ n 1))
      (display-comment (make-string (+ n 1) #\.))
      (display-term (proof-in-all-elim-form-to-arg proof)) (newline)
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by all elim") (newline))
     ((proof-in-allnc-intro-form)
      (display-proof-aux (proof-in-allnc-intro-form-to-kernel proof) (+ n 1))
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by allnc intro") (newline))
     ((proof-in-allnc-elim-form)
      (display-proof-aux (proof-in-allnc-elim-form-to-op proof) (+ n 1))
      (display-comment (make-string (+ n 1) #\.))
      (display-term (proof-in-allnc-elim-form-to-arg proof)) (newline)
      (display-comment (make-string n #\.))
      (dff (proof-to-formula proof)) (display " by allnc elim") (newline))
     (else (myerror "display-proof-aux" "proof tag expected" (tag proof))))))

(define (dff formula) (df (fold-formula formula)))

(define (proof-to-pterm proof)
  (let* ((genavars (append (proof-to-free-and-bound-avars proof)
			   (proof-to-aconsts-without-rules proof)))
	 (vars (map (lambda (x)
		      (type-to-new-var
		       (nbe-formula-to-type
			(cond
			 ((avar-form? x) (avar-to-formula x))
			 ((aconst-form? x) (aconst-to-formula x))
			 (else (myerror
				"proof-to-pterm" "genavar expected" x))))))
		    genavars))
	 (genavar-var-alist (map (lambda (u x) (list u x)) genavars vars))
	 (var-genavar-alist (map (lambda (x u) (list x u)) vars genavars)))
    (proof-and-genavar-var-alist-to-pterm genavar-var-alist proof)))

(define (display-pterm . opt-proof)
  (if (and (null? opt-proof)
	   (null? PPROOF-STATE))
      (myerror
       "display-pterm: proof argument or proof under construction expected"))
  (let ((proof (if (null? opt-proof)
		   (pproof-state-to-proof)
		   (car opt-proof))))
    (if
     COMMENT-FLAG
     (term-to-string (proof-to-pterm proof)))))

(define dpt display-pterm)

(define (display-normalized-pterm . opt-proof)
  (if (and (null? opt-proof)
	   (null? PPROOF-STATE))
      (myerror "display-normalized-pterm"
	       "proof argument or proof under construction expected"))
  (let ((proof (if (null? opt-proof)
		   (pproof-state-to-proof)
		   (car opt-proof))))
    (if
     COMMENT-FLAG
     (term-to-string (proof-to-pterm (nbe-normalize-proof proof))))))

(define dnpt display-normalized-pterm)

(define (display-eterm . opt-proof)
  (if (and (null? opt-proof)
	   (null? PPROOF-STATE))
      (myerror
       "display-eterm: proof argument or proof under construction expected"))
  (let ((proof (if (null? opt-proof)
		   (pproof-state-to-proof)
		   (car opt-proof))))
    (if
     COMMENT-FLAG
     (term-to-string (proof-to-extracted-term proof)))))

(define det display-eterm)

(define (display-normalized-eterm . opt-proof)
  (if (and (null? opt-proof)
	   (null? PPROOF-STATE))
      (myerror "display-normalized-eterm"
	       "proof argument or proof under construction expected"))
  (let ((proof (if (null? opt-proof)
		   (pproof-state-to-proof)
		   (car opt-proof))))
    (if
     COMMENT-FLAG
     (term-to-string (nbe-normalize-term (proof-to-extracted-term proof))))))

(define dnet display-normalized-eterm)

;; We also provide a readable type-free lambda expression

(define (proof-to-expr . opt-proof-or-thm-name)
  (if
   (null? opt-proof-or-thm-name)
   (proof-to-expr (current-proof))
   (let* ((proof-or-thm-name (car opt-proof-or-thm-name))
	  (proof (cond ((proof-form? proof-or-thm-name) proof-or-thm-name)
		       ((string? proof-or-thm-name)
			(theorem-name-to-proof proof-or-thm-name))
		       (else (myerror "proof-to-expr"
				      "proof or theorem name expected"
				      proof-or-thm-name)))))
     (case (tag proof)
       ((proof-in-avar-form)
	(let* ((avar (proof-in-avar-form-to-avar proof))
	       (string (avar-to-string avar)))
	  (string->symbol string)))
       ((proof-in-aconst-form)
	(let* ((aconst (proof-in-aconst-form-to-aconst proof))
	       (string (aconst-to-name aconst)))
	  (string->symbol string)))
       ((proof-in-imp-intro-form)
	(let* ((avar (proof-in-imp-intro-form-to-avar proof))
	       (kernel (proof-in-imp-intro-form-to-kernel proof))
	       (string (avar-to-string avar)))
	  (list 'lambda (list (string->symbol string))
		(proof-to-expr kernel))))
       ((proof-in-imp-elim-form)
	(let* ((op (proof-in-imp-elim-form-to-op proof))
	       (arg (proof-in-imp-elim-form-to-arg proof)))
	  (list (proof-to-expr op)
		(proof-to-expr arg))))
       ((proof-in-impnc-intro-form)
	(let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	       (kernel (proof-in-impnc-intro-form-to-kernel proof))
	       (string (avar-to-string avar)))
	  (list 'lambda (list (string->symbol string))
		(proof-to-expr kernel))))
       ((proof-in-impnc-elim-form)
	(let* ((op (proof-in-impnc-elim-form-to-op proof))
	       (arg (proof-in-impnc-elim-form-to-arg proof)))
	  (list (proof-to-expr op)
		(proof-to-expr arg))))
       ((proof-in-and-intro-form)
	(let* ((left (proof-in-and-intro-form-to-left proof))
	       (right (proof-in-and-intro-form-to-right proof)))
	  (list 'cons (proof-to-expr left) (proof-to-expr right))))
       ((proof-in-and-elim-left-form)
	(let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
	  (list 'car (proof-to-expr kernel))))
       ((proof-in-and-elim-right-form)
	(let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
	  (list 'cdr (proof-to-expr kernel))))
       ((proof-in-all-intro-form)
	(let* ((var (proof-in-all-intro-form-to-var proof))
	       (kernel (proof-in-all-intro-form-to-kernel proof))
	       (var-expr (term-to-expr (make-term-in-var-form var))))
	  (list 'lambda (list var-expr)	(proof-to-expr kernel))))
       ((proof-in-all-elim-form)
	(let* ((op (proof-in-all-elim-form-to-op proof))
	       (arg (proof-in-all-elim-form-to-arg proof)))
	  (list (proof-to-expr op) (term-to-expr arg))))
       ((proof-in-allnc-intro-form)
	(let* ((var (proof-in-allnc-intro-form-to-var proof))
	       (kernel (proof-in-allnc-intro-form-to-kernel proof))
	       (var-expr (term-to-expr (make-term-in-var-form var))))
	  (list 'lambda (list var-expr)	(proof-to-expr kernel))))
       ((proof-in-allnc-elim-form)
	(let* ((op (proof-in-allnc-elim-form-to-op proof))
	       (arg (proof-in-allnc-elim-form-to-arg proof)))
	  (list (proof-to-expr op) (term-to-expr arg))))
       (else (myerror "proof-to-expr" "proof tag expected" (tag proof)))))))

(define (display-proof-expr . opt-proof)
  (if (and (null? opt-proof)
	   (null? PPROOF-STATE))
      (myerror
       "display-proof-expr"
       "proof argument or proof under construction expected"))
  (let* ((proof (if (null? opt-proof)
		    (pproof-state-to-proof)
		    (car opt-proof))))
    (cond
     (COMMENT-FLAG
      (proof-to-expr proof)))))

(define dpe display-proof-expr)

(define (display-normalized-proof-expr . opt-proof)
  (if (and (null? opt-proof)
	   (null? PPROOF-STATE))
      (myerror
       "display-normalized-proof-expr"
       " proof argument or proof under construction expected"))
  (let ((proof (if (null? opt-proof)
		   (pproof-state-to-proof)
		   (car opt-proof))))
    (if
     COMMENT-FLAG
     (proof-to-expr (nbe-normalize-proof proof)))))

(define dnpe display-normalized-proof-expr)

(define (proof-to-expr-with-formulas . opt-proof-or-thm-name-and-fold)
  (if (null? opt-proof-or-thm-name-and-fold)
      (proof-to-expr-with-formulas-aux (rename-avars (current-proof))
				       fold-formula)
      (let* ((fst (car opt-proof-or-thm-name-and-fold))
	     (rest (cdr opt-proof-or-thm-name-and-fold))
	     (proof-or-thm-name
	      (if (or (proof-form? fst) (string? fst)) fst (current-proof)))
	     (proof (cond ((proof-form? proof-or-thm-name) proof-or-thm-name)
			  ((string? proof-or-thm-name)
			   (theorem-name-to-proof proof-or-thm-name))
			  (else (myerror "proof-to-expr-with-formulas"
					 "proof or theorem name expected"
					 proof-or-thm-name))))
	     (f (if (or (proof-form? fst) (string? fst))
		    (if (pair? rest) (car rest) fold-formula)
		    fst)))
	(proof-to-expr-with-formulas-aux (rename-avars proof) f))))

(define (proof-to-expr-with-formulas-aux proof f)
  (if
   COMMENT-FLAG
   (let* ((aconsts (proof-to-aconsts proof))
	  (bound-avars (proof-to-bound-avars proof))
	  (free-avars (proof-to-free-avars proof)))
     (for-each
      (lambda (aconst)
	(display-comment
	 (aconst-to-name aconst) ": "
	 (pretty-print-string
	  (string-length COMMENT-STRING) ;indent
	  (- PP-WIDTH (string-length COMMENT-STRING))
	  (f (rename-variables (aconst-to-formula aconst)))))
	(newline))
      aconsts)
     (for-each
      (lambda (avar)
	(display-comment
	 (avar-to-string avar) ": "
	 (pretty-print-string
	  (string-length COMMENT-STRING) ;indent
	  (- PP-WIDTH (string-length COMMENT-STRING))
	  (f (rename-variables (avar-to-formula avar)))))
	(newline))
      free-avars)
     (for-each
      (lambda (avar)
	(display-comment
	 (avar-to-string avar) ": "
	 (pretty-print-string
	  (string-length COMMENT-STRING) ;indent
	  (- PP-WIDTH (string-length COMMENT-STRING))
	  (f (rename-variables (avar-to-formula avar)))))
	(newline))
      bound-avars)
     (newline)
     (proof-to-expr proof))))

(define (proof-to-expr-with-aconsts . opt-proof-and-fold)
  (if (null? opt-proof-and-fold)
      (proof-to-expr-with-aconsts-aux (current-proof) fold-formula)
      (let ((fst (car opt-proof-and-fold))
	    (rest (cdr opt-proof-and-fold)))
	(if (proof-form? fst)
	    (let ((f (if (null? rest) fold-formula (car rest))))
	      (proof-to-expr-with-aconsts-aux fst f))
	    (proof-to-expr-with-aconsts-aux (current-proof) fst)))))

(define (proof-to-expr-with-aconsts-aux proof f)
  (if
   COMMENT-FLAG
   (let* ((aconsts (proof-to-aconsts proof)))
     (display-comment "Assumption constants:")
     (newline)
     (for-each
      (lambda (aconst)
	(display-comment
	 (aconst-to-name aconst) ": "
	 (pretty-print-string
	  (string-length COMMENT-STRING) ;indent
	  (- PP-WIDTH (string-length COMMENT-STRING))
	  (f (aconst-to-formula aconst))))
	(newline))
      aconsts)
     (proof-to-expr proof))))

;; 10-5. Check
;; ===========

;; check-and-display-proof-aux sets ignore-deco-flag to true as soon
;; as its proof argument proves a formula of nulltype.  Moreover it is
;; checked that in c.r. parts every aconst has relevant pvars
;; substituted by c.r. cterms only.

(define (check-proof display-flag . opt-proof-and-ignore-deco-flag)
  (let* ((proof-and-ignore-deco-flag
	  (cond
	   ((null? opt-proof-and-ignore-deco-flag)
	    (list (current-proof) #f))
	   ((= 1 (length opt-proof-and-ignore-deco-flag))
	    (let ((first (car opt-proof-and-ignore-deco-flag)))
	      (cond ((proof-form? first) (list first #f))
		    ((boolean? first) (list (current-proof) first))
		    (else (myerror "check-proof" "proof or boolean expected"
				   first)))))
	   ((= 2 (length opt-proof-and-ignore-deco-flag)
	       (let ((first (car opt-proof-and-ignore-deco-flag))
		     (second (cadr opt-proof-and-ignore-deco-flag)))
		 (if (and (proof-form? first) (boolean? second))
		     (list first second)
		     (myerror "check-proof" "proof and boolean expected"
			      first second)))))
	   (else (myerror "check-proof"
			  "list of length <=2 expected"
			  opt-proof-and-ignore-deco-flag))))
	 (proof (car proof-and-ignore-deco-flag))
	 (ignore-deco-flag (cadr proof-and-ignore-deco-flag))
	 (nc-viols (nc-violations proof))
	 (h-deg-viols (h-deg-violations proof))
	 (avar-convention-viols
	  (avar-convention-violations proof ignore-deco-flag))
	 (free-avars (proof-to-free-avars proof))
	 (aconsts (proof-to-aconsts proof))
	 (theorems (list-transform-positive
		       aconsts
		     (lambda (ac) (eq? 'theorem (aconst-to-kind ac)))))
	 (impl-gas (list-transform-positive
		       GLOBAL-ASSUMPTIONS
		     (lambda (ga)
		       (initial-substring? "RewriteGA"(car ga))))))
    (check-proof-aux display-flag proof 0 ignore-deco-flag)
    (if (pair? nc-viols)
	(begin
	  (comment
	   "Incorrect proof: nc-intro with computational variable(s)")
	  (for-each comment (map (lambda (x)
				   (if (var-form? x)
				       (var-to-string x)
				       (avar-to-string x)))
				 nc-viols))))
    (if
     (pair? h-deg-viols)
     (begin
       (comment
	"Proof not suitable for extraction.  h-deg violations at aconst(s)")
       (for-each comment h-deg-viols)))
    (if (pair? avar-convention-viols)
	(begin
	  (comment
	   "Proof does not respect the avar convention.")
	  (do ((l avar-convention-viols (cdr l)))
	      ((null? l))
	    (let* ((pair (car l))
		   (flagged-avar1 (car pair))
		   (flagged-avar2 (cadr pair))
		   (avar1 (cadr flagged-avar1))
		   (avar2 (cadr flagged-avar2)))
	      (comment "The same avar with name "
		       (let ((name (avar-to-name avar1)))
			 (if (string=? "" name)
			     DEFAULT-AVAR-NAME
			     name)		       )
		       " and index "
		       (avar-to-index avar1)
		       " carries the two different formulas")
	      (pp (avar-to-formula avar1))
	      (comment "and")
	      (pp (avar-to-formula avar2))))))
    (comment "Ok, proof is correct.")
    (if (pair? free-avars)
	(comment "Free assumption variables present.")
	(comment "No free assumption variables."))
    (if (pair? impl-gas)
	(comment
	 "Implicit global assumptions possibly used (unproven rewrite rules): "
	 (map car impl-gas))
	(comment
	 "No implicit global assumptions (unproven rewrite rules)."))
    (if (pair? theorems)
	(comment "Theorems used: " (remove-duplicates-wrt
				    string=?
				    (map aconst-to-name theorems)))
	(comment "No theorems used.")))
  *the-non-printing-object*)

;; Code discarded 2021-10-24
;; (define (check-proof display-flag . opt-proof-or-thm-name-and-ignore-deco-flag)
;;   (let* ((proof-and-ignore-deco-flag
;; 	  (cond
;; 	   ((null? opt-proof-or-thm-name-and-ignore-deco-flag)
;; 	    (list (current-proof) #f))
;; 	   ((= 1 (length opt-proof-or-thm-name-and-ignore-deco-flag))
;; 	    (let ((first (car opt-proof-or-thm-name-and-ignore-deco-flag)))
;; 	      (cond ((proof-form? first) (list first #f))
;; 		    ((string? first)
;; 		     (list (theorem-name-to-proof first) #f))
;; 		    ((boolean? first) (list (current-proof) first))
;; 		    (else (myerror "check-proof"
;; 				   "proof or theorem name or boolean expected"
;; 				   first)))))
;; 	   ((= 2 (length opt-proof-or-thm-name-and-ignore-deco-flag)
;; 	       (let ((first (car opt-proof-or-thm-name-and-ignore-deco-flag))
;; 		     (second
;; 		      (cadr opt-proof-or-thm-name-and-ignore-deco-flag)))
;; 		 (cond ((and (proof-form? first) (boolean? second))
;; 			(list first second))
;; 		       ((and (string? first) (boolean? second))
;; 			(list (theorem-name-to-proof first) second))
;; 		       (else (myerror
;; 			      "check-proof"
;; 			      "proof or theorem name and boolean expected"
;; 			      first second))))))
;; 	   (else (myerror "check-proof"
;; 			  "list of length <=2 expected"
;; 			  opt-proof-or-thm-name-and-ignore-deco-flag))))
;; 	 (proof (car proof-and-ignore-deco-flag))
;; 	 (ignore-deco-flag (cadr proof-and-ignore-deco-flag))
;; 	 (nc-viols (nc-violations proof))
;; 	 (h-deg-viols (h-deg-violations proof))
;; 	 (avar-convention-viols
;; 	  (avar-convention-violations proof ignore-deco-flag))
;; 	 (free-avars (proof-to-free-avars proof))
;; 	 (impl-gas (list-transform-positive
;; 		       GLOBAL-ASSUMPTIONS
;; 		     (lambda (ga)
;; 		       (initial-substring? "RewriteGA"(car ga)))))
;; 	 (expl-gas (proof-to-global-assumptions proof)))
;;     (check-proof-aux display-flag proof 0 ignore-deco-flag)
;;     (if (pair? nc-viols)
;; 	(begin
;; 	  (comment
;; 	   "Incorrect proof: nc-intro with computational variable(s)")
;; 	  (for-each comment (map (lambda (x)
;; 				   (if (var-form? x)
;; 				       (var-to-string x)
;; 				       (avar-to-string x)))
;; 				 nc-viols))))
;;     (if
;;      (pair? h-deg-viols)
;;      (begin
;;        (comment
;; 	"Proof not suitable for extraction.  h-deg violations at aconst(s)")
;;        (for-each comment h-deg-viols)))
;;     (if (pair? avar-convention-viols)
;; 	(begin
;; 	  (comment
;; 	   "Proof does not respect the avar convention.")
;; 	  (do ((l avar-convention-viols (cdr l)))
;; 	      ((null? l))
;; 	    (let* ((pair (car l))
;; 		   (flagged-avar1 (car pair))
;; 		   (flagged-avar2 (cadr pair))
;; 		   (avar1 (cadr flagged-avar1))
;; 		   (avar2 (cadr flagged-avar2)))
;; 	      (comment "The same avar with name "
;; 		       (let ((name (avar-to-name avar1)))
;; 			 (if (string=? "" name)
;; 			     DEFAULT-AVAR-NAME
;; 			     name)		       )
;; 		       " and index "
;; 		       (avar-to-index avar1)
;; 		       " carries the two different formulas")
;; 	      (pp (avar-to-formula avar1))
;; 	      (comment "and")
;; 	      (pp (avar-to-formula avar2))))))
;;     (comment "Ok, proof is correct.")
;;     (if (pair? free-avars)
;; 	(comment "Free assumption variables present.")
;; 	(comment "No free assumption variables."))
;;     (if (pair? impl-gas)
;; 	(comment
;; 	 "Implicit global assumptions possibly used (unproven rewrite rules): "
;; 	 (map car impl-gas))
;; 	(comment
;; 	 "No implicit global assumptions (unproven rewrite rules)."))
;;     (if (pair? expl-gas)
;; 	(comment "Explicit global assumptions used: "
;; 		 (map aconst-to-name  expl-gas))
;; 	(comment "No explicit global assumptions used.")))
;;   *the-non-printing-object*)

(define (check-proof-aux display-flag proof n ignore-deco-flag)
  (cond
   ((proof-in-avar-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (avar (proof-in-avar-form-to-avar proof)))
      (if (not (avar? avar)) (myerror "avar expected" avar))
      (let ((avar-fla (avar-to-formula avar)))
	(check-formula fla)
	(check-formula avar-fla)
	(if (not (classical-formula=? fla avar-fla new-ignore-deco-flag))
	    (myerror "equal formulas expected" fla avar-fla))
	(if display-flag
	    (begin
	      (display-comment (make-string n #\.))
	      (dff fla) (display " by assumption ")
	      (display (avar-to-string avar)) (newline))))))
   ((proof-in-aconst-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (aconst (proof-in-aconst-form-to-aconst proof)))
      (check-aconst aconst ignore-deco-flag)
      (let ((aconst-fla (aconst-to-formula aconst)))
	(check-formula fla)
	(check-formula aconst-fla)
	(if (not (classical-formula=? fla aconst-fla new-ignore-deco-flag))
	    (myerror "equal formulas expected" fla aconst-fla))
	(if ;check for correct Elim in case of an n.c. idpc
	 (string=? "Elim" (aconst-to-name aconst))
	 (let* ((kernel (all-allnc-form-to-final-kernel aconst-fla))
		(prems (imp-form-to-premises kernel))
		(concl (imp-form-to-final-conclusion kernel))
		(idpc-fla (if (pair? prems) (car prems)
			      (myerror "imp premises expected in" kernel)))
		(pred (if (predicate-form? idpc-fla)
			  (predicate-form-to-predicate idpc-fla)
			  (myerror "predicate formula expected" idpc-fla)))
		(idpc-name (if (idpredconst-form? pred)
			       (idpredconst-to-name pred)
			       (myerror "idpredconst expected" pred)))
		(clauses (idpredconst-name-to-clauses idpc-name)))
	   (if (and (null? (idpredconst-name-to-opt-alg-name idpc-name))
					;but not one of the special ones
					;allowing arbitrary conclusions
		    (not (member idpc-name '("EqD" "ExNc" "AndNc")))
					;not a one-clause-nc idpc
		    (not (= 1 (length clauses))) ;but with a c.r. conclusion
		    (not (formula-of-nulltype? concl)))
	       (myerror "n.c. conclusion expected" concl
			"in the elimination axiom for an n.c. idpc formula"
			idpc-fla))))
	(if display-flag
	    (begin
	      (display-comment (make-string n #\.))
	      (dff fla)
	      (case (aconst-to-kind aconst)
		((axiom) (display " by axiom "))
		((theorem) (display " by theorem "))
		((global-assumption) (display " by global assumption "))
		(else (myerror "kind of aconst expected"
			       (aconst-to-kind aconst))))
	      (display (aconst-to-name aconst)) (newline))))))
   ((proof-in-imp-intro-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (avar (proof-in-imp-intro-form-to-avar proof))
	   (kernel (proof-in-imp-intro-form-to-kernel proof)))
      (check-proof-aux display-flag kernel (+ n 1) new-ignore-deco-flag)
      (if (not (avar? avar)) (myerror "avar expected" avar))
      (let ((avar-fla (avar-to-formula avar))
	    (kernel-fla (proof-to-formula kernel)))
	(check-formula fla)
	(if (not (classical-formula=? (make-imp avar-fla kernel-fla)
				      fla ignore-deco-flag))
	    (myerror "equal formulas expected"
		     (make-imp avar-fla kernel-fla) fla))
	(if display-flag
	    (begin
	      (display-comment (make-string n #\.))
	      (dff fla) (display " by imp intro ")
	      (display (avar-to-string avar)) (newline))))))
   ((proof-in-imp-elim-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (op (proof-in-imp-elim-form-to-op proof))
	   (op-fla (proof-to-formula op))
	   (arg (proof-in-imp-elim-form-to-arg proof))
	   (arg-fla (proof-to-formula arg))
	   (arg-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? arg-fla))))
      (check-proof-aux display-flag op (+ n 1) new-ignore-deco-flag)
      (check-proof-aux display-flag arg (+ n 1) arg-ignore-deco-flag)
      (check-formula fla)
      (if (not (or (imp-form? op-fla)
		   (and arg-ignore-deco-flag (impnc-form? op-fla))))
	  (myerror "imp form or impnc form with n.c. premise expected"
		   op-fla))
      (if (not (classical-formula=?
		(imp-impnc-form-to-conclusion op-fla)
		fla new-ignore-deco-flag))
	  (myerror "equal formulas expected"
		   (imp-impnc-form-to-conclusion op-fla) fla))
      (if (not (classical-formula=?
		(imp-impnc-form-to-premise op-fla)
		arg-fla arg-ignore-deco-flag))
	  (myerror "equal formulas expected"
		   (imp-impnc-form-to-premise op-fla) arg-fla))
      (if display-flag
	  (begin
	    (display-comment (make-string n #\.))
	    (dff fla) (display " by imp elim") (newline)))))
   ((proof-in-impnc-intro-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (avar (proof-in-impnc-intro-form-to-avar proof))
	   (kernel (proof-in-impnc-intro-form-to-kernel proof))
	   (cvars (proof-to-cvars kernel)))
      (if (and (not (formula-of-nulltype? (proof-to-formula kernel)))
	       (member-wrt avar=? avar cvars))
	  (begin (display-comment "warning: impnc-intro with cvar"
				  (avar-to-string avar))
		 (newline)))
      (check-proof-aux display-flag kernel (+ n 1) new-ignore-deco-flag)
      (if (not (avar? avar)) (myerror "avar expected" avar))
      (let ((avar-fla (avar-to-formula avar))
	    (kernel-fla (proof-to-formula kernel)))
	(check-formula fla)
	(if (not (classical-formula=? (make-impnc avar-fla kernel-fla)
				      fla new-ignore-deco-flag))
	    (myerror "equal formulas expected"
		     (make-impnc avar-fla kernel-fla) fla))
	(if display-flag
	    (begin
	      (display-comment (make-string n #\.))
	      (dff fla) (display " by impnc intro ")
	      (display (avar-to-string avar)) (newline))))))
   ((proof-in-impnc-elim-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (op (proof-in-impnc-elim-form-to-op proof))
	   (op-fla (proof-to-formula op))
	   (arg (proof-in-impnc-elim-form-to-arg proof))
	   (arg-fla (proof-to-formula arg))
	   (arg-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? arg-fla))))
      (check-proof-aux display-flag op (+ n 1) new-ignore-deco-flag)
      (check-proof-aux display-flag arg (+ n 1) #t)
      (check-formula fla)
      (if (not (or (impnc-form? op-fla)
		   (and arg-ignore-deco-flag (imp-form? arg-fla))))
	  (myerror "impnc form or imp form with n.c premise expected" op-fla))
      (if (not (classical-formula=?
		(imp-impnc-form-to-conclusion op-fla) fla
		new-ignore-deco-flag))
	  (myerror
	   "equal formulas expected" (impnc-form-to-conclusion op-fla) fla))
      (if (not (classical-formula=?
		(imp-impnc-form-to-premise op-fla) arg-fla
		arg-ignore-deco-flag))
	  (myerror "equal formulas expected"
		   (imp-impnc-form-to-premise op-fla) arg-fla))
      (if display-flag
	  (begin
	    (display-comment (make-string n #\.))
	    (dff fla) (display " by impnc elim") (newline)))))
   ((proof-in-and-intro-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (left (proof-in-and-intro-form-to-left proof))
	   (right (proof-in-and-intro-form-to-right proof))
	   (left-ignore-deco-flag
	    (or ignore-deco-flag
		(formula-of-nulltype? (proof-to-formula left))))
	   (right-ignore-deco-flag
	    (or ignore-deco-flag
		(formula-of-nulltype? (proof-to-formula right)))))
      (check-proof-aux display-flag left (+ n 1) left-ignore-deco-flag)
      (check-proof-aux display-flag right (+ n 1) right-ignore-deco-flag)
      (check-formula fla)
      (let ((left-fla (proof-to-formula left))
	    (right-fla (proof-to-formula right)))
	(if (not (and-form? fla))
	    (myerror "and form expected" fla))
	(if (not (classical-formula=?
		  left-fla (and-form-to-left fla) left-ignore-deco-flag))
	    (myerror
	     "equal formulas expected" left-fla (and-form-to-left fla)))
	(if (not (classical-formula=?
		  right-fla (and-form-to-right fla) right-ignore-deco-flag))
	    (myerror
	     "equal formulas expected" right-fla (and-form-to-right fla)))
	(if display-flag
	    (begin
	      (display-comment (make-string n #\.))
	      (dff fla) (display " by and intro") (newline))))))
   ((proof-in-and-elim-left-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (kernel (proof-in-and-elim-left-form-to-kernel proof)))
      (check-proof-aux display-flag kernel (+ n 1) new-ignore-deco-flag)
      (check-formula fla)
      (let ((kernel-fla (proof-to-formula kernel)))
	(if (not (and-form? kernel-fla))
	    (myerror "in and-elim and-form expected" kernel-fla))
	(if (not (classical-formula=?
		  (and-form-to-left kernel-fla) fla new-ignore-deco-flag))
	    (myerror "in and-elim formulas do not fit"
		     (and-form-to-left kernel-fla) fla))
	(if display-flag
	    (begin
	      (display-comment (make-string n #\.))
	      (dff fla) (display " by and elim left") (newline))))))
   ((proof-in-and-elim-right-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (kernel (proof-in-and-elim-right-form-to-kernel proof)))
      (check-proof-aux display-flag kernel (+ n 1) new-ignore-deco-flag)
      (check-formula fla)
      (let ((kernel-fla (proof-to-formula kernel)))
	(if (not (and-form? kernel-fla))
	    (myerror "in and-elim and-form expected" kernel-fla))
	(if (not (classical-formula=?
		  (and-form-to-right kernel-fla) fla new-ignore-deco-flag))
	    (myerror "in and-elim formulas do not fit"
		     (and-form-to-right kernel-fla) fla))
	(if display-flag
	    (begin
	      (display-comment (make-string n #\.))
	      (dff fla) (display " by and elim right") (newline))))))
   ((proof-in-all-intro-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
      (check-proof-aux display-flag kernel (+ n 1) new-ignore-deco-flag)
      (check-formula fla)
      (let* ((context (proof-to-context kernel))
	     (avars (context-to-avars context))
	     (formulas (map avar-to-formula avars)))
	(if
	 (and
	  (member var (apply union (map formula-to-free formulas)))
	  (member var (apply union (map formula-to-free
					(map normalize-formula formulas)))))
	 (myerror "variable condition fails for" var)))
      (if (and (not new-ignore-deco-flag) (not (all-form? fla)))
	  (myerror "at all-intro: all form expected" fla))
      (if (and new-ignore-deco-flag (not (all-allnc-form? fla)))
	  (myerror "all or allnc form expected" fla))
      ;; (if (not (all-form? fla))
      ;; 	   (myerror "all form expected" fla))
      (let ((kernel-fla (proof-to-formula kernel)))
	(if (not (classical-formula=?
		  (make-all var kernel-fla) fla new-ignore-deco-flag))
	    (myerror "equal formulas expected"
		     (make-all var kernel-fla) fla)))
      (if display-flag
	  (begin
	    (display-comment (make-string n #\.))
	    (dff fla) (display " by all intro") (newline)))))
   ((proof-in-all-elim-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
      (check-proof-aux display-flag op (+ n 1) new-ignore-deco-flag)
      (check-formula fla)
      (check-term arg)
      (let ((op-fla (proof-to-formula op)))
	(if (and (not new-ignore-deco-flag) (not (all-form? op-fla)))
	    (myerror "at all-elim: all form expected" op-fla))
	(if (and new-ignore-deco-flag (not (all-allnc-form? op-fla)))
	    (myerror "at all-elim: all or allnc form expected" op-fla))
	;; (if (not (all-form? op-fla))
	;;     (myerror "at all-elim: all form expected" op-fla))
	(if (not (equal? (var-to-type (all-form-to-var op-fla))
			 (term-to-type arg)))
	    (myerror "equal types expected of variable"
		     (all-form-to-var op-fla) "and term" arg))
	(if (and (t-deg-one? (var-to-t-deg (all-form-to-var op-fla)))
		 (not (synt-total? arg)))
	    (myerror "degrees of totality do not fit for variable"
		     (all-form-to-var op-fla) "and term" arg))
	(let ((var (all-form-to-var op-fla))
	      (kernel (all-form-to-kernel op-fla)))
	  (if (and (term-in-var-form? arg)
		   (equal? var (term-in-var-form-to-var arg)))
	      (if (not (classical-formula=? fla kernel new-ignore-deco-flag))
		  (myerror "equal formulas expected" fla kernel))
	      (if (not (classical-formula=?
			fla (formula-subst kernel var arg)
			new-ignore-deco-flag))
		  (myerror "equal formulas expected"
			   fla (formula-subst kernel var arg)))))
	(if display-flag
	    (begin
	      (display-comment (make-string (+ n 1) #\.))
	      (display-term arg) (newline)
	      (display-comment (make-string n #\.))
	      (dff fla) (display " by all elim") (newline))))))
   ((proof-in-allnc-intro-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (var (proof-in-allnc-intro-form-to-var proof))
	   (kernel (proof-in-allnc-intro-form-to-kernel proof))
	   (context (proof-to-context kernel))
	   (cvars (proof-to-cvars kernel))
	   (avars (context-to-avars context))
	   (formulas (map avar-to-formula avars))
	   (free (apply union (map formula-to-free formulas))))
      (if
       (or (and
	    (member var (apply union (map formula-to-free formulas)))
	    (member var (apply union (map formula-to-free
					  (map normalize-formula formulas)))))
	   (and (not (formula-of-nulltype? (proof-to-formula kernel)))
		(member var cvars)))
       (begin (display-comment "warning: allnc-intro with cvar"
			       (var-to-string var))
	      (newline)))
      (check-proof-aux display-flag kernel (+ n 1) new-ignore-deco-flag)
      (check-formula fla)
      (if (and (not new-ignore-deco-flag) (not (allnc-form? fla)))
	  (myerror "at allnc-intro: allnc form expected" fla))
      (if (and new-ignore-deco-flag (not (all-allnc-form? fla)))
	  (myerror "all or allnc form expected" fla))
      ;; (if (not (allnc-form? fla))
      ;; 	   (myerror "allnc form expected" fla))
      (let ((kernel-fla (proof-to-formula kernel)))
	(if (not (classical-formula=?
		  (make-allnc var kernel-fla) fla new-ignore-deco-flag))
	    (myerror "equal formulas expected"
		     (make-allnc var kernel-fla) fla)))
      (if display-flag
	  (begin
	    (display-comment (make-string n #\.))
	    (dff fla) (display " by allnc intro") (newline)))))
   ((proof-in-allnc-elim-form? proof)
    (let* ((fla (proof-to-formula proof))
	   (new-ignore-deco-flag
	    (or ignore-deco-flag (formula-of-nulltype? fla)))
	   (op (proof-in-allnc-elim-form-to-op proof))
	   (arg (proof-in-allnc-elim-form-to-arg proof)))
      (check-proof-aux display-flag op (+ n 1) new-ignore-deco-flag)
      (check-formula fla)
      (check-term arg)
      (let ((op-fla (proof-to-formula op)))
	(if (and (not new-ignore-deco-flag) (not (allnc-form? op-fla)))
	    (myerror "at allnc-elim: allnc form expected" op-fla))
	(if (and new-ignore-deco-flag (not (all-allnc-form? op-fla)))
	    (myerror "at allnc-elim: all or allnc form expected" op-fla))
	;; (if (not (allnc-form? op-fla))
	;;     (myerror "allnc form expected" op-fla))
	(if (not (equal? (var-to-type (allnc-form-to-var op-fla))
			 (term-to-type arg)))
	    (myerror "equal types expected of variable"
		     (allnc-form-to-var op-fla) "and term" arg))
	(if (and (t-deg-one? (var-to-t-deg (allnc-form-to-var op-fla)))
		 (not (synt-total? arg)))
	    (myerror "degrees of totality do not fit for variable"
		     (allnc-form-to-var op-fla) "and term" arg))
	(let ((op-var (allnc-form-to-var op-fla))
	      (op-kernel (allnc-form-to-kernel op-fla)))
	  (if (and (term-in-var-form? arg)
		   (equal? op-var (term-in-var-form-to-var arg)))
	      (if (not (classical-formula=? fla op-kernel
					    new-ignore-deco-flag))
		  (myerror "equal formulas expected" fla op-kernel))
	      (if (not (classical-formula=?
			fla (formula-subst op-kernel op-var arg)
			new-ignore-deco-flag))
		  (myerror "equal formulas expected"
			   fla (formula-subst op-kernel op-var arg)))))
	(if display-flag
	    (begin
	      (display-comment (make-string (+ n 1) #\.))
	      (display-term arg) (newline)
	      (display-comment (make-string n #\.))
	      (dff fla) (display " by allnc elim") (newline))))))
   (else (myerror "proof tag expected"
		  (tag proof)))))

(define (cdp . opt-proof-or-thm-name-and-ignore-deco-flag)
  (apply check-proof #t opt-proof-or-thm-name-and-ignore-deco-flag))

(define (cp . opt-proof-or-thm-name-and-ignore-deco-flag)
  (apply check-proof #f opt-proof-or-thm-name-and-ignore-deco-flag))

;; Code discarded 2021-10-18
;; (define (check-and-display-proof . opt-proof-or-thm-name-and-ignore-deco-flag)
;;   (let* ((proof-and-ignore-deco-flag
;; 	  (cond
;; 	   ((null? opt-proof-or-thm-name-and-ignore-deco-flag)
;; 	    (list (current-proof) #f))
;; 	   ((= 1 (length opt-proof-or-thm-name-and-ignore-deco-flag))
;; 	    (let ((first (car opt-proof-or-thm-name-and-ignore-deco-flag)))
;; 	      (cond ((proof-form? first) (list first #f))
;; 		    ((string? first)
;; 		     (list (theorem-name-to-proof first) #f))
;; 		    ((boolean? first) (list (current-proof) first))
;; 		    (else (myerror "check-and-display-proof"
;; 				   "proof or theorem name or boolean expected"
;; 				   first)))))
;; 	   ((= 2 (length opt-proof-or-thm-name-and-ignore-deco-flag)
;; 	       (let ((first (car opt-proof-or-thm-name-and-ignore-deco-flag))
;; 		     (second
;; 		      (cadr opt-proof-or-thm-name-and-ignore-deco-flag)))
;; 		 (cond ((and (proof-form? first) (boolean? second))
;; 			(list first second))
;; 		       ((and (string? first) (boolean? second))
;; 			(list (theorem-name-to-proof first) second))
;; 		       (else (myerror
;; 			      "check-and-display-proof"
;; 			      "proof or theorem name and boolean expected"
;; 			      first second))))))
;; 	   (else (myerror "check-and-display-proof"
;; 			  "list of length <=2 expected"
;; 			  opt-proof-or-thm-name-and-ignore-deco-flag))))
;; 	 (proof (car proof-and-ignore-deco-flag))
;; 	 (ignore-deco-flag (cadr proof-and-ignore-deco-flag))
;; 	 (nc-viols (nc-violations proof))
;; 	 (h-deg-viols (h-deg-violations proof))
;; 	 (avar-convention-viols
;; 	  (avar-convention-violations proof ignore-deco-flag)))
;;     (check-and-display-proof-aux proof 0 ignore-deco-flag)
;;     (if (pair? nc-viols)
;; 	(begin
;; 	  (comment
;; 	   "Incorrect proof: nc-intro with computational variable(s)")
;; 	  (for-each comment (map (lambda (x)
;; 				   (if (var-form? x)
;; 				       (var-to-string x)
;; 				       (avar-to-string x)))
;; 				 nc-viols))))
;;     (if
;;      (pair? h-deg-viols)
;;      (begin
;;        (comment
;; 	"Proof not suitable for extraction.  h-deg violations at aconst(s)")
;;        (for-each comment h-deg-viols)))
;;     (if (pair? avar-convention-viols)
;; 	(begin
;; 	  (comment
;; 	   "Proof does not respect the avar convention.")
;; 	  (do ((l avar-convention-viols (cdr l)))
;; 	      ((null? l))
;; 	    (let* ((pair (car l))
;; 		   (flagged-avar1 (car pair))
;; 		   (flagged-avar2 (cadr pair))
;; 		   (avar1 (cadr flagged-avar1))
;; 		   (avar2 (cadr flagged-avar2)))
;; 	      (comment "The same avar with name "
;; 		       (let ((name (avar-to-name avar1)))
;; 			 (if (string=? "" name)
;; 			     DEFAULT-AVAR-NAME
;; 			     name)		       )
;; 		       " and index "
;; 		       (avar-to-index avar1)
;; 		       " carries the two different formulas")
;; 	      (pp (avar-to-formula avar1))
;; 	      (comment "and")
;; 	      (pp (avar-to-formula avar2))))))
;;     *the-non-printing-object*))

;; (define (check-and-display-proof-aux proof n ignore-deco-flag)
;;   (if
;;    COMMENT-FLAG
;;    (cond
;;     ((proof-in-avar-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (avar (proof-in-avar-form-to-avar proof)))
;;        (if (not (avar? avar)) (myerror "avar expected" avar))
;;        (let ((avar-fla (avar-to-formula avar)))
;; 	 (check-formula fla)
;; 	 (check-formula avar-fla)
;; 	 (if (not (classical-formula=? fla avar-fla new-ignore-deco-flag))
;; 	     (myerror "equal formulas expected" fla avar-fla))
;; 	 (if CDP-COMMENT-FLAG
;; 	     (begin
;; 	       (display-comment (make-string n #\.))
;; 	       (dff fla) (display " by assumption ")
;; 	       (display (avar-to-string avar)) (newline))))))
;;     ((proof-in-aconst-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (aconst (proof-in-aconst-form-to-aconst proof)))
;;        (check-aconst aconst ignore-deco-flag)
;;        (let ((aconst-fla (aconst-to-formula aconst)))
;; 	 (check-formula fla)
;; 	 (check-formula aconst-fla)
;; 	 (if (not (classical-formula=? fla aconst-fla new-ignore-deco-flag))
;; 	     (myerror "equal formulas expected" fla aconst-fla))
;; 	 (if ;check for correct Elim in case of an n.c. idpc
;; 	  (string=? "Elim" (aconst-to-name aconst))
;; 	  (let* ((kernel (all-allnc-form-to-final-kernel aconst-fla))
;; 		 (prems (imp-form-to-premises kernel))
;; 		 (concl (imp-form-to-final-conclusion kernel))
;; 		 (idpc-fla (if (pair? prems) (car prems)
;; 			       (myerror "imp premises expected in" kernel)))
;; 		 (pred (if (predicate-form? idpc-fla)
;; 			   (predicate-form-to-predicate idpc-fla)
;; 			   (myerror "predicate formula expected" idpc-fla)))
;; 		 (idpc-name (if (idpredconst-form? pred)
;; 				(idpredconst-to-name pred)
;; 				(myerror "idpredconst expected" pred)))
;; 		 (clauses (idpredconst-name-to-clauses idpc-name)))
;; 	    (if (and (null? (idpredconst-name-to-opt-alg-name idpc-name))
;; 					;but not one of the special ones
;; 					;allowing arbitrary conclusions
;; 		     (not (member idpc-name '("EqD" "ExNc" "AndNc")))
;; 					;not a one-clause-nc idpc
;; 		     (not (= 1 (length clauses))) ;but with a c.r. conclusion
;; 		     (not (formula-of-nulltype? concl)))
;; 		(myerror "n.c. conclusion expected" concl
;; 			 "in the elimination axiom for an n.c. idpc formula"
;; 			 idpc-fla))))
;; 	 (if CDP-COMMENT-FLAG
;; 	     (begin
;; 	       (display-comment (make-string n #\.))
;; 	       (dff fla)
;; 	       (case (aconst-to-kind aconst)
;; 		 ((axiom) (display " by axiom "))
;; 		 ((theorem) (display " by theorem "))
;; 		 ((global-assumption) (display " by global assumption "))
;; 		 (else (myerror "kind of aconst expected"
;; 				(aconst-to-kind aconst))))
;; 	       (display (aconst-to-name aconst)) (newline))))))
;;     ((proof-in-imp-intro-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (avar (proof-in-imp-intro-form-to-avar proof))
;; 	    (kernel (proof-in-imp-intro-form-to-kernel proof)))
;;        (check-and-display-proof-aux kernel (+ n 1) new-ignore-deco-flag)
;;        (if (not (avar? avar)) (myerror "avar expected" avar))
;;        (let ((avar-fla (avar-to-formula avar))
;; 	     (kernel-fla (proof-to-formula kernel)))
;; 	 (check-formula fla)
;; 	 (if (not (classical-formula=? (make-imp avar-fla kernel-fla)
;; 				       fla ignore-deco-flag))
;; 	     (myerror "equal formulas expected"
;; 		      (make-imp avar-fla kernel-fla) fla))
;; 	 (if CDP-COMMENT-FLAG
;; 	     (begin
;; 	       (display-comment (make-string n #\.))
;; 	       (dff fla) (display " by imp intro ")
;; 	       (display (avar-to-string avar)) (newline))))))
;;     ((proof-in-imp-elim-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (op (proof-in-imp-elim-form-to-op proof))
;; 	    (op-fla (proof-to-formula op))
;; 	    (arg (proof-in-imp-elim-form-to-arg proof))
;; 	    (arg-fla (proof-to-formula arg))
;; 	    (arg-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? arg-fla))))
;;        (check-and-display-proof-aux op (+ n 1) new-ignore-deco-flag)
;;        (check-and-display-proof-aux arg (+ n 1) arg-ignore-deco-flag)
;;        (check-formula fla)
;;        (if (not (or (imp-form? op-fla)
;; 		    (and arg-ignore-deco-flag (impnc-form? op-fla))))
;; 	   (myerror "imp form or impnc form with n.c. premise expected"
;; 		    op-fla))
;;        (if (not (classical-formula=?
;; 		 (imp-impnc-form-to-conclusion op-fla)
;; 		 fla new-ignore-deco-flag))
;; 	   (myerror "equal formulas expected"
;; 		    (imp-impnc-form-to-conclusion op-fla) fla))
;;        (if (not (classical-formula=?
;; 		 (imp-impnc-form-to-premise op-fla)
;; 		 arg-fla arg-ignore-deco-flag))
;; 	   (myerror "equal formulas expected"
;; 		    (imp-impnc-form-to-premise op-fla) arg-fla))
;;        (if CDP-COMMENT-FLAG
;; 	   (begin
;; 	     (display-comment (make-string n #\.))
;; 	     (dff fla) (display " by imp elim") (newline)))))
;;     ((proof-in-impnc-intro-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (avar (proof-in-impnc-intro-form-to-avar proof))
;; 	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
;; 	    (cvars (proof-to-cvars kernel)))
;;        (if (and (not (formula-of-nulltype? (proof-to-formula kernel)))
;; 		(member-wrt avar=? avar cvars))
;; 	   (begin (display-comment "warning: impnc-intro with cvar"
;; 				   (avar-to-string avar))
;; 		  (newline)))
;;        (check-and-display-proof-aux kernel (+ n 1) new-ignore-deco-flag)
;;        (if (not (avar? avar)) (myerror "avar expected" avar))
;;        (let ((avar-fla (avar-to-formula avar))
;; 	     (kernel-fla (proof-to-formula kernel)))
;; 	 (check-formula fla)
;; 	 (if (not (classical-formula=? (make-impnc avar-fla kernel-fla)
;; 				       fla new-ignore-deco-flag))
;; 	     (myerror "equal formulas expected"
;; 		      (make-impnc avar-fla kernel-fla) fla))
;; 	 (if CDP-COMMENT-FLAG
;; 	     (begin
;; 	       (display-comment (make-string n #\.))
;; 	       (dff fla) (display " by impnc intro ")
;; 	       (display (avar-to-string avar)) (newline))))))
;;     ((proof-in-impnc-elim-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (op (proof-in-impnc-elim-form-to-op proof))
;; 	    (op-fla (proof-to-formula op))
;; 	    (arg (proof-in-impnc-elim-form-to-arg proof))
;; 	    (arg-fla (proof-to-formula arg))
;; 	    (arg-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? arg-fla))))
;;        (check-and-display-proof-aux op (+ n 1) new-ignore-deco-flag)
;;        (check-and-display-proof-aux arg (+ n 1) #t)
;;        (check-formula fla)
;;        (if (not (or (impnc-form? op-fla)
;; 		    (and arg-ignore-deco-flag (imp-form? arg-fla))))
;; 	   (myerror "impnc form or imp form with n.c premise expected" op-fla))
;;        (if (not (classical-formula=?
;; 		 (imp-impnc-form-to-conclusion op-fla) fla
;; 		 new-ignore-deco-flag))
;; 	   (myerror
;; 	    "equal formulas expected" (impnc-form-to-conclusion op-fla) fla))
;;        (if (not (classical-formula=?
;; 		 (imp-impnc-form-to-premise op-fla) arg-fla
;; 		 arg-ignore-deco-flag))
;; 	   (myerror "equal formulas expected"
;; 		    (imp-impnc-form-to-premise op-fla) arg-fla))
;;        (if CDP-COMMENT-FLAG
;; 	   (begin
;; 	     (display-comment (make-string n #\.))
;; 	     (dff fla) (display " by impnc elim") (newline)))))
;;     ((proof-in-and-intro-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (left (proof-in-and-intro-form-to-left proof))
;; 	    (right (proof-in-and-intro-form-to-right proof))
;; 	    (left-ignore-deco-flag
;; 	     (or ignore-deco-flag
;; 		 (formula-of-nulltype? (proof-to-formula left))))
;; 	    (right-ignore-deco-flag
;; 	     (or ignore-deco-flag
;; 		 (formula-of-nulltype? (proof-to-formula right)))))
;;        (check-and-display-proof-aux left (+ n 1) left-ignore-deco-flag)
;;        (check-and-display-proof-aux right (+ n 1) right-ignore-deco-flag)
;;        (check-formula fla)
;;        (let ((left-fla (proof-to-formula left))
;; 	     (right-fla (proof-to-formula right)))
;; 	 (if (not (and-form? fla))
;; 	     (myerror "and form expected" fla))
;; 	 (if (not (classical-formula=?
;; 		   left-fla (and-form-to-left fla) left-ignore-deco-flag))
;; 	     (myerror
;; 	      "equal formulas expected" left-fla (and-form-to-left fla)))
;; 	 (if (not (classical-formula=?
;; 		   right-fla (and-form-to-right fla) right-ignore-deco-flag))
;; 	     (myerror
;; 	      "equal formulas expected" right-fla (and-form-to-right fla)))
;; 	 (if CDP-COMMENT-FLAG
;; 	     (begin
;; 	       (display-comment (make-string n #\.))
;; 	       (dff fla) (display " by and intro") (newline))))))
;;     ((proof-in-and-elim-left-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (kernel (proof-in-and-elim-left-form-to-kernel proof)))
;;        (check-and-display-proof-aux kernel (+ n 1) new-ignore-deco-flag)
;;        (check-formula fla)
;;        (let ((kernel-fla (proof-to-formula kernel)))
;; 	 (if (not (and-form? kernel-fla))
;; 	     (myerror "in and-elim and-form expected" kernel-fla))
;; 	 (if (not (classical-formula=?
;; 		   (and-form-to-left kernel-fla) fla new-ignore-deco-flag))
;; 	     (myerror "in and-elim formulas do not fit"
;; 		      (and-form-to-left kernel-fla) fla))
;; 	 (if CDP-COMMENT-FLAG
;; 	     (begin
;; 	       (display-comment (make-string n #\.))
;; 	       (dff fla) (display " by and elim left") (newline))))))
;;     ((proof-in-and-elim-right-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (kernel (proof-in-and-elim-right-form-to-kernel proof)))
;;        (check-and-display-proof-aux kernel (+ n 1) new-ignore-deco-flag)
;;        (check-formula fla)
;;        (let ((kernel-fla (proof-to-formula kernel)))
;; 	 (if (not (and-form? kernel-fla))
;; 	     (myerror "in and-elim and-form expected" kernel-fla))
;; 	 (if (not (classical-formula=?
;; 		   (and-form-to-right kernel-fla) fla new-ignore-deco-flag))
;; 	     (myerror "in and-elim formulas do not fit"
;; 		      (and-form-to-right kernel-fla) fla))
;; 	 (if CDP-COMMENT-FLAG
;; 	     (begin
;; 	       (display-comment (make-string n #\.))
;; 	       (dff fla) (display " by and elim right") (newline))))))
;;     ((proof-in-all-intro-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (var (proof-in-all-intro-form-to-var proof))
;; 	    (kernel (proof-in-all-intro-form-to-kernel proof)))
;;        (check-and-display-proof-aux kernel (+ n 1) new-ignore-deco-flag)
;;        (check-formula fla)
;;        (let* ((context (proof-to-context kernel))
;; 	      (avars (context-to-avars context))
;; 	      (formulas (map avar-to-formula avars)))
;; 	 (if
;; 	  (and
;; 	   (member var (apply union (map formula-to-free formulas)))
;; 	   (member var (apply union (map formula-to-free
;; 					 (map normalize-formula formulas)))))
;; 	  (myerror "variable condition fails for" var)))
;;        (if (and (not new-ignore-deco-flag) (not (all-form? fla)))
;; 	   (myerror "at all-intro: all form expected" fla))
;;        (if (and new-ignore-deco-flag (not (all-allnc-form? fla)))
;; 	   (myerror "all or allnc form expected" fla))
;;        ;; (if (not (all-form? fla))
;;        ;; 	   (myerror "all form expected" fla))
;;        (let ((kernel-fla (proof-to-formula kernel)))
;; 	 (if (not (classical-formula=?
;; 		   (make-all var kernel-fla) fla new-ignore-deco-flag))
;; 	     (myerror "equal formulas expected"
;; 		      (make-all var kernel-fla) fla)))
;;        (if CDP-COMMENT-FLAG
;; 	   (begin
;; 	     (display-comment (make-string n #\.))
;; 	     (dff fla) (display " by all intro") (newline)))))
;;     ((proof-in-all-elim-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (op (proof-in-all-elim-form-to-op proof))
;; 	    (arg (proof-in-all-elim-form-to-arg proof)))
;;        (check-and-display-proof-aux op (+ n 1) new-ignore-deco-flag)
;;        (check-formula fla)
;;        (check-term arg)
;;        (let ((op-fla (proof-to-formula op)))
;; 	 (if (and (not new-ignore-deco-flag) (not (all-form? op-fla)))
;; 	     (myerror "at all-elim: all form expected" op-fla))
;; 	 (if (and new-ignore-deco-flag (not (all-allnc-form? op-fla)))
;; 	     (myerror "at all-elim: all or allnc form expected" op-fla))
;; 	 ;; (if (not (all-form? op-fla))
;; 	 ;;     (myerror "at all-elim: all form expected" op-fla))
;; 	 (if (not (equal? (var-to-type (all-form-to-var op-fla))
;; 			  (term-to-type arg)))
;; 	     (myerror "equal types expected of variable"
;; 		      (all-form-to-var op-fla) "and term" arg))
;; 	 (if (and (t-deg-one? (var-to-t-deg (all-form-to-var op-fla)))
;; 		  (not (synt-total? arg)))
;; 	     (myerror "degrees of totality do not fit for variable"
;; 		      (all-form-to-var op-fla) "and term" arg))
;; 	 (let ((var (all-form-to-var op-fla))
;; 	       (kernel (all-form-to-kernel op-fla)))
;; 	   (if (and (term-in-var-form? arg)
;; 		    (equal? var (term-in-var-form-to-var arg)))
;; 	       (if (not (classical-formula=? fla kernel new-ignore-deco-flag))
;; 		   (myerror "equal formulas expected" fla kernel))
;; 	       (if (not (classical-formula=?
;; 			 fla (formula-subst kernel var arg)
;; 			 new-ignore-deco-flag))
;; 		   (myerror "equal formulas expected"
;; 			    fla (formula-subst kernel var arg)))))
;; 	 (if CDP-COMMENT-FLAG
;; 	     (begin
;; 	       (display-comment (make-string (+ n 1) #\.))
;; 	       (display-term arg) (newline)
;; 	       (display-comment (make-string n #\.))
;; 	       (dff fla) (display " by all elim") (newline))))))
;;     ((proof-in-allnc-intro-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (var (proof-in-allnc-intro-form-to-var proof))
;; 	    (kernel (proof-in-allnc-intro-form-to-kernel proof))
;; 	    (context (proof-to-context kernel))
;; 	    (cvars (proof-to-cvars kernel))
;; 	    (avars (context-to-avars context))
;; 	    (formulas (map avar-to-formula avars))
;; 	    (free (apply union (map formula-to-free formulas))))
;;        (if
;; 	(or (and
;; 	     (member var (apply union (map formula-to-free formulas)))
;; 	     (member var (apply union (map formula-to-free
;; 					   (map normalize-formula formulas)))))
;; 	    (and (not (formula-of-nulltype? (proof-to-formula kernel)))
;; 		 (member var cvars)))
;; 	(begin (display-comment "warning: allnc-intro with cvar"
;; 				(var-to-string var))
;; 	       (newline)))
;;        (check-and-display-proof-aux kernel (+ n 1) new-ignore-deco-flag)
;;        (check-formula fla)
;;        (if (and (not new-ignore-deco-flag) (not (allnc-form? fla)))
;; 	   (myerror "at allnc-intro: allnc form expected" fla))
;;        (if (and new-ignore-deco-flag (not (all-allnc-form? fla)))
;; 	   (myerror "all or allnc form expected" fla))
;;        ;; (if (not (allnc-form? fla))
;;        ;; 	   (myerror "allnc form expected" fla))
;;        (let ((kernel-fla (proof-to-formula kernel)))
;; 	 (if (not (classical-formula=?
;; 		   (make-allnc var kernel-fla) fla new-ignore-deco-flag))
;; 	     (myerror "equal formulas expected"
;; 		      (make-allnc var kernel-fla) fla)))
;;        (if CDP-COMMENT-FLAG
;; 	   (begin
;; 	     (display-comment (make-string n #\.))
;; 	     (dff fla) (display " by allnc intro") (newline)))))
;;     ((proof-in-allnc-elim-form? proof)
;;      (let* ((fla (proof-to-formula proof))
;; 	    (new-ignore-deco-flag
;; 	     (or ignore-deco-flag (formula-of-nulltype? fla)))
;; 	    (op (proof-in-allnc-elim-form-to-op proof))
;; 	    (arg (proof-in-allnc-elim-form-to-arg proof)))
;;        (check-and-display-proof-aux op (+ n 1) new-ignore-deco-flag)
;;        (check-formula fla)
;;        (check-term arg)
;;        (let ((op-fla (proof-to-formula op)))
;; 	 (if (and (not new-ignore-deco-flag) (not (allnc-form? op-fla)))
;; 	     (myerror "at allnc-elim: allnc form expected" op-fla))
;; 	 (if (and new-ignore-deco-flag (not (all-allnc-form? op-fla)))
;; 	     (myerror "at allnc-elim: all or allnc form expected" op-fla))
;; 	 ;; (if (not (allnc-form? op-fla))
;; 	 ;;     (myerror "allnc form expected" op-fla))
;; 	 (if (not (equal? (var-to-type (allnc-form-to-var op-fla))
;; 			  (term-to-type arg)))
;; 	     (myerror "equal types expected of variable"
;; 		      (allnc-form-to-var op-fla) "and term" arg))
;; 	 (if (and (t-deg-one? (var-to-t-deg (allnc-form-to-var op-fla)))
;; 		  (not (synt-total? arg)))
;; 	     (myerror "degrees of totality do not fit for variable"
;; 		      (allnc-form-to-var op-fla) "and term" arg))
;; 	 (let ((op-var (allnc-form-to-var op-fla))
;; 	       (op-kernel (allnc-form-to-kernel op-fla)))
;; 	   (if (and (term-in-var-form? arg)
;; 		    (equal? op-var (term-in-var-form-to-var arg)))
;; 	       (if (not (classical-formula=? fla op-kernel
;; 					     new-ignore-deco-flag))
;; 		   (myerror "equal formulas expected" fla op-kernel))
;; 	       (if (not (classical-formula=?
;; 			 fla (formula-subst op-kernel op-var arg)
;; 			 new-ignore-deco-flag))
;; 		   (myerror "equal formulas expected"
;; 			    fla (formula-subst op-kernel op-var arg)))))
;; 	 (if CDP-COMMENT-FLAG
;; 	     (begin
;; 	       (display-comment (make-string (+ n 1) #\.))
;; 	       (display-term arg) (newline)
;; 	       (display-comment (make-string n #\.))
;; 	       (dff fla) (display " by allnc elim") (newline))))))
;;     (else (myerror "proof tag expected"
;; 		   (tag proof))))))

;; (define cdp check-and-display-proof)

;; (define (check-proof . opt-proof-or-thm-name-and-ignore-deco-flag)
;;   (if COMMENT-FLAG
;;       (begin 
;; 	(set! COMMENT-FLAG #f)
;; 	(apply check-and-display-proof
;; 	       opt-proof-or-thm-name-and-ignore-deco-flag)
;; 	(set! COMMENT-FLAG #t)
;; 	(comment "ok, proof is correct."))
;;       (begin
;; 	(apply check-and-display-proof
;; 	       opt-proof-or-thm-name-and-ignore-deco-flag)
;; 	(set! COMMENT-FLAG #t)
;; 	(comment "ok, proof is correct.")
;; 	(set! COMMENT-FLAG #f))))

;; (define cp check-proof)

;; A flagged avar is a list (#t avar) or (#f avar).  The entries #t or
;; #f indicate whether this occurrence of an avar is above a c.i.
;; formula in a proof or not.

(define (flagged-avar-full=? flagged-avar1 flagged-avar2)
  (let* ((flag1 (car flagged-avar1))
	 (avar1 (cadr flagged-avar1))
	 (flag2 (car flagged-avar2))
	 (avar2 (cadr flagged-avar2)))
    (if (or flag1 flag2)
	(avar-full=? avar1 avar2 #t) ;ignore-deco-flag set to true
	(avar-full=? avar1 avar2 #f))))

(define (proof-to-flagged-free-and-bound-avars proof ignore-deco-flag)
  (case (tag proof)
    ((proof-in-avar-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (avar (proof-in-avar-form-to-avar proof))
	    (flagged-avar (list new-ignore-deco-flag avar)))
       (list flagged-avar)))
    ((proof-in-aconst-form) '())
    ((proof-in-imp-intro-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (avar (proof-in-imp-intro-form-to-avar proof))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (prev (proof-to-flagged-free-and-bound-avars
		   kernel new-ignore-deco-flag)))
       (union-wrt
	flagged-avar-full=? (list (list new-ignore-deco-flag avar)) prev)))
    ((proof-in-imp-elim-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof))
	    (arg-ignore-deco-flag
	     (or ignore-deco-flag
		 (formula-of-nulltype? (proof-to-formula arg))))
	    (prev1 (proof-to-flagged-free-and-bound-avars
		    op new-ignore-deco-flag))
	    (prev2 (proof-to-flagged-free-and-bound-avars
		    arg arg-ignore-deco-flag)))
       (union-wrt flagged-avar-full=? prev1 prev2)))
    ((proof-in-impnc-intro-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (avar (proof-in-impnc-intro-form-to-avar proof))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (prev (proof-to-flagged-free-and-bound-avars
		   kernel new-ignore-deco-flag)))
       (union-wrt
	flagged-avar-full=? (list (list new-ignore-deco-flag avar)) prev)))
    ((proof-in-impnc-elim-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof))
	    (prev1 (proof-to-flagged-free-and-bound-avars
		    op new-ignore-deco-flag))
	    (prev2 (proof-to-flagged-free-and-bound-avars arg #t)))
       (union-wrt flagged-avar-full=? prev1 prev2)))
    ((proof-in-and-intro-form)
     (let* ((fla (proof-to-formula proof))
	    (left (proof-in-and-intro-form-to-left proof))
	    (right (proof-in-and-intro-form-to-right proof))
	    (left-ignore-deco-flag
	     (or ignore-deco-flag
		 (formula-of-nulltype? (proof-to-formula left))))
	    (right-ignore-deco-flag
	     (or ignore-deco-flag
		 (formula-of-nulltype? (proof-to-formula right))))
	    (prev1 (proof-to-flagged-free-and-bound-avars
		    left left-ignore-deco-flag))
	    (prev2 (proof-to-flagged-free-and-bound-avars
		    right right-ignore-deco-flag)))
       (union-wrt flagged-avar-full=? prev1 prev2)))
    ((proof-in-and-elim-left-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (proof-to-flagged-free-and-bound-avars kernel new-ignore-deco-flag)))
    ((proof-in-and-elim-right-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (proof-to-flagged-free-and-bound-avars kernel new-ignore-deco-flag)))
    ((proof-in-all-intro-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (kernel (proof-in-all-intro-form-to-kernel proof)))
       (proof-to-flagged-free-and-bound-avars kernel new-ignore-deco-flag)))
    ((proof-in-all-elim-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (op (proof-in-all-elim-form-to-op proof)))
       (proof-to-flagged-free-and-bound-avars op new-ignore-deco-flag)))
    ((proof-in-allnc-intro-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (proof-to-flagged-free-and-bound-avars kernel new-ignore-deco-flag)))
    ((proof-in-allnc-elim-form)
     (let* ((fla (proof-to-formula proof))
	    (new-ignore-deco-flag
	     (or ignore-deco-flag (formula-of-nulltype? fla)))
	    (op (proof-in-allnc-elim-form-to-op proof)))
       (proof-to-flagged-free-and-bound-avars op new-ignore-deco-flag)))
    (else (myerror "proof-to-flagged-free-and-bound-avars" "proof tag expected"
		   (tag proof)))))

(define (avar-convention-violations proof . opt-ignore-deco-flag)
  (let* ((ignore-deco-flag (if (pair? opt-ignore-deco-flag)
			       (car opt-ignore-deco-flag)
			       #f))
	 (flagged-free-and-bound-avars
	  (proof-to-flagged-free-and-bound-avars proof ignore-deco-flag)))
    (duplicates-wrt flagged-avar-full=? flagged-free-and-bound-avars)))

;; (define CDP-COMMENT-FLAG #t)

;; 10-6. Classical logic
;; =====================

;; (proof-of-stab-at formula) generates a proof of ((A -> F) -> F) -> A.
;; For F, T one takes the obvious proof, and for other atomic formulas
;; the proof using cases on booleans.  For all other prime or ex
;; formulas one takes an instance of the global assumption Stab:
;; ((Pvar -> F) -> F) -> Pvar.

(define (proof-of-stab-at formula) ;formula must be unfolded
  (case (tag formula)
    ((atom predicate ex)
     (cond
      ((equal? falsity formula)
;;                                    u2:F
;;                                   --------u2
;;              u1:(F -> F) -> F      F -> F
;;              ----------------------------
;;                              F

       (let ((u1 (formula-to-new-avar (make-negation (make-negation falsity))))
	     (u2 (formula-to-new-avar falsity)))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-imp-elim-form
	      (make-proof-in-avar-form u1)
	      (make-proof-in-imp-intro-form
	       u2 (make-proof-in-avar-form u2))))))
      ((equal? truth formula)
       (let ((u1 (formula-to-new-avar (make-negation (make-negation truth)))))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-aconst-form truth-aconst))))
      ((atom-form? formula)
       (let ((kernel (atom-form-to-kernel formula)))
	 (if (not (synt-total? kernel))
	     (myerror "proof-of-stab-at" "total kernel expected" kernel))
	 (mk-proof-in-elim-form
	  (make-proof-in-aconst-form
	   (all-formula-to-cases-aconst
	    (pf "all boole(((boole -> F) -> F) -> boole)")))
	  kernel
	  (make-proof-in-imp-intro-form
	   (formula-to-new-avar (make-negation (make-negation truth)))
	   (make-proof-in-aconst-form truth-aconst))
	  (let ((u1 (formula-to-new-avar
		     (make-negation (make-negation falsity))))
		(u2 (formula-to-new-avar falsity)))
	    (make-proof-in-imp-intro-form
	     u1 (make-proof-in-imp-elim-form
		 (make-proof-in-avar-form u1)
		 (make-proof-in-imp-intro-form
		  u2 (make-proof-in-avar-form u2))))))))
      (else
       (let* ((aconst (global-assumption-name-to-aconst "Stab"))
	      (stab-formula (aconst-to-uninst-formula aconst))
	      (pvars (formula-to-pvars stab-formula))
	      (pvar (if (pair? pvars) (car pvars)
			(myerror
			 "proof-to-stab-at" "stab-formula with pvars expected"
			 stab-formula)))
	      (cterm (make-cterm formula))
	      (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm)))
	 (proof-substitute (make-proof-in-aconst-form aconst) psubst)))))
    ((imp)
;;                                  u4:A -> B   u2:A
;;                                  ----------------
;;                           u3:~B          B
;;                           ----------------
;;                                       F
;;                                   -------- u4
;;              u1:~~(A -> B)        ~(A -> B)
;;              ------------------------------
;;                              F
;;       |                     --- u3
;;   ~~B -> B                  ~~B
;;   -----------------------------
;;                  B
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (u1 (formula-to-new-avar (make-negation (make-negation formula))))
	    (u2 (formula-to-new-avar prem))
	    (u3 (formula-to-new-avar (make-negation concl)))
	    (u4 (formula-to-new-avar formula)))
       (mk-proof-in-intro-form
	u1 u2 (make-proof-in-imp-elim-form
	       (proof-of-stab-at concl)
	       (make-proof-in-imp-intro-form
		u3 (make-proof-in-imp-elim-form
		    (make-proof-in-avar-form u1)
		    (make-proof-in-imp-intro-form
		     u4 (make-proof-in-imp-elim-form
			 (make-proof-in-avar-form u3)
			 (make-proof-in-imp-elim-form
			  (make-proof-in-avar-form u4)
			  (make-proof-in-avar-form u2))))))))))
    ((impnc)
;;                                  u4:A --> B   u2:A
;;                                  -----------------
;;                           u3:~B          B
;;                           ----------------
;;                                       F
;;                                   -------- u4
;;              u1:~~(A --> B)      ~(A --> B)
;;              ------------------------------
;;                              F
;;       |                     --- u3
;;   ~~B -> B                  ~~B
;;   -----------------------------
;;                  B
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula))
	    (u1 (formula-to-new-avar (make-negation (make-negation formula))))
	    (u2 (formula-to-new-avar prem))
	    (u3 (formula-to-new-avar (make-negation concl)))
	    (u4 (formula-to-new-avar formula)))
       (mk-proof-in-intro-form
	u1 u2 (make-proof-in-imp-elim-form
	       (proof-of-stab-at concl)
	       (make-proof-in-imp-intro-form
		u3 (make-proof-in-imp-elim-form
		    (make-proof-in-avar-form u1)
		    (make-proof-in-imp-intro-form
		     u4 (make-proof-in-imp-elim-form
			 (make-proof-in-avar-form u3)
			 (make-proof-in-impnc-elim-form
			  (make-proof-in-avar-form u4)
			  (make-proof-in-avar-form u2))))))))))
    ((and)
;;                          u3:A&B                           u3:A&B
;;                          ------                           ------
;;                    u2:~A    A                       u2:~B    B
;;                    ------------                     ------------
;;                         F                                F
;;                       ------ u3                        ------ u3
;;          u1:~~(A&B)   ~(A&B)              u1:~~(A&B)   ~(A&B)
;;          -------------------              -------------------
;;                   F                                F
;;      |           --- u2               |           --- u2
;;  ~~A -> A        ~~A              ~~B -> B        ~~B
;;  -------------------              -------------------
;;            A                                B
;;            ----------------------------------
;;                           A & B
     (let* ((left-conjunct (and-form-to-left formula))
	    (right-conjunct (and-form-to-right formula))
	    (u1 (formula-to-new-avar (make-negation (make-negation formula))))
	    (u2left (formula-to-new-avar (make-negation left-conjunct)))
	    (u2right (formula-to-new-avar (make-negation right-conjunct)))
	    (u3 (formula-to-new-avar formula)))
       (make-proof-in-imp-intro-form
	u1 (make-proof-in-and-intro-form
	    (make-proof-in-imp-elim-form
	     (proof-of-stab-at left-conjunct)
	     (make-proof-in-imp-intro-form
	      u2left (make-proof-in-imp-elim-form
		      (make-proof-in-avar-form u1)
		      (make-proof-in-imp-intro-form
		       u3 (make-proof-in-imp-elim-form
			   (make-proof-in-avar-form u2left)
			   (make-proof-in-and-elim-left-form
			    (make-proof-in-avar-form u3)))))))
	    (make-proof-in-imp-elim-form
	     (proof-of-stab-at right-conjunct)
	     (make-proof-in-imp-intro-form
	      u2right (make-proof-in-imp-elim-form
		       (make-proof-in-avar-form u1)
		       (make-proof-in-imp-intro-form
			u3 (make-proof-in-imp-elim-form
			    (make-proof-in-avar-form u2right)
			    (make-proof-in-and-elim-right-form
			     (make-proof-in-avar-form u3)))))))))))
    ((all)
;;                                  u3:all x A   x
;;                                  --------------
;;                           u2:~A          A
;;                           ----------------
;;                                       F
;;                                   -------- u3
;;              u1:~~all x A         ~all x A
;;              -----------------------------
;;                              F
;;       |                     --- u2
;;   ~~A -> A                  ~~A
;;   -----------------------------
;;                 A
;;              -------
;;              all x A
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (u1 (formula-to-new-avar (make-negation (make-negation formula))))
	    (u2 (formula-to-new-avar (make-negation kernel)))
	    (u3 (formula-to-new-avar formula)))
       (mk-proof-in-intro-form
	u1 var (make-proof-in-imp-elim-form
		(proof-of-stab-at kernel)
		(make-proof-in-imp-intro-form
		 u2 (make-proof-in-imp-elim-form
		     (make-proof-in-avar-form u1)
		     (make-proof-in-imp-intro-form
		      u3 (make-proof-in-imp-elim-form
			  (make-proof-in-avar-form u2)
			  (make-proof-in-all-elim-form
			   (make-proof-in-avar-form u3)
			   (make-term-in-var-form var))))))))))
    ((allnc)
;;                                    u3:allnc x A   x
;;                                    ----------------
;;                             u2:~A          A
;;                             ----------------
;;                                         F
;;                                     ---------- u3
;;              u1:~~allnc x A         ~allnc x A
;;              ---------------------------------
;;                              F
;;       |                     --- u2
;;   ~~A -> A                  ~~A
;;   -----------------------------
;;                 A
;;              ---------
;;              allnc x A
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (u1 (formula-to-new-avar (make-negation (make-negation formula))))
	    (u2 (formula-to-new-avar (make-negation kernel)))
	    (u3 (formula-to-new-avar formula)))
       (mk-proof-in-nc-intro-form
	u1 var (make-proof-in-imp-elim-form
		(proof-of-stab-at kernel)
		(make-proof-in-imp-intro-form
		 u2 (make-proof-in-imp-elim-form
		     (make-proof-in-avar-form u1)
		     (make-proof-in-imp-intro-form
		      u3 (make-proof-in-imp-elim-form
			  (make-proof-in-avar-form u2)
			  (make-proof-in-allnc-elim-form
			   (make-proof-in-avar-form u3)
			   (make-term-in-var-form var))))))))))
    (else (myerror "proof-of-stab-at" "formula expected" formula))))

(define (proof-of-stab-log-at formula) ;formula must be unfolded
  (case (tag formula)
    ((atom predicate ex)
     (cond
      ((equal? falsity-log formula)
;;                                            u2:bot
;;                                          ----------u2
;;              u1:(bot -> bot) -> bot      bot -> bot
;;              --------------------------------------
;;                                     bot

       (let ((u1 (formula-to-new-avar
		  (make-negation-log (make-negation-log falsity-log))))
	     (u2 (formula-to-new-avar falsity-log)))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-imp-elim-form
	      (make-proof-in-avar-form u1)
	      (make-proof-in-imp-intro-form
	       u2 (make-proof-in-avar-form u2))))))
      ((equal? truth formula)
       (let ((u1 (formula-to-new-avar
		  (make-negation-log (make-negation-log truth)))))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-aconst-form truth-aconst))))
      (else
       (let* ((aconst (global-assumption-name-to-aconst "StabLog"))
	      (stab-log-formula (aconst-to-uninst-formula aconst))
	      (pvars (formula-to-pvars stab-log-formula))
	      (pvar (if (pair? pvars) (car pvars)
			(myerror "proof-to-stab-log-at"
				 "stab-log-formula with pvars expected"
				 stab-log-formula)))
	      (cterm (make-cterm formula))
	      (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm)))
	 (proof-substitute (make-proof-in-aconst-form aconst) psubst)))))
    ((imp)
;;                                  u4:A -> B   u2:A
;;                                  ----------------
;;                           u3:~B          B
;;                           ----------------
;;                                       bot
;;                                   -------- u4
;;              u1:~~(A -> B)        ~(A -> B)
;;              ------------------------------
;;                              bot
;;       |                     --- u3
;;   ~~B -> B                  ~~B
;;   -----------------------------
;;                  B
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (u1 (formula-to-new-avar
		 (make-negation-log (make-negation-log formula))))
	    (u2 (formula-to-new-avar prem))
	    (u3 (formula-to-new-avar (make-negation-log concl)))
	    (u4 (formula-to-new-avar formula)))
       (mk-proof-in-intro-form
	u1 u2 (make-proof-in-imp-elim-form
	       (proof-of-stab-log-at concl)
	       (make-proof-in-imp-intro-form
		u3 (make-proof-in-imp-elim-form
		    (make-proof-in-avar-form u1)
		    (make-proof-in-imp-intro-form
		     u4 (make-proof-in-imp-elim-form
			 (make-proof-in-avar-form u3)
			 (make-proof-in-imp-elim-form
			  (make-proof-in-avar-form u4)
			  (make-proof-in-avar-form u2))))))))))
    ((impnc)
;;                                  u4:A --> B   u2:A
;;                                  -----------------
;;                           u3:~B          B
;;                           ----------------
;;                                       bot
;;                                   -------- u4
;;              u1:~~(A --> B)      ~(A --> B)
;;              ------------------------------
;;                              bot
;;       |                     --- u3
;;   ~~B -> B                  ~~B
;;   -----------------------------
;;                  B
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula))
	    (u1 (formula-to-new-avar
		 (make-negation-log (make-negation-log formula))))
	    (u2 (formula-to-new-avar prem))
	    (u3 (formula-to-new-avar (make-negation-log concl)))
	    (u4 (formula-to-new-avar formula)))
       (mk-proof-in-intro-form
	u1 u2 (make-proof-in-imp-elim-form
	       (proof-of-stab-log-at concl)
	       (make-proof-in-imp-intro-form
		u3 (make-proof-in-imp-elim-form
		    (make-proof-in-avar-form u1)
		    (make-proof-in-imp-intro-form
		     u4 (make-proof-in-imp-elim-form
			 (make-proof-in-avar-form u3)
			 (make-proof-in-impnc-elim-form
			  (make-proof-in-avar-form u4)
			  (make-proof-in-avar-form u2))))))))))
    ((and)
;;                          u3:A&B                           u3:A&B
;;                          ------                           ------
;;                    u2:~A    A                       u2:~B    B
;;                    ------------                     ------------
;;                         bot                              bot
;;                       ------ u3                        ------ u3
;;          u1:~~(A&B)   ~(A&B)              u1:~~(A&B)   ~(A&B)
;;          -------------------              -------------------
;;                  bot                             bot
;;      |           --- u2               |           --- u2
;;  ~~A -> A        ~~A              ~~B -> B        ~~B
;;  -------------------              -------------------
;;            A                                B
;;            ----------------------------------
;;                           A & B
     (let* ((left-conjunct (and-form-to-left formula))
	    (right-conjunct (and-form-to-right formula))
	    (u1 (formula-to-new-avar
		 (make-negation-log (make-negation-log formula))))
	    (u2left (formula-to-new-avar (make-negation-log left-conjunct)))
	    (u2right (formula-to-new-avar (make-negation-log right-conjunct)))
	    (u3 (formula-to-new-avar formula)))
       (make-proof-in-imp-intro-form
	u1 (make-proof-in-and-intro-form
	    (make-proof-in-imp-elim-form
	     (proof-of-stab-log-at left-conjunct)
	     (make-proof-in-imp-intro-form
	      u2left (make-proof-in-imp-elim-form
		      (make-proof-in-avar-form u1)
		      (make-proof-in-imp-intro-form
		       u3 (make-proof-in-imp-elim-form
			   (make-proof-in-avar-form u2left)
			   (make-proof-in-and-elim-left-form
			    (make-proof-in-avar-form u3)))))))
	    (make-proof-in-imp-elim-form
	     (proof-of-stab-log-at right-conjunct)
	     (make-proof-in-imp-intro-form
	      u2right (make-proof-in-imp-elim-form
		       (make-proof-in-avar-form u1)
		       (make-proof-in-imp-intro-form
			u3 (make-proof-in-imp-elim-form
			    (make-proof-in-avar-form u2right)
			    (make-proof-in-and-elim-right-form
			     (make-proof-in-avar-form u3)))))))))))
    ((all)
;;                                  u3:all x A   x
;;                                  --------------
;;                           u2:~A          A
;;                           ----------------
;;                                      bot
;;                                   -------- u3
;;              u1:~~all x A         ~all x A
;;              -----------------------------
;;                             bot
;;       |                     --- u2
;;   ~~A -> A                  ~~A
;;   -----------------------------
;;                 A
;;              -------
;;              all x A
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (u1 (formula-to-new-avar
		 (make-negation-log (make-negation-log formula))))
	    (u2 (formula-to-new-avar (make-negation-log kernel)))
	    (u3 (formula-to-new-avar formula)))
       (mk-proof-in-intro-form
	u1 var (make-proof-in-imp-elim-form
		(proof-of-stab-log-at kernel)
		(make-proof-in-imp-intro-form
		 u2 (make-proof-in-imp-elim-form
		     (make-proof-in-avar-form u1)
		     (make-proof-in-imp-intro-form
		      u3 (make-proof-in-imp-elim-form
			  (make-proof-in-avar-form u2)
			  (make-proof-in-all-elim-form
			   (make-proof-in-avar-form u3)
			   (make-term-in-var-form var))))))))))
    ((allnc)
;;                                    u3:allnc x A   x
;;                                    ----------------
;;                             u2:~A          A
;;                             ----------------
;;                                        bot
;;                                     ---------- u3
;;              u1:~~allnc x A         ~allnc x A
;;              -----------------------------
;;                             bot
;;       |                     --- u2
;;   ~~A -> A                  ~~A
;;   -----------------------------
;;                 A
;;              -------
;;              allnc x A
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (u1 (formula-to-new-avar
		 (make-negation-log (make-negation-log formula))))
	    (u2 (formula-to-new-avar (make-negation-log kernel)))
	    (u3 (formula-to-new-avar formula)))
       (mk-proof-in-nc-intro-form
	u1 var (make-proof-in-imp-elim-form
		(proof-of-stab-log-at kernel)
		(make-proof-in-imp-intro-form
		 u2 (make-proof-in-imp-elim-form
		     (make-proof-in-avar-form u1)
		     (make-proof-in-imp-intro-form
		      u3 (make-proof-in-imp-elim-form
			  (make-proof-in-avar-form u2)
			  (make-proof-in-allnc-elim-form
			   (make-proof-in-avar-form u3)
			   (make-term-in-var-form var))))))))))
    (else (myerror "proof-of-stab-log-at" "formula expected" formula))))

(define (proof-of-efq-at formula) ;formula must be unfolded
  (case (tag formula)
    ((atom predicate)
     (cond
      ((equal? falsity formula)
;;               u1:F
;;             --------u1
;;              F -> F
       (let ((u1 (formula-to-new-avar falsity)))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-avar-form u1))))
      ((equal? truth formula)
       (let ((u1 (formula-to-new-avar falsity)))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-aconst-form truth-aconst))))
      ((atom-form? formula)
       (let* ((u1 (formula-to-new-avar falsity))
	      (elim-proof
	       (mk-proof-in-elim-form
		(make-proof-in-aconst-form
		 (theorem-name-to-aconst "EfqAtom")) ;F -> all p^ p^
		(make-proof-in-avar-form u1)
		(atom-form-to-kernel formula))))
	 (make-proof-in-imp-intro-form
	  u1 elim-proof)))
      ((predicate-form? formula)
       (let ((pred (predicate-form-to-predicate formula))
	     (args (predicate-form-to-args formula)))
	 (cond
	  ((and (idpredconst-form? pred)
		(string=? "EqD" (idpredconst-to-name pred)))
	   (let* ((u1 (formula-to-new-avar falsity))
		  (aconst ;F -> all x^,y^ x^ eqd y^
		   (theorem-name-to-aconst "EfqEqD"))
		  (uninst-formula (aconst-to-uninst-formula aconst))
		  (concl (imp-form-to-conclusion uninst-formula))
		  (var (all-form-to-var concl))
		  (tvar (var-to-type var))
		  (type (term-to-type (car args)))
		  (subst-aconst
		   (if (equal? tvar type)
		       aconst
		       (aconst-substitute aconst (make-subst tvar type))))
		  (elim-proof (mk-proof-in-elim-form
			       (make-proof-in-aconst-form subst-aconst)
			       (make-proof-in-avar-form u1)
			       (car args) (cadr args))))
	     (make-proof-in-imp-intro-form
	      u1 elim-proof)))
	  (else
	   (let* ((aconst (global-assumption-name-to-aconst "Efq"))
		  (efq-formula (aconst-to-uninst-formula aconst))
		  (pvars (formula-to-pvars efq-formula))
		  (pvar (if (pair? pvars) (car pvars)
			    (myerror
			     "proof-to-efq-at" "efq-formula with pvars expected"
			     efq-formula)))
		  (cterm (make-cterm formula))
		  (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm)))
	     (proof-substitute (make-proof-in-aconst-form aconst) psubst))))))))
    ((imp)
;;              |
;;            F -> B     u1:F
;;          -----------------
;;                    B
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (u1 (formula-to-new-avar falsity))
	    (u2 (formula-to-new-avar prem)))
       (mk-proof-in-intro-form
	u1 u2 (make-proof-in-imp-elim-form
	       (proof-of-efq-at concl)
	       (make-proof-in-avar-form u1)))))
    ((impnc)
;;              |
;;            F -> B     u1:F
;;          -----------------
;;                    B
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula))
	    (u1 (formula-to-new-avar falsity))
	    (u2 (formula-to-new-avar prem)))
       (make-proof-in-imp-intro-form
	u1 (make-proof-in-impnc-intro-form
	    u2 (make-proof-in-imp-elim-form
		(proof-of-efq-at concl)
		(make-proof-in-avar-form u1))))))
    ((and)
;;          |                              |
;;        F -> A       u1:F              F -> B        u1:F
;;        -------------------              ----------------
;;                 A                               B
;;                 ---------------------------------
;;                               A & B
     (let* ((left-conjunct (and-form-to-left formula))
	    (right-conjunct (and-form-to-right formula))
	    (u1 (formula-to-new-avar falsity)))
       (make-proof-in-imp-intro-form
	u1 (make-proof-in-and-intro-form
	    (make-proof-in-imp-elim-form
	     (proof-of-efq-at left-conjunct)
	     (make-proof-in-avar-form u1))
	    (make-proof-in-imp-elim-form
	     (proof-of-efq-at right-conjunct)
	     (make-proof-in-avar-form u1))))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (u1 (formula-to-new-avar falsity)))
       (mk-proof-in-intro-form
	u1 var (make-proof-in-imp-elim-form
		(proof-of-efq-at kernel)
		(make-proof-in-avar-form u1)))))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (u1 (formula-to-new-avar falsity)))
       (mk-proof-in-intro-form
	u1 var (make-proof-in-imp-elim-form
		(proof-of-efq-at kernel)
		(make-proof-in-avar-form u1)))))
    ((ex)
     (let* ((var (ex-form-to-var formula))
	    (kernel (ex-form-to-kernel formula))
	    (type (var-to-type var))
	    (inhab (type-to-canonical-inhabitant type))
	    (inst-kernel (formula-subst kernel var inhab))
	    (u1 (formula-to-new-avar falsity)))
       (make-proof-in-imp-intro-form
	u1 (make-proof-in-ex-intro-form
	    inhab formula
	    (make-proof-in-imp-elim-form
	     (proof-of-efq-at inst-kernel)
	     (make-proof-in-avar-form u1))))))
    (else (myerror "proof-of-efq-at" "formula expected" formula))))

(define (proof-of-efq-log-at formula) ;formula must be unfolded
  (case (tag formula)
    ((atom predicate ex)
     (cond
      ((equal? falsity-log formula)
;;               u1:bot
;;             -----------u1
;;              bot -> bot
       (let ((u1 (formula-to-new-avar falsity-log)))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-avar-form u1))))
      ((equal? truth formula)
       (let ((u1 (formula-to-new-avar falsity-log)))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-aconst-form truth-aconst))))
      (else
       (let* ((aconst (global-assumption-name-to-aconst "EfqLog"))
	      (efq-log-formula (aconst-to-uninst-formula aconst))
	      (pvars (formula-to-pvars efq-log-formula))
	      (pvar (if (pair? pvars) (car (last-pair pvars))
			(myerror "proof-to-efq-log-at"
				 "efq-log-formula with pvars expected"
				 efq-log-formula)))
	      (cterm (make-cterm formula))
	      (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm)))
	 (proof-substitute (make-proof-in-aconst-form aconst) psubst)))))
    ((imp)
;;              |
;;          bot -> B     u1:bot
;;          -------------------
;;                    B
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (u1 (formula-to-new-avar falsity-log))
	    (u2 (formula-to-new-avar prem)))
       (mk-proof-in-intro-form
	u1 u2 (make-proof-in-imp-elim-form
	       (proof-of-efq-log-at concl)
	       (make-proof-in-avar-form u1)))))
    ((impnc)
;;              |
;;          bot -> B     u1:bot
;;          -------------------
;;                    B
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula))
	    (u1 (formula-to-new-avar falsity-log))
	    (u2 (formula-to-new-avar prem)))
       (make-proof-in-imp-intro-form
	u1 (make-proof-in-impnc-intro-form
	    u2 (make-proof-in-imp-elim-form
		(proof-of-efq-log-at concl)
		(make-proof-in-avar-form u1))))))
    ((and)
;;          |                              |
;;        bot -> A     u1:bot              bot -> B    u1:bot
;;        -------------------              ------------------
;;                 A                               B
;;                 ---------------------------------
;;                               A & B
     (let* ((left-conjunct (and-form-to-left formula))
	    (right-conjunct (and-form-to-right formula))
	    (u1 (formula-to-new-avar falsity-log)))
       (make-proof-in-imp-intro-form
	u1 (make-proof-in-and-intro-form
	    (make-proof-in-imp-elim-form
	     (proof-of-efq-log-at left-conjunct)
	     (make-proof-in-avar-form u1))
	    (make-proof-in-imp-elim-form
	     (proof-of-efq-log-at right-conjunct)
	     (make-proof-in-avar-form u1))))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (u1 (formula-to-new-avar falsity-log)))
       (mk-proof-in-intro-form
	u1 var (make-proof-in-imp-elim-form
		(proof-of-efq-log-at kernel)
		(make-proof-in-avar-form u1)))))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (u1 (formula-to-new-avar falsity-log)))
       (mk-proof-in-nc-intro-form
	u1 var (make-proof-in-imp-elim-form
		(proof-of-efq-log-at kernel)
		(make-proof-in-avar-form u1)))))
    (else (myerror "proof-of-efq-log-at" "formula expected" formula))))

(define (formula-to-efq-proof-or-f formula) ;formula should be unfolded
  (case (tag formula)
    ((atom predicate) #f)
    ((imp)
     (let ((prem (imp-form-to-premise formula))
	   (concl (imp-form-to-conclusion formula)))
       (if (classical-formula=? prem falsity)
	   (proof-of-efq-at concl)
	   (let ((prev (formula-to-efq-proof-or-f concl)))
	     (if prev
		 (make-proof-in-imp-intro-form
		  (formula-to-new-avar prem) prev)
		 #f)))))
    ((impnc)
     (let ((prem (impnc-form-to-premise formula))
	   (concl (impnc-form-to-conclusion formula)))
       (if (classical-formula=? prem falsity)
	   (proof-of-efq-at concl)
	   (let ((prev (formula-to-efq-proof-or-f concl)))
	     (if prev
		 (make-proof-in-impnc-intro-form
		  (formula-to-new-avar prem) prev)
		 #f)))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula))
	    (prev1 (formula-to-efq-proof-or-f left))
	    (prev2 (formula-to-efq-proof-or-f right)))
       (if (and prev1 prev2)
	   (make-proof-in-and-intro-form prev1 prev2)
	   #f)))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (prev (formula-to-efq-proof-or-f kernel)))
       (if prev
	   (make-proof-in-all-intro-form var prev)
	   #f)))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (prev (formula-to-efq-proof-or-f kernel)))
       (if prev
	   (make-proof-in-allnc-intro-form var prev)
	   #f)))
    ((ex)
     (let* ((var (ex-form-to-var formula))
	    (kernel (ex-form-to-kernel formula))
	    (prev (formula-to-efq-proof-or-f kernel)))
       (if prev
	   (make-proof-in-ex-intro-form
	    (make-term-in-var-form var) formula prev)
	   #f)))
    ((exca excl)
     (myerror "formula-to-efq-proof-or-f" "unfolded formula expected" formula))
    (else (myerror "formula-to-efq-proof-or-f" "formula expected" formula))))

(define (reduce-efq-and-stab proof)
  (case (tag proof)
    ((proof-in-avar-form) proof)
    ((proof-in-aconst-form)
     (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	    (name (aconst-to-name aconst)))
       (cond ((string=? name "Stab")
	      (let* ((formula (unfold-formula (proof-to-formula proof)))
		     (vars-and-final-kernel
		      (allnc-form-to-vars-and-final-kernel formula))
		     (vars (car vars-and-final-kernel))
		     (kernel (cadr vars-and-final-kernel))
		     (concl (imp-form-to-conclusion kernel)))
		(apply mk-proof-in-nc-intro-form
		       (append vars (list (proof-of-stab-at concl))))))
	     ((string=? name "Efq")
	      (let* ((formula (unfold-formula (proof-to-formula proof)))
		     (vars-and-final-kernel
		      (allnc-form-to-vars-and-final-kernel formula))
		     (vars (car vars-and-final-kernel))
		     (kernel (cadr vars-and-final-kernel))
		     (concl (imp-form-to-conclusion kernel)))
		(apply mk-proof-in-nc-intro-form
		       (append vars (list (proof-of-efq-at concl))))))
	     ((string=? name "StabLog")
	      (let* ((formula (unfold-formula (proof-to-formula proof)))
		     (vars-and-final-kernel
		      (allnc-form-to-vars-and-final-kernel formula))
		     (vars (car vars-and-final-kernel))
		     (kernel (cadr vars-and-final-kernel))
		     (concl (imp-form-to-conclusion kernel)))
		(apply mk-proof-in-nc-intro-form
		       (append vars (list (proof-of-stab-log-at concl))))))
	     ((string=? name "EfqLog")
	      (let* ((formula (unfold-formula (proof-to-formula proof)))
		     (vars-and-final-kernel
		      (allnc-form-to-vars-and-final-kernel formula))
		     (vars (car vars-and-final-kernel))
		     (kernel (cadr vars-and-final-kernel))
		     (concl (imp-form-to-conclusion kernel)))
		(apply mk-proof-in-nc-intro-form
		       (append vars (list (proof-of-efq-log-at concl))))))
	     (else proof))))
    ((proof-in-imp-elim-form)
     (let ((op (proof-in-imp-elim-form-to-op proof))
	   (arg (proof-in-imp-elim-form-to-arg proof)))
       (make-proof-in-imp-elim-form
	(reduce-efq-and-stab op)
	(reduce-efq-and-stab arg))))
    ((proof-in-imp-intro-form)
     (let ((avar (proof-in-imp-intro-form-to-avar proof))
	   (kernel (proof-in-imp-intro-form-to-kernel proof)))
       (make-proof-in-imp-intro-form
	avar (reduce-efq-and-stab kernel))))
    ((proof-in-impnc-elim-form)
     (let ((op (proof-in-impnc-elim-form-to-op proof))
	   (arg (proof-in-impnc-elim-form-to-arg proof)))
       (make-proof-in-impnc-elim-form
	(reduce-efq-and-stab op)
	(reduce-efq-and-stab arg))))
    ((proof-in-impnc-intro-form)
     (let ((avar (proof-in-impnc-intro-form-to-avar proof))
	   (kernel (proof-in-impnc-intro-form-to-kernel proof)))
       (make-proof-in-impnc-intro-form
	avar (reduce-efq-and-stab kernel))))
    ((proof-in-and-intro-form)
     (let ((left (proof-in-and-intro-form-to-left proof))
	   (right (proof-in-and-intro-form-to-right proof)))
       (make-proof-in-and-intro-form
	(reduce-efq-and-stab left)
	(reduce-efq-and-stab right))))
    ((proof-in-and-elim-left-form)
     (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (make-proof-in-and-elim-left-form ;inserted M.S.
	(reduce-efq-and-stab kernel))))
    ((proof-in-and-elim-right-form)
     (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (make-proof-in-and-elim-right-form ;inserted M.S.
	(reduce-efq-and-stab kernel))))
    ((proof-in-all-intro-form)
     (let ((var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-proof-in-all-intro-form
	var (reduce-efq-and-stab kernel))))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
       (make-proof-in-all-elim-form (reduce-efq-and-stab op) arg)))
    ((proof-in-allnc-intro-form)
     (let ((var (proof-in-allnc-intro-form-to-var proof))
	   (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-proof-in-allnc-intro-form
	var (reduce-efq-and-stab kernel))))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof))
	   (arg (proof-in-allnc-elim-form-to-arg proof)))
       (make-proof-in-allnc-elim-form (reduce-efq-and-stab op) arg)))
    (else (myerror "reduce-efq-and-stab" "proof tag expected"
		   (tag proof)))))

;; We can transform a proof involving classical existential quantifiers
;; in another one without, i.e., in minimal logic.  The Exc-Intro and
;; Exc-Elim theorems are replaced by their proofs, using expand-theorems.

(define (rm-exc proof)
  (let ((name-test?
	 (lambda (string)
	   (or
	    (and (<= (string-length "ExcaIntro") (string-length string))
		 (string=? (substring string 0 (string-length "ExcaIntro"))
			   "ExcaIntro"))
	    (and (<= (string-length "ExclIntro") (string-length string))
		 (string=? (substring string 0 (string-length "ExclIntro"))
			   "ExclIntro"))
	    (and (<= (string-length "ExcaElim") (string-length string))
		 (string=? (substring string 0 (string-length "ExcaElim"))
			   "ExcaElim"))
	    (and (<= (string-length "ExclElim") (string-length string))
		 (string=? (substring string 0 (string-length "ExclElim"))
			   "ExclElim"))))))
    (expand-theorems proof name-test?)))

;; We now define the Goedel-Gentzen translation of formulas.  We do not
;; consider $\exc$, because it can be unfolded (is not needed for
;; program extraction).

(define (formula-to-goedel-gentzen-translation formula)
  (case (tag formula)
    ((atom predicate)
     (if (formula=? falsity-log formula)
	 falsity-log
	 (mk-neg-log (mk-neg-log formula))))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (prev1 (formula-to-goedel-gentzen-translation prem))
	    (prev2 (formula-to-goedel-gentzen-translation concl)))
       (make-imp prev1 prev2)))
    ((impnc)
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula))
	    (prev1 (formula-to-goedel-gentzen-translation prem))
	    (prev2 (formula-to-goedel-gentzen-translation concl)))
       (make-impnc prev1 prev2)))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula))
	    (prev1 (formula-to-goedel-gentzen-translation left))
	    (prev2 (formula-to-goedel-gentzen-translation right)))
       (make-and prev1 prev2)))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (prev (formula-to-goedel-gentzen-translation kernel)))
       (make-all var prev)))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (prev (formula-to-goedel-gentzen-translation kernel)))
       (make-allnc var prev)))
    (else
     (myerror "formula-to-goedel-gentzen-translation" "unexpected formula"
	      formula))))

;; We introduce a further observation (due to Leivant;; see Troelstra and
;; van Dalen \cite[Ch.2, Sec.3]{TroelstravanDalen88}) which will be
;; useful for program extraction from classical proofs.  There it will be
;; necessary to actually transform a given classical derivation $\vdash_c
;; A$ into a minimal logic derivation $\vdash A^g$.  In particular, for
;; every assumption constant $C$ used in the given derivation we have to
;; provide a derivation of $C^g$.  Now for some formulas $S$ -- the
;; so-called spreading formulas -- this is immediate, for we can derive
;; $S \to S^g$, and hence can use the original assumption constant.

;; In order to obtain a derivation of $C^g$ for $C$ an assumption
;; constant it suffices to know that its uninstantiated formula $S$ is
;; spreading, for then we generally have $\vdash S[\vec{A}^g] \to
;; S[\vec{A}]^g$ and hence can use the same assumption constant with a
;; different substitution.

;; We define spreading, wiping and isolating formulas inductively.

(define (spreading-formula? formula)
  (case (tag formula)
    ((atom predicate) #t)
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula)))
       (and (isolating-formula? prem)
	    (spreading-formula? concl))))
    ((impnc)
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula)))
       (and (isolating-formula? prem)
	    (spreading-formula? concl))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula)))
       (and (spreading-formula? left)
	    (spreading-formula? right))))
    ((all)
     (let ((kernel (all-form-to-kernel formula)))
       (spreading-formula? kernel)))
    ((allnc)
     (let ((kernel (allnc-form-to-kernel formula)))
       (spreading-formula? kernel)))
    (else (myerror "spreading-formula?" "unexpected formula" formula))))

(define (wiping-formula? formula)
  (case (tag formula)
    ((atom predicate)
     (or (formula=? falsity-log formula)
	 (and (predicate-form? formula)
	      (pvar? (predicate-form-to-predicate formula)))))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula)))
       (and (spreading-formula? prem)
	    (wiping-formula? concl))))
    ((impnc)
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula)))
       (and (spreading-formula? prem)
	    (wiping-formula? concl))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula)))
       (and (wiping-formula? left)
	    (wiping-formula? right))))
    ((all)
     (let ((kernel (all-form-to-kernel formula)))
       (wiping-formula? kernel)))
    ((allnc)
     (let ((kernel (allnc-form-to-kernel formula)))
       (wiping-formula? kernel)))
    (else (myerror "wiping-formula?" "unexpected formula" formula))))

(define (isolating-formula? formula)
  (or (prime-form? formula)
      (wiping-formula? formula)
      (and (and-form? formula)
	   (isolating-formula? (and-form-to-left formula))
	   (isolating-formula? (and-form-to-right formula)))))

;; For a spreading formula S we can derive S[A^g] -> S[A]^g.
;; opt-topsubst contains of some X -> A.  The other pvars in S are
;; substituted automatically by their Goedel-Gentzen translations.

(define (spreading-formula-to-proof formula . opt-topsubst)
  (let* ((orig-topsubst
	  (if (null? opt-topsubst) empty-subst (car opt-topsubst)))
	 (orig-topsubst-gg
	  (map (lambda (item)
		 (if (pvar-form? (car item))
		     (let* ((pvar (car item))
			    (cterm (cadr item))
			    (vars (cterm-to-vars cterm))
			    (formula (cterm-to-formula cterm))
			    (formula-gg
			     (formula-to-goedel-gentzen-translation formula)))
		       (list pvar (apply make-cterm
					 (append vars (list formula-gg)))))
		     item))
	       orig-topsubst))
	 (pvars (remove (predicate-form-to-predicate falsity-log)
			(formula-to-pvars formula)))
	 (extra-pvars (set-minus pvars (map car orig-topsubst)))
	 (extra-psubst-gg
	  (map (lambda (pvar)
		 (let* ((arity (pvar-to-arity pvar))
			(types (arity-to-types arity))
			(vars (map type-to-new-partial-var types))
			(varterms (map make-term-in-var-form vars))
			(formula (apply make-predicate-formula pvar varterms))
			(formula-gg (make-negation-log
				     (make-negation-log formula))))
		   (list pvar
			 (apply make-cterm
				(append vars (list formula-gg))))))
	       extra-pvars))
	 (topsubst-gg (append orig-topsubst-gg extra-psubst-gg)))
    (spreading-formula-to-proof-aux formula orig-topsubst topsubst-gg)))

;; Now use topsubst-gg (X -> A^g, Y -> ~~Y) for all (orig) formulas.
;; Recall topsubst: X -> A

(define (spreading-formula-to-proof-aux formula topsubst topsubst-gg)
  (case (tag formula)
    ((atom predicate)
     (if (and (predicate-form? formula)
	      (pvar? (predicate-form-to-predicate formula)))
	 (let* ((subst-formula-gg (formula-substitute formula topsubst-gg))
		(u (formula-to-new-avar subst-formula-gg)))
	   (make-proof-in-imp-intro-form
	    u (make-proof-in-avar-form u)))
	 (let* ((tosubst (list-transform-positive topsubst
			   (lambda (x) (or (tvar-form? (car x))
					   (var-form? (car x))))))
		(subst-formula (formula-substitute formula tosubst))
		(u (formula-to-new-avar subst-formula))
		(v (formula-to-new-avar (mk-neg-log subst-formula))))
	   (mk-proof-in-intro-form
	    u v (make-proof-in-imp-elim-form
		 (make-proof-in-avar-form v)
		 (make-proof-in-avar-form u))))))
    ((imp)
     (let* ((subst-formula (formula-substitute formula topsubst)) ;I[A] -> S[A]
	    (gg-subst-formula ;I[A^g] -> S[A^g]
	     (formula-substitute formula topsubst-gg))
	    (prem (imp-form-to-premise formula))
	    (subst-prem (imp-form-to-premise subst-formula))
	    (subst-prem-gg ;I[A]^g
	     (formula-to-goedel-gentzen-translation subst-prem))
	    (gg-subst-prem ;I[A^g]
	     (imp-form-to-premise gg-subst-formula))
	    (concl (imp-form-to-conclusion formula))
	    (subst-concl (imp-form-to-conclusion subst-formula))
	    (subst-concl-gg ;S[A]^g
	     (formula-to-goedel-gentzen-translation subst-concl))
	    (gg-subst-concl ;S[A^g]
	     (imp-form-to-conclusion gg-subst-formula))
	    (u (formula-to-new-avar gg-subst-formula))
	    (v (formula-to-new-avar subst-prem-gg))
	    (w1 (formula-to-new-avar (mk-neg-log subst-concl-gg)))
	    (w2 (formula-to-new-avar gg-subst-prem)))
       (mk-proof-in-intro-form
	u v (make-proof-in-imp-elim-form
	     (proof-of-stab-log-at subst-concl-gg)
	     (make-proof-in-imp-intro-form
	      w1 (mk-proof-in-elim-form
		  (isolating-formula-to-proof-aux prem topsubst topsubst-gg)
		  (make-proof-in-avar-form v)
		  (make-proof-in-imp-intro-form
		   w2 (make-proof-in-imp-elim-form
		       (make-proof-in-avar-form w1)
		       (make-proof-in-imp-elim-form
			(spreading-formula-to-proof-aux
			 concl topsubst topsubst-gg)
			(make-proof-in-imp-elim-form
			 (make-proof-in-avar-form u)
			 (make-proof-in-avar-form w2)))))))))))
    ((impnc)
     (let* ((subst-formula (formula-substitute formula topsubst)) ;I[A] -> S[A]
	    (gg-subst-formula ;I[A^g] -> S[A^g]
	     (formula-substitute formula topsubst-gg))
	    (prem (impnc-form-to-premise formula))
	    (subst-prem (impnc-form-to-premise subst-formula))
	    (subst-prem-gg ;I[A]^g
	     (formula-to-goedel-gentzen-translation subst-prem))
	    (gg-subst-prem ;I[A^g]
	     (impnc-form-to-premise gg-subst-formula))
	    (concl (impnc-form-to-conclusion formula))
	    (subst-concl (impnc-form-to-conclusion subst-formula))
	    (subst-concl-gg ;S[A]^g
	     (formula-to-goedel-gentzen-translation subst-concl))
	    (gg-subst-concl ;S[A^g]
	     (impnc-form-to-conclusion gg-subst-formula))
	    (u (formula-to-new-avar gg-subst-formula))
	    (v (formula-to-new-avar subst-prem-gg))
	    (w1 (formula-to-new-avar (mk-neg-log subst-concl-gg)))
	    (w2 (formula-to-new-avar gg-subst-prem)))
       (make-proof-in-imp-intro-form
	u (make-proof-in-impnc-intro-form
	   v (make-proof-in-imp-elim-form
	      (proof-of-stab-log-at subst-concl-gg)
	      (make-proof-in-imp-intro-form
	       w1 (mk-proof-in-elim-form
		   (isolating-formula-to-proof-aux prem topsubst topsubst-gg)
		   (make-proof-in-avar-form v)
		   (make-proof-in-imp-intro-form
		    w2 (make-proof-in-imp-elim-form
			(make-proof-in-avar-form w1)
			(make-proof-in-imp-elim-form
			 (spreading-formula-to-proof-aux
			  concl topsubst topsubst-gg)
			 (make-proof-in-impnc-elim-form
			  (make-proof-in-avar-form u)
			  (make-proof-in-avar-form w2))))))))))))
     ((and)
      (let* ((u (formula-to-new-avar formula))
	     (left (and-form-to-left formula))
	     (right (and-form-to-right formula)))
	(mk-proof-in-intro-form
	 u (make-proof-in-and-intro-form
	    (make-proof-in-imp-elim-form
	     (spreading-formula-to-proof-aux left topsubst topsubst-gg)
	     (make-proof-in-and-elim-left-form
	      (make-proof-in-avar-form u)))
	    (make-proof-in-imp-elim-form
	     (spreading-formula-to-proof-aux right topsubst topsubst-gg)
	     (make-proof-in-and-elim-right-form
	      (make-proof-in-avar-form u)))))))
     ((all)
      (let* ((gg-subst-formula ;(all x S)[A^g]
	      (formula-substitute formula topsubst-gg))
	     (u (formula-to-new-avar gg-subst-formula))
	     (var (all-form-to-var formula))
	     (kernel (all-form-to-kernel formula))
	     (type (var-to-type var))
	     (tsubst (list-transform-positive topsubst
		       (lambda (x) (tvar-form? (car x)))))
	     (type-unchanged?
	      (null? (intersection (type-to-tvars type) (map car tsubst))))
	     (new-var
	      (if type-unchanged?
		  var
		  (if (t-deg-zero? (var-to-t-deg var))
		      (type-to-new-partial-var (type-substitute type tsubst))
		      (type-to-new-var (type-substitute type tsubst)))))
	     (new-topsubst
	      (if type-unchanged?
		  topsubst
		  (append tsubst
			  (cons (list var (make-term-in-var-form new-var))
				(list-transform-positive topsubst
				  (lambda (x)
				    (or (var-form? (car x))
					(pvar-form? (car x)))))))))
	     (new-topsubst-gg
	      (if type-unchanged?
		  topsubst-gg
		  (append tsubst
			  (cons (list var (make-term-in-var-form new-var))
				(list-transform-positive topsubst-gg
				  (lambda (x)
				    (or (var-form? (car x))
					(pvar-form? (car x))))))))))
	(make-proof-in-imp-intro-form
	 u (make-proof-in-all-intro-form
	    new-var (make-proof-in-imp-elim-form
		     (spreading-formula-to-proof-aux
		      kernel new-topsubst new-topsubst-gg)
		     (make-proof-in-all-elim-form
		      (make-proof-in-avar-form u)
		      (make-term-in-var-form new-var)))))))
     ((allnc)
      (let* ((gg-subst-formula ;(allnc x S)[A^g]
	      (formula-substitute formula topsubst-gg))
	     (u (formula-to-new-avar gg-subst-formula))
	     (var (allnc-form-to-var formula))
	     (kernel (allnc-form-to-kernel formula))
	     (type (var-to-type var))
	     (tsubst (list-transform-positive topsubst
		       (lambda (x) (tvar-form? (car x)))))
	     (type-unchanged?
	      (null? (intersection (type-to-tvars type) (map car tsubst))))
	     (new-var
	      (if type-unchanged?
		  var
		  (if (t-deg-zero? (var-to-t-deg var))
		      (type-to-new-partial-var (type-substitute type tsubst))
		      (type-to-new-var (type-substitute type tsubst)))))
	     (new-topsubst
	      (if type-unchanged?
		  topsubst
		  (append tsubst
			  (cons (list var (make-term-in-var-form new-var))
				(list-transform-positive topsubst
				  (lambda (x)
				    (or (var-form? (car x))
					(pvar-form? (car x)))))))))
	     (new-topsubst-gg
	      (if type-unchanged?
		  topsubst-gg
		  (append tsubst
			  (cons (list var (make-term-in-var-form new-var))
				(list-transform-positive topsubst-gg
				  (lambda (x)
				    (or (var-form? (car x))
					(pvar-form? (car x))))))))))
	(make-proof-in-imp-intro-form
	 u (make-proof-in-allnc-intro-form
	    new-var (make-proof-in-imp-elim-form
		     (spreading-formula-to-proof-aux
		      kernel new-topsubst new-topsubst-gg)
		     (make-proof-in-allnc-elim-form
		      (make-proof-in-avar-form u)
		      (make-term-in-var-form new-var)))))))
     (else (myerror "spreading-formula-to-proof-aux" "unexpected formula"
		    formula))))

(define (wiping-formula-to-proof formula . opt-topsubst)
  (let* ((orig-topsubst
	  (if (null? opt-topsubst) empty-subst (car opt-topsubst)))
	 (orig-topsubst-gg
	  (map (lambda (item)
		 (if (pvar-form? (car item))
		     (let* ((pvar (car item))
			    (cterm (cadr item))
			    (vars (cterm-to-vars cterm))
			    (formula (cterm-to-formula cterm))
			    (formula-gg
			     (formula-to-goedel-gentzen-translation formula)))
		       (list pvar (apply make-cterm
					 (append vars (list formula-gg)))))
		     item))
	       orig-topsubst))
	 (pvars (remove (predicate-form-to-predicate falsity-log)
			(formula-to-pvars formula)))
	 (extra-pvars (set-minus pvars (map car orig-topsubst)))
	 (extra-psubst-gg
	  (map (lambda (pvar)
		 (let* ((arity (pvar-to-arity pvar))
			(types (arity-to-types arity))
			(vars (map type-to-new-partial-var types))
			(varterms (map make-term-in-var-form vars))
			(formula (apply make-predicate-formula pvar varterms))
			(formula-gg (make-negation-log
				     (make-negation-log formula))))
		   (list pvar
			 (apply make-cterm
				(append vars (list formula-gg))))))
	       extra-pvars))
	 (topsubst-gg (append orig-topsubst-gg extra-psubst-gg)))
    (wiping-formula-to-proof-aux formula orig-topsubst topsubst-gg)))

(define (wiping-formula-to-proof-aux formula topsubst topsubst-gg)
  (case (tag formula)
    ((atom predicate)
     (if (and (predicate-form? formula)
	      (pvar? (predicate-form-to-predicate formula)))
	 (let* ((gg-subst-formula (formula-substitute formula topsubst-gg))
		(u (formula-to-new-avar gg-subst-formula)))
	   (make-proof-in-imp-intro-form
	    u (make-proof-in-avar-form u)))
	 (myerror "wiping-formula-to-proof-aux" "pvar or falsity-log expected"
		  formula)))
    ((imp)
     (let* ((subst-formula ;S[A] -> W[A]
	     (formula-substitute formula topsubst))
	    (prem (imp-form-to-premise formula))
	    (subst-prem (imp-form-to-premise subst-formula))
	    (subst-prem-gg ;S[A]^g
	     (formula-to-goedel-gentzen-translation subst-prem))
	    (gg-subst-prem ;S[A^g]
	     (formula-substitute prem topsubst-gg))
	    (concl (imp-form-to-conclusion formula))
	    (subst-concl (imp-form-to-conclusion subst-formula))
	    (subst-concl-gg ;W[A]^g
	     (formula-to-goedel-gentzen-translation subst-concl))
	    (u (formula-to-new-avar (make-imp subst-prem-gg subst-concl-gg)))
	    (v (formula-to-new-avar gg-subst-prem)))
       (mk-proof-in-intro-form
	u v (make-proof-in-imp-elim-form
	     (wiping-formula-to-proof-aux concl topsubst topsubst-gg)
	     (make-proof-in-imp-elim-form
	      (make-proof-in-avar-form u)
	      (make-proof-in-imp-elim-form
	       (spreading-formula-to-proof-aux prem topsubst topsubst-gg)
	       (make-proof-in-avar-form v)))))))
    ((impnc)
     (let* ((subst-formula ;S[A] -> W[A]
	     (formula-substitute formula topsubst))
	    (prem (impnc-form-to-premise formula))
	    (subst-prem (impnc-form-to-premise subst-formula))
	    (subst-prem-gg ;S[A]^g
	     (formula-to-goedel-gentzen-translation subst-prem))
	    (gg-subst-prem ;S[A^g]
	     (formula-substitute prem topsubst-gg))
	    (concl (impnc-form-to-conclusion formula))
	    (subst-concl (impnc-form-to-conclusion subst-formula))
	    (subst-concl-gg ;W[A]^g
	     (formula-to-goedel-gentzen-translation subst-concl))
	    (u (formula-to-new-avar (make-impnc subst-prem-gg subst-concl-gg)))
	    (v (formula-to-new-avar gg-subst-prem)))
       (make-proof-in-imp-intro-form
	u (make-proof-in-impnc-intro-form
	   v (make-proof-in-imp-elim-form
	      (wiping-formula-to-proof-aux concl topsubst topsubst-gg)
	      (make-proof-in-impnc-elim-form
	       (make-proof-in-avar-form u)
	       (make-proof-in-imp-elim-form
		(spreading-formula-to-proof-aux prem topsubst topsubst-gg)
		(make-proof-in-avar-form v))))))))
    ((and)
     (let* ((gg-subst-formula ;(W1 & W2)^g
	     (formula-substitute formula topsubst-gg))
	    (u (formula-to-new-avar gg-subst-formula))
	    (left (and-form-to-left formula))
	    (right (and-form-to-right formula)))
       (mk-proof-in-intro-form
	u (make-proof-in-and-intro-form
	   (make-proof-in-imp-elim-form
	    (wiping-formula-to-proof-aux left topsubst topsubst-gg)
	    (make-proof-in-and-elim-left-form
	     (make-proof-in-avar-form u)))
	   (make-proof-in-imp-elim-form
	    (wiping-formula-to-proof-aux right topsubst topsubst-gg)
	    (make-proof-in-and-elim-right-form
	     (make-proof-in-avar-form u)))))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (type (var-to-type var))
	    (tsubst (list-transform-positive topsubst
		      (lambda (x) (tvar-form? (car x)))))
	    (type-unchanged?
	     (null? (intersection (type-to-tvars type) (map car tsubst))))
	    (new-var
	     (if type-unchanged?
		 var
		 (if (t-deg-zero? (var-to-t-deg var))
		     (type-to-new-partial-var (type-substitute type tsubst))
		     (type-to-new-var (type-substitute type tsubst)))))
	    (new-topsubst
	     (if type-unchanged?
		 topsubst
		 (append tsubst
			 (cons (list var (make-term-in-var-form new-var))
			       (list-transform-positive topsubst
				 (lambda (x)
				   (or (var-form? (car x))
				       (pvar-form? (car x)))))))))
	    (new-topsubst-gg
	     (if type-unchanged?
		 topsubst-gg
		 (append tsubst
			 (cons (list var (make-term-in-var-form new-var))
			       (list-transform-positive topsubst-gg
				 (lambda (x)
				   (or (var-form? (car x))
				       (pvar-form? (car x)))))))))
	    (subst-kernel (formula-substitute kernel topsubst))
	    (subst-kernel-gg ;W[A]^g
	     (formula-to-goedel-gentzen-translation subst-kernel))
	    (u (formula-to-new-avar (make-all new-var subst-kernel-gg))))
       (make-proof-in-imp-intro-form
	u (make-proof-in-all-intro-form
	   new-var (make-proof-in-imp-elim-form
		    (wiping-formula-to-proof-aux
		     kernel new-topsubst new-topsubst-gg)
		    (make-proof-in-all-elim-form
		     (make-proof-in-avar-form u)
		     (make-term-in-var-form new-var)))))))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (type (var-to-type var))
	    (tsubst (list-transform-positive topsubst
		      (lambda (x) (tvar-form? (car x)))))
	    (type-unchanged?
	     (null? (intersection (type-to-tvars type) (map car tsubst))))
	    (new-var
	     (if type-unchanged?
		 var
		 (if (t-deg-zero? (var-to-t-deg var))
		     (type-to-new-partial-var (type-substitute type tsubst))
		     (type-to-new-var (type-substitute type tsubst)))))
	    (new-topsubst
	     (if type-unchanged?
		 topsubst
		 (append tsubst
			 (cons (list var (make-term-in-var-form new-var))
			       (list-transform-positive topsubst
				 (lambda (x)
				   (or (var-form? (car x))
				       (pvar-form? (car x)))))))))
	    (new-topsubst-gg
	     (if type-unchanged?
		 topsubst-gg
		 (append tsubst
			 (cons (list var (make-term-in-var-form new-var))
			       (list-transform-positive topsubst-gg
				 (lambda (x)
				   (or (var-form? (car x))
				       (pvar-form? (car x)))))))))
	    (subst-kernel (formula-substitute kernel topsubst))
	    (subst-kernel-gg ;W[A]^g
	     (formula-to-goedel-gentzen-translation subst-kernel))
	    (u (formula-to-new-avar (make-allnc new-var subst-kernel-gg))))
       (make-proof-in-imp-intro-form
	u (make-proof-in-allnc-intro-form
	   new-var (make-proof-in-imp-elim-form
		    (wiping-formula-to-proof-aux
		     kernel new-topsubst new-topsubst-gg)
		    (make-proof-in-allnc-elim-form
		     (make-proof-in-avar-form u)
		     (make-term-in-var-form new-var)))))))
    (else (myerror "wiping-formula-to-proof-aux" "unexpected formula"
		   formula))))

(define (isolating-formula-to-proof formula . opt-topsubst)
  (let* ((orig-topsubst
	  (if (null? opt-topsubst) empty-subst (car opt-topsubst)))
	 (orig-topsubst-gg
	  (map (lambda (item)
		 (if (pvar-form? (car item))
		     (let* ((pvar (car item))
			    (cterm (cadr item))
			    (vars (cterm-to-vars cterm))
			    (formula (cterm-to-formula cterm))
			    (formula-gg
			     (formula-to-goedel-gentzen-translation formula)))
		       (list pvar (apply make-cterm
					 (append vars (list formula-gg)))))
		     item))
	       orig-topsubst))
	 (pvars (remove (predicate-form-to-predicate falsity-log)
			(formula-to-pvars formula)))
	 (extra-pvars (set-minus pvars (map car orig-topsubst)))
	 (extra-psubst-gg
	  (map (lambda (pvar)
		 (let* ((arity (pvar-to-arity pvar))
			(types (arity-to-types arity))
			(vars (map type-to-new-partial-var types))
			(varterms (map make-term-in-var-form vars))
			(formula (apply make-predicate-formula pvar varterms))
			(formula-gg (make-negation-log
				     (make-negation-log formula))))
		   (list pvar
			 (apply make-cterm
				(append vars (list formula-gg))))))
	       extra-pvars))
	 (topsubst-gg (append orig-topsubst-gg extra-psubst-gg)))
    (isolating-formula-to-proof-aux formula orig-topsubst topsubst-gg)))

(define (isolating-formula-to-proof-aux formula topsubst topsubst-gg)
  (cond
   ((wiping-formula? formula)
    (let* ((subst-formula (formula-substitute formula topsubst))
	   (subst-formula-gg ;W[A]^g
	    (formula-to-goedel-gentzen-translation subst-formula))
	   (gg-subst-formula ;W[A^g]
	    (formula-substitute formula topsubst-gg))
	   (u (formula-to-new-avar subst-formula-gg))
	   (v (formula-to-new-avar (mk-neg-log gg-subst-formula))))
      (mk-proof-in-intro-form
       u v (make-proof-in-imp-elim-form
	    (make-proof-in-avar-form v)
	    (make-proof-in-imp-elim-form
	     (wiping-formula-to-proof-aux formula topsubst topsubst-gg)
	     (make-proof-in-avar-form u))))))
   ((prime-form? formula)
    (let* ((tosubst (list-transform-positive topsubst
		      (lambda (x) (or (tvar-form? (car x))
				      (var-form? (car x))))))
	   (subst-formula (formula-substitute formula tosubst))
	   (u (formula-to-new-avar (mk-neg-log (mk-neg-log subst-formula)))))
      (make-proof-in-imp-intro-form
       u (make-proof-in-avar-form u))))
   ((and-form? formula)
    (let* ((subst-formula (formula-substitute formula topsubst))
	   (subst-formula-gg ;(I1 & I2)[A]^g
	    (formula-to-goedel-gentzen-translation subst-formula))
	   (u (formula-to-new-avar subst-formula-gg))
	   (left (and-form-to-left formula))
	   (right (and-form-to-right formula))
	   (v (formula-to-new-avar (make-negation-log formula)))
	   (w1 (formula-to-new-avar left))
	   (w2 (formula-to-new-avar right)))
      (mk-proof-in-intro-form
       u v (mk-proof-in-elim-form
	    (isolating-formula-to-proof-aux right topsubst topsubst-gg)
	    (make-proof-in-and-elim-right-form
	     (make-proof-in-avar-form u))
	    (make-proof-in-imp-intro-form
	     w2 (mk-proof-in-elim-form
		 (isolating-formula-to-proof-aux left topsubst topsubst-gg)
		 (make-proof-in-and-elim-left-form
		  (make-proof-in-avar-form u))
		 (make-proof-in-imp-intro-form
		  w1 (make-proof-in-imp-elim-form
		      (make-proof-in-avar-form v)
		      (make-proof-in-and-intro-form
		       (make-proof-in-avar-form w1)
		       (make-proof-in-avar-form w2))))))))))
   (else (myerror "isolating-formula-to-proof-aux" "unexpected formula"
		  formula))))

;; Now we can define the Goedel-Gentzen translation.

(define (proof-to-goedel-gentzen-translation proof)
  (let ((avar-to-goedel-gentzen-avar
	 (let ((assoc-list '()))
	   (lambda (avar)
	     (let ((info (assoc-wrt avar=? avar assoc-list)))
	       (if info
		   (cadr info)
		   (let ((new-avar (formula-to-new-avar
				    (formula-to-goedel-gentzen-translation
				     (avar-to-formula avar)))))
		     (set! assoc-list (cons (list avar new-avar) assoc-list))
		     new-avar)))))))
    (proof-to-goedel-gentzen-translation-aux
     proof avar-to-goedel-gentzen-avar)))

(define (proof-to-goedel-gentzen-translation-aux proof
						 avar-to-goedel-gentzen-avar)
  (case (tag proof)
    ((proof-in-avar-form)
     (let ((avar (proof-in-avar-form-to-avar proof)))
       (make-proof-in-avar-form
	(avar-to-goedel-gentzen-avar avar))))
    ((proof-in-aconst-form)
     (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	    (name (aconst-to-name aconst))
	    (kind (aconst-to-kind aconst))
	    (uninst-formula (aconst-to-uninst-formula aconst))
	    (topsubst (aconst-to-tpsubst aconst))
	    (repro-data (aconst-to-repro-data aconst))
	    (inst-formula (aconst-to-inst-formula aconst))
	    (free (formula-to-free inst-formula)))
       (cond
	((spreading-formula? inst-formula)
	 (apply
	  mk-proof-in-nc-intro-form
	  (append
	   free
	   (list (make-proof-in-imp-elim-form
		  (spreading-formula-to-proof inst-formula)
		  (apply mk-proof-in-elim-form
			 proof (map make-term-in-var-form free)))))))
	((spreading-formula? uninst-formula)
	 (let* ((pvars (remove (predicate-form-to-predicate falsity-log)
			       (formula-to-pvars uninst-formula)))
		(extra-pvars (set-minus pvars (map car topsubst)))
		(extra-psubst-gg
		 (map (lambda (pvar)
			(let* ((arity (pvar-to-arity pvar))
			       (types (arity-to-types arity))
			       (vars (map type-to-new-partial-var types))
			       (varterms (map make-term-in-var-form vars))
			       (formula (apply make-predicate-formula
					       pvar varterms))
			       (formula-gg (make-negation-log
					    (make-negation-log formula))))
			  (list pvar
				(apply make-cterm
				       (append vars (list formula-gg))))))
		      extra-pvars))
		(orig-topsubst-gg
		 (map (lambda (item)
			(if (pvar-form? (car item))
			    (let* ((pvar (car item))
				   (cterm (cadr item))
				   (vars (cterm-to-vars cterm))
				   (formula (cterm-to-formula cterm))
				   (formula-gg
				    (formula-to-goedel-gentzen-translation
				     formula)))
			      (list pvar
				    (apply make-cterm
					   (append vars (list formula-gg)))))
			    item))
		      topsubst))
		(topsubst-gg (append orig-topsubst-gg extra-psubst-gg))
		(subst-aconst
		 (apply make-aconst
			name kind uninst-formula topsubst-gg
			repro-data)))
	   (apply
	    mk-proof-in-nc-intro-form
	    (append
	     free
	     (list (make-proof-in-imp-elim-form
		    (spreading-formula-to-proof uninst-formula topsubst)
		    (apply mk-proof-in-elim-form
			   (make-proof-in-aconst-form subst-aconst)
			   (map make-term-in-var-form free))))))))
	((eq? 'theorem kind)
	 (proof-to-goedel-gentzen-translation-aux
	  (theorem-name-to-proof name) avar-to-goedel-gentzen-avar))
	(else (myerror "proof-to-goedel-gentzen-translation-aux"
		       "unexpected aconst of kind" kind "with formula"
		       formula)))))
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (u (avar-to-goedel-gentzen-avar avar))
	    (kernel (proof-in-imp-intro-form-to-kernel proof)))
       (make-proof-in-imp-intro-form
	u (proof-to-goedel-gentzen-translation-aux
	   kernel avar-to-goedel-gentzen-avar))))
    ((proof-in-imp-elim-form)
     (let* ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof))
	    (prev-op (proof-to-goedel-gentzen-translation-aux
		      op avar-to-goedel-gentzen-avar))
	    (prev-arg (proof-to-goedel-gentzen-translation-aux
		       arg avar-to-goedel-gentzen-avar)))
       (make-proof-in-imp-elim-form prev-op prev-arg)))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (u (avar-to-goedel-gentzen-avar avar))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof)))
       (make-proof-in-impnc-intro-form
	u (proof-to-goedel-gentzen-translation-aux
	   kernel avar-to-goedel-gentzen-avar))))
    ((proof-in-impnc-elim-form)
     (let* ((op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof))
	    (prev-op (proof-to-goedel-gentzen-translation-aux
		      op avar-to-goedel-gentzen-avar))
	    (prev-arg (proof-to-goedel-gentzen-translation-aux
		       arg avar-to-goedel-gentzen-avar)))
       (make-proof-in-impnc-elim-form prev-op prev-arg)))
    ((proof-in-and-intro-form)
     (make-proof-in-and-intro-form
      (proof-to-goedel-gentzen-translation-aux
       (proof-in-and-intro-form-to-left proof)
       avar-to-goedel-gentzen-avar)
      (proof-to-goedel-gentzen-translation-aux
       (proof-in-and-intro-form-to-right proof)
       avar-to-goedel-gentzen-avar)))
    ((proof-in-and-elim-left-form)
     (make-proof-in-and-elim-left-form
      (proof-to-goedel-gentzen-translation-aux
       (proof-in-and-elim-left-form-to-kernel proof)
       avar-to-goedel-gentzen-avar)))
    ((proof-in-and-elim-right-form)
     (make-proof-in-and-elim-right-form
      (proof-to-goedel-gentzen-translation-aux
       (proof-in-and-elim-right-form-to-kernel proof)
       avar-to-goedel-gentzen-avar)))
    ((proof-in-all-intro-form)
     (let* ((var (proof-in-all-intro-form-to-var proof))
	    (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-proof-in-all-intro-form
	var (proof-to-goedel-gentzen-translation-aux
	     kernel avar-to-goedel-gentzen-avar))))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
       (make-proof-in-all-elim-form
	(proof-to-goedel-gentzen-translation-aux
	 op avar-to-goedel-gentzen-avar)
	arg)))
    ((proof-in-allnc-intro-form)
     (let* ((var (proof-in-allnc-intro-form-to-var proof))
	    (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-proof-in-allnc-intro-form
	var (proof-to-goedel-gentzen-translation-aux
	     kernel avar-to-goedel-gentzen-avar))))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof))
	   (arg (proof-in-allnc-elim-form-to-arg proof)))
       (make-proof-in-allnc-elim-form
	(proof-to-goedel-gentzen-translation-aux
	 op avar-to-goedel-gentzen-avar)
	arg)))
    (else (myerror "proof-to-goedel-gentzen-translation-aux"
		   "proof tag expected" (tag proof)))))

;; Notice that the Goedel-Gentzen translation double negates every
;; atom, and hence may produce triple negations.  However, we can
;; systematically replace triple negations by single ones.

;; For a formula A let A* be the formula obtaind by replacing triple
;; negations whenever possible by single negations.

(define (formula-to-formula-without-triple-negations-log formula)
  (if ;formula is triple negation
   (and (imp-form? formula)
	(formula=? falsity-log (imp-form-to-conclusion formula))
	(imp-form? (imp-form-to-premise formula))
	(formula=? falsity-log (imp-form-to-conclusion
				(imp-form-to-premise formula)))
	(imp-form? (imp-form-to-premise (imp-form-to-premise formula)))
	(formula=? falsity-log (imp-form-to-conclusion
				(imp-form-to-premise
				 (imp-form-to-premise formula)))))
   (formula-to-formula-without-triple-negations-log
    (imp-form-to-premise (imp-form-to-premise formula)))
   (case (tag formula)
     ((atom predicate) formula)
     ((imp)
      (let* ((prem (imp-form-to-premise formula))
	     (concl (imp-form-to-conclusion formula))
	     (prev1 (formula-to-formula-without-triple-negations-log prem))
	     (prev2 (formula-to-formula-without-triple-negations-log concl)))
	(make-imp prev1 prev2)))
     ((impnc)
      (let* ((prem (impnc-form-to-premise formula))
	     (concl (impnc-form-to-conclusion formula))
	     (prev1 (formula-to-formula-without-triple-negations-log prem))
	     (prev2 (formula-to-formula-without-triple-negations-log concl)))
	(make-impnc prev1 prev2)))
     ((and)
      (let* ((left (and-form-to-left formula))
	     (right (and-form-to-right formula))
	     (prev1 (formula-to-formula-without-triple-negations-log left))
	     (prev2 (formula-to-formula-without-triple-negations-log right)))
	(make-and prev1 prev2)))
     ((all)
      (let* ((var (all-form-to-var formula))
	     (kernel (all-form-to-kernel formula))
	     (prev (formula-to-formula-without-triple-negations-log kernel)))
	(make-all var prev)))
     ((allnc)
      (let* ((var (allnc-form-to-var formula))
	     (kernel (allnc-form-to-kernel formula))
	     (prev (formula-to-formula-without-triple-negations-log kernel)))
	(make-allnc var prev)))
     (else
      (myerror
       "formula-to-formula-without-triple-negations-log" "unexpected formula"
       formula)))))

;; We simultaneously construct derivations of (1) A -> A* and (2) A* -> A

(define (formula-to-rm-triple-negations-log-proof1 formula)
  (let ((reduced-formula
	 (formula-to-formula-without-triple-negations-log formula)))
    (case (tag formula)
      ((atom predicate)
       (let ((u (formula-to-new-avar formula)))
	 (make-proof-in-imp-intro-form
	  u (make-proof-in-avar-form u))))
      ((imp)
       (let ((prem (imp-form-to-premise formula))
	     (concl (imp-form-to-conclusion formula))
	     (u (formula-to-new-avar formula)))
	 (if ;formula is a triple negation
	  (and (formula=? falsity-log concl)
	       (imp-form? prem)
	       (formula=? falsity-log (imp-form-to-conclusion prem))
	       (imp-form? (imp-form-to-premise prem))
	       (formula=? falsity-log (imp-form-to-conclusion
				       (imp-form-to-premise prem))))
	  (let ((v (formula-to-new-avar (imp-form-to-premise prem)))
		(w (formula-to-new-avar (imp-form-to-premise
					 (imp-form-to-premise prem)))))
	    (make-proof-in-imp-intro-form
	     u (make-proof-in-imp-elim-form
		(formula-to-rm-triple-negations-log-proof1
		 (imp-form-to-premise prem))
		(make-proof-in-imp-intro-form
		 w (make-proof-in-imp-elim-form
		    (make-proof-in-avar-form u)
		    (make-proof-in-imp-intro-form
		     v (make-proof-in-imp-elim-form
			(make-proof-in-avar-form v)
			(make-proof-in-avar-form w))))))))
	  (let ((v (formula-to-new-avar
		    (formula-to-formula-without-triple-negations-log prem))))
	    (mk-proof-in-intro-form
	     u v (make-proof-in-imp-elim-form
		  (formula-to-rm-triple-negations-log-proof1 concl)
		  (make-proof-in-imp-elim-form
		   (make-proof-in-avar-form u)
		   (make-proof-in-imp-elim-form
		    (formula-to-rm-triple-negations-log-proof2 prem)
		    (make-proof-in-avar-form v)))))))))
      ((impnc)
       (let ((prem (impnc-form-to-premise formula))
	     (concl (impnc-form-to-conclusion formula))
	     (u (formula-to-new-avar formula)))
	 (if ;formula is a triple negation
	  (and (formula=? falsity-log concl)
	       (imp-form? prem)
	       (formula=? falsity-log (imp-form-to-conclusion prem))
	       (imp-form? (imp-form-to-premise prem))
	       (formula=? falsity-log (imp-form-to-conclusion
				       (imp-form-to-premise prem))))
	  (let ((v (formula-to-new-avar (imp-form-to-premise prem)))
		(w (formula-to-new-avar (imp-form-to-premise
					 (imp-form-to-premise prem)))))
	    (make-proof-in-imp-intro-form
	     u (make-proof-in-imp-elim-form
		(formula-to-rm-triple-negations-log-proof1
		 (imp-form-to-premise prem))
		(make-proof-in-imp-intro-form
		 w (make-proof-in-imp-elim-form
		    (make-proof-in-avar-form u)
		    (make-proof-in-imp-intro-form
		     v (make-proof-in-imp-elim-form
			(make-proof-in-avar-form v)
			(make-proof-in-avar-form w))))))))
	  (let ((v (formula-to-new-avar
		    (formula-to-formula-without-triple-negations-log prem))))
	    (make-proof-in-imp-intro-form
	     u (make-proof-in-impnc-intro-form
		v (make-proof-in-imp-elim-form
		   (formula-to-rm-triple-negations-log-proof1 concl)
		   (make-proof-in-impnc-elim-form
		    (make-proof-in-avar-form u)
		    (make-proof-in-imp-elim-form
		     (formula-to-rm-triple-negations-log-proof2 prem)
		     (make-proof-in-avar-form v))))))))))
      ((all)
       (let ((var (all-form-to-var formula))
	     (kernel (all-form-to-kernel formula))
	     (u (formula-to-new-avar formula)))
	 (make-proof-in-imp-intro-form
	  u (make-proof-in-all-intro-form
	     var (make-proof-in-imp-elim-form
		  (formula-to-rm-triple-negations-log-proof1 kernel)
		  (make-proof-in-all-elim-form
		   (make-proof-in-avar-form u)
		   (make-term-in-var-form var)))))))
      ((allnc)
       (let ((var (allnc-form-to-var formula))
	     (kernel (allnc-form-to-kernel formula))
	     (u (formula-to-new-avar formula)))
	 (make-proof-in-imp-intro-form
	  u (make-proof-in-allnc-intro-form
	     var (make-proof-in-imp-elim-form
		  (formula-to-rm-triple-negations-log-proof1 kernel)
		  (make-proof-in-allnc-elim-form
		   (make-proof-in-avar-form u)
		   (make-term-in-var-form var)))))))
      (else (myerror
	     "formula-to-rm-triple-negations-log-proof1" "unexpected formula"
	     formula)))))

(define (formula-to-rm-triple-negations-log-proof2 formula)
  (let ((reduced-formula
	 (formula-to-formula-without-triple-negations-log formula)))
    (case (tag formula)
      ((atom predicate)
       (let ((u (formula-to-new-avar formula)))
	 (make-proof-in-imp-intro-form
	  u (make-proof-in-avar-form u))))
      ((imp)
       (let ((prem (imp-form-to-premise formula))
	     (concl (imp-form-to-conclusion formula))
	     (u (formula-to-new-avar reduced-formula)))
	 (if ;formula is a triple negation
	  (and (formula=? falsity-log concl)
	       (imp-form? prem)
	       (formula=? falsity-log (imp-form-to-conclusion prem))
	       (imp-form? (imp-form-to-premise prem))
	       (formula=? falsity-log (imp-form-to-conclusion
				       (imp-form-to-premise prem))))
	  (let ((v (formula-to-new-avar prem)))
	    (mk-proof-in-intro-form
	     u v (make-proof-in-imp-elim-form
		  (make-proof-in-avar-form v)
		  (make-proof-in-imp-elim-form
		   (formula-to-rm-triple-negations-log-proof2
		    (imp-form-to-premise prem))
		   (make-proof-in-avar-form u)))))
	  (let ((v (formula-to-new-avar prem)))
	    (mk-proof-in-intro-form
	     u v (make-proof-in-imp-elim-form
		  (formula-to-rm-triple-negations-log-proof2 concl)
		  (make-proof-in-imp-elim-form
		   (make-proof-in-avar-form u)
		   (make-proof-in-imp-elim-form
		    (formula-to-rm-triple-negations-log-proof1 prem)
		    (make-proof-in-avar-form v)))))))))
      ((impnc)
       (let ((prem (impnc-form-to-premise formula))
	     (concl (impnc-form-to-conclusion formula))
	     (u (formula-to-new-avar reduced-formula)))
	 (if ;formula is a triple negation
	  (and (formula=? falsity-log concl)
	       (imp-form? prem)
	       (formula=? falsity-log (imp-form-to-conclusion prem))
	       (imp-form? (imp-form-to-premise prem))
	       (formula=? falsity-log (imp-form-to-conclusion
				       (imp-form-to-premise prem))))
	  (let ((v (formula-to-new-avar prem)))
	    (mk-proof-in-intro-form
	     u v (make-proof-in-imp-elim-form
		  (make-proof-in-avar-form v)
		  (make-proof-in-imp-elim-form
		   (formula-to-rm-triple-negations-log-proof2
		    (imp-form-to-premise prem))
		   (make-proof-in-avar-form u)))))
	  (let ((v (formula-to-new-avar prem)))
	    (make-proof-in-imp-intro-form
	     u (make-proof-in-impnc-intro-form
		v (make-proof-in-imp-elim-form
		   (formula-to-rm-triple-negations-log-proof2 concl)
		   (make-proof-in-impnc-elim-form
		    (make-proof-in-avar-form u)
		    (make-proof-in-imp-elim-form
		     (formula-to-rm-triple-negations-log-proof1 prem)
		     (make-proof-in-avar-form v))))))))))
      ((all)
       (let ((var (all-form-to-var formula))
	     (kernel (all-form-to-kernel formula))
	     (u (formula-to-new-avar
		 (formula-to-formula-without-triple-negations-log formula))))
	 (make-proof-in-imp-intro-form
	  u (make-proof-in-all-intro-form
	     var (make-proof-in-imp-elim-form
		  (formula-to-rm-triple-negations-log-proof2 kernel)
		  (make-proof-in-all-elim-form
		   (make-proof-in-avar-form u)
		   (make-term-in-var-form var)))))))
      ((allnc)
       (let ((var (allnc-form-to-var formula))
	     (kernel (allnc-form-to-kernel formula))
	     (u (formula-to-new-avar
		 (formula-to-formula-without-triple-negations-log formula))))
	 (make-proof-in-imp-intro-form
	  u (make-proof-in-allnc-intro-form
	     var (make-proof-in-imp-elim-form
		  (formula-to-rm-triple-negations-log-proof2 kernel)
		  (make-proof-in-allnc-elim-form
		   (make-proof-in-avar-form u)
		   (make-term-in-var-form var)))))))
      (else (myerror
	     "formula-to-rm-triple-negations-log-proof2" "unexpected formula"
	     formula)))))

;; Now we can refine the Goedel-Gentzen translation accordingly.

(define (proof-to-reduced-goedel-gentzen-translation proof)
  (let* ((avar-to-goedel-gentzen-avar
	  (let ((assoc-list '()))
	    (lambda (avar)
	      (let ((info (assoc-wrt avar=? avar assoc-list)))
		(if info
		    (cadr info)
		    (let ((new-avar (formula-to-new-avar
				     (formula-to-goedel-gentzen-translation
				      (avar-to-formula avar)))))
		      (set! assoc-list (cons (list avar new-avar) assoc-list))
		      new-avar))))))
	 (proof-gg (proof-to-goedel-gentzen-translation-aux
		    proof avar-to-goedel-gentzen-avar))
	 (formula-gg (proof-to-formula proof-gg))
	 (proof1 ;of formula-gg -> formula-gg*
	  (formula-to-rm-triple-negations-log-proof1 formula-gg)))
    (make-proof-in-imp-elim-form proof1 proof-gg)))

;; 10-7. Existence formulas
;; ========================

;; In case of ex-formulas ex xs1 A1 ... ex xsn An and conclusion B we
;; recursively construct a proof of

;; ex xs1 A1 -> ... -> ex xsn An -> all xs1,...,xsn(A1 -> ... -> An -> B) -> B.

;; Notice that the free variables zs are not generalized here.  We assume
;; that B does not contain any variable from xs1 ... xsn free.  This is
;; checked and - if it does not hold - enforced in a preprocessing step.

(define (ex-formulas-and-concl-to-ex-elim-proof x . rest)
  (let* ((ex-formulas (list-head (cons x rest) (length rest)))
	 (concl (car (last-pair (cons x rest))))
	 (zs (apply union (map formula-to-free (cons x rest))))
	 (vars-and-kernel-list
	  (map ex-form-to-vars-and-final-kernel ex-formulas))
	 (varss (map car vars-and-kernel-list))
	 (kernels (map cadr vars-and-kernel-list))
	 (test (and (pair? ex-formulas)
		    (or (pair? (apply intersection varss))
			(pair? (intersection (apply append varss)
					     (formula-to-free concl))))))
	 (new-varss
	  (if test
	      (map (lambda (vars) (map var-to-new-var vars)) varss)
	      varss))
	 (new-kernels
	  (if test
	      (do ((l1 varss (cdr l1))
		   (l2 kernels (cdr l2))
		   (l3 new-varss (cdr l3))
		   (res '() (let* ((vars (car l1))
				   (kernel (car l2))
				   (new-vars (car l3))
				   (subst (map list
					       vars
					       (map make-term-in-var-form
						    new-vars))))
			      (cons (formula-substitute kernel subst) res))))
		  ((null? l1) (reverse res)))
	      kernels)))
    (ex-formulas-and-concl-to-ex-elim-proof-aux
     new-varss new-kernels ex-formulas concl)))

(define (ex-formulas-and-concl-to-ex-elim-proof-aux varss kernels
						    ex-formulas concl)
  (if
   (null? kernels)
   (let ((u (formula-to-new-avar concl)))
     (make-proof-in-imp-intro-form u (make-proof-in-avar-form u)))
   (let ((vars (car varss))
	 (kernel (car kernels)))
     (if
      (null? vars)
      (let* ((prev (ex-formulas-and-concl-to-ex-elim-proof-aux
		    (cdr varss) (cdr kernels) (cdr ex-formulas) concl))
	     (u1 (formula-to-new-avar kernel))
	     (us (map formula-to-new-avar (cdr ex-formulas)))
	     (flattened-varss (apply append (cdr varss)))
	     (v (formula-to-new-avar
		 (apply
		  mk-all
		  (append
		   flattened-varss
		   (list (apply mk-imp (append kernels (list concl)))))))))
	(apply
	 mk-proof-in-intro-form
	 u1 (append
	     us (cons
		 v (list
		    (apply
		     mk-proof-in-elim-form
		     prev (append
			   (map make-proof-in-avar-form us)
			   (list (apply
				  mk-proof-in-intro-form
				  (append
				   flattened-varss
				   (list (apply
					  mk-proof-in-elim-form
					  (make-proof-in-avar-form v)
					  (append
					   (map make-term-in-var-form
						flattened-varss)
					   (list (make-proof-in-avar-form
						  u1)))))))))))))))
      (let* ((prev (ex-formulas-and-concl-to-ex-elim-proof-aux
		    (cons (cdr vars) (cdr varss)) kernels
		    (cons (ex-form-to-kernel (car ex-formulas))
			  (cdr ex-formulas)) concl))
	     (ex-formula (apply mk-ex (append vars (list kernel))))
	     (zs (union (formula-to-free ex-formula) (formula-to-free concl)))
	     (aconst-proof
	      (apply
	       mk-proof-in-elim-form
	       (make-proof-in-aconst-form
		(ex-formula-and-concl-to-ex-elim-aconst ex-formula concl))
	       (map make-term-in-var-form zs)))
	     (var (car vars))
	     (u1 (formula-to-new-avar ex-formula))
	     (us (map formula-to-new-avar (cdr ex-formulas)))
	     (flattened-varss (apply append varss))
	     (v (formula-to-new-avar
		 (apply
		  mk-all
		  (append
		   flattened-varss
		   (list (apply mk-imp (append kernels (list concl))))))))
	     (w (formula-to-new-avar
		 (apply mk-ex (append (cdr vars) (list kernel))))))
	(apply
	 mk-proof-in-intro-form
	 u1 (append
	     us (cons v (list (mk-proof-in-elim-form
			       aconst-proof
			       (make-proof-in-avar-form u1)
			       (mk-proof-in-intro-form
				var w
				(apply mk-proof-in-elim-form
				       prev
				       (make-proof-in-avar-form w)
				       (append
					(map make-proof-in-avar-form us)
					(list (make-proof-in-all-elim-form
					       (make-proof-in-avar-form v)
					       (make-term-in-var-form
						var))))))))))))))))

;; Call a formula E essentially existential, if it can be transformed
;; into an existential form.  Inductive definition:

;; E ::= ex x A | A & E | E & A | decidable -> E (postponed)

;; We want to replace an implication with an essentially existential
;; premise by a formula with one existential quantifier less.
;; Application: search.  Given a formula A, reduce it to A* by
;; eliminating as many existential quantifiers as possible.  Then search
;; for a proof of A*.  Since a proof of A* -> A can be constructed easily,
;; one obtains a proof of A.

(define (formula-to-ex-red-formula formula) ;constructs A* from A
  (case (tag formula)
    ((predicate atom) formula)
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (prev-prem (formula-to-ex-red-formula prem))
	    (prev-concl (formula-to-ex-red-formula concl)))
       (if
	(ex-form? prev-prem)
	(let* ((vars-and-kernel (ex-form-to-vars-and-final-kernel prev-prem))
	       (vars (car vars-and-kernel))
	       (kernel (cadr vars-and-kernel)))
	  (if
	   (null? (intersection vars (formula-to-free prev-concl)))
	   (apply mk-all (append vars (list (make-imp kernel prev-concl))))
	   (let* ((new-vars (map var-to-new-var vars))
		  (new-varterms (map make-term-in-var-form new-vars))
		  (subst (map list vars new-varterms))
		  (new-kernel (formula-substitute kernel subst)))
	     (apply mk-all (append new-vars
				   (list (make-imp new-kernel prev-concl)))))))
	(make-imp prev-prem prev-concl))))
    ((impnc)
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula))
	    (prev-prem (formula-to-ex-red-formula prem))
	    (prev-concl (formula-to-ex-red-formula concl)))
       (if
	(ex-form? prev-prem)
	(let* ((vars-and-kernel (ex-form-to-vars-and-final-kernel prev-prem))
	       (vars (car vars-and-kernel))
	       (kernel (cadr vars-and-kernel)))
	  (if
	   (null? (intersection vars (formula-to-free prev-concl)))
	   (apply mk-all (append vars (list (make-imp kernel prev-concl))))
	   (let* ((new-vars (map var-to-new-var vars))
		  (new-varterms (map make-term-in-var-form new-vars))
		  (subst (map list vars new-varterms))
		  (new-kernel (formula-substitute kernel subst)))
	     (apply mk-all (append new-vars
				   (list (make-imp new-kernel prev-concl)))))))
	(make-impnc prev-prem prev-concl))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula))
	    (prev1 (formula-to-ex-red-formula left))
	    (prev2 (formula-to-ex-red-formula right)))
       (if
	(or (ex-form? prev1) (ex-form? prev2))
	(let* ((vars-and-kernel1 (ex-form-to-vars-and-final-kernel prev1))
	       (vars1 (car vars-and-kernel1))
	       (kernel1 (cadr vars-and-kernel1))
	       (vars-and-kernel2 (ex-form-to-vars-and-final-kernel prev2))
	       (vars2 (car vars-and-kernel2))
	       (kernel2 (cadr vars-and-kernel2)))
	  (if
	   (and (null? (intersection vars1 (formula-to-free kernel2)))
		(null? (intersection vars2 (formula-to-free kernel1)))
		(null? (intersection vars1 vars2)))
	   (apply mk-ex (append vars1 vars2 (list (make-and kernel1 kernel2))))
	   (let* ((new-vars1 (map var-to-new-var vars1))
		  (new-varterms1 (map make-term-in-var-form new-vars1))
		  (subst1 (map list vars1 new-varterms1))
		  (new-kernel1 (formula-substitute kernel1 subst1))
		  (new-vars2 (map var-to-new-var vars2))
		  (new-varterms2 (map make-term-in-var-form new-vars2))
		  (subst2 (map list vars2 new-varterms2))
		  (new-kernel2 (formula-substitute kernel2 subst2)))
	     (apply mk-ex
		    (append new-vars1 new-vars2
			    (list (make-and new-kernel1 new-kernel2)))))))
	(make-and prev1 prev2))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (prev (formula-to-ex-red-formula kernel)))
       (make-all var prev)))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (prev (formula-to-ex-red-formula kernel)))
       (make-allnc var prev)))
    ((ex)
     (let* ((var (ex-form-to-var formula))
	    (kernel (ex-form-to-kernel formula))
	    (prev (formula-to-ex-red-formula kernel)))
       (make-ex var prev)))
    (else (myerror "formula-to-ex-red-formula" "formula expected")
	  formula)))

(define (formula-to-proof-of-formula-imp-ex-red-formula formula)
  (case (tag formula)
    ((predicate atom)
     (let ((u (formula-to-new-avar formula)))
       (make-proof-in-imp-intro-form u (make-proof-in-avar-form u))))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (ex-red-prem (formula-to-ex-red-formula prem))
	    (ex-red-concl (formula-to-ex-red-formula concl))
	    (vars-and-kernel (ex-form-to-vars-and-final-kernel ex-red-prem))
	    (vars (car vars-and-kernel))
	    (kernel (cadr vars-and-kernel))
	    (test (null? (intersection vars (formula-to-free ex-red-concl))))
	    (new-vars (if test vars (map var-to-new-var vars)))
	    (new-varterms (map make-term-in-var-form new-vars))
	    (subst (map list vars new-varterms))
	    (new-kernel (if test kernel (formula-substitute kernel subst)))
	    (u1 (formula-to-new-avar new-kernel)) ;A0
	    (u2 (formula-to-new-avar formula)) ;A -> B
	    (proof-of-ex-red-prem-to-prem ;A* -> A
	     (formula-to-proof-of-ex-red-formula-imp-formula prem))
	    (proof-of-concl-to-ex-red-concl ;B -> B*
	     (formula-to-proof-of-formula-imp-ex-red-formula concl)))
       (apply
	mk-proof-in-intro-form
	u2 ;A -> B
	(append
	 new-vars ;xs
	 (list u1 ;A0
	       (make-proof-in-imp-elim-form
		proof-of-concl-to-ex-red-concl ;B -> B*
		(make-proof-in-imp-elim-form
		 (make-proof-in-avar-form u2) ;A -> B
		 (make-proof-in-imp-elim-form
		  proof-of-ex-red-prem-to-prem ;A* -> A
		  (apply
		   mk-proof-in-ex-intro-form
		   (append
		    (map make-term-in-var-form new-vars) ;xs
		    (list ex-red-prem ;A*
			  (make-proof-in-avar-form u1))))))))))))
    ((impnc)
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula))
	    (ex-red-prem (formula-to-ex-red-formula prem))
	    (ex-red-concl (formula-to-ex-red-formula concl))
	    (vars-and-kernel (ex-form-to-vars-and-final-kernel ex-red-prem))
	    (vars (car vars-and-kernel))
	    (kernel (cadr vars-and-kernel))
	    (test (null? (intersection vars (formula-to-free ex-red-concl))))
	    (new-vars (if test vars (map var-to-new-var vars)))
	    (new-varterms (map make-term-in-var-form new-vars))
	    (subst (map list vars new-varterms))
	    (new-kernel (if test kernel (formula-substitute kernel subst)))
	    (u1 (formula-to-new-avar new-kernel)) ;A0
	    (u2 (formula-to-new-avar formula)) ;A --> B
	    (proof-of-ex-red-prem-to-prem ;A* -> A
	     (formula-to-proof-of-ex-red-formula-imp-formula prem))
	    (proof-of-concl-to-ex-red-concl ;B -> B*
	     (formula-to-proof-of-formula-imp-ex-red-formula concl)))
       (apply
	mk-proof-in-intro-form
	u2 ;A --> B
	(append
	 new-vars ;xs
	 (list u1 ;A0
	       (make-proof-in-imp-elim-form
		proof-of-concl-to-ex-red-concl ;B -> B*
		(make-proof-in-impnc-elim-form
		 (make-proof-in-avar-form u2) ;A --> B
		 (make-proof-in-imp-elim-form
		  proof-of-ex-red-prem-to-prem ;A* -> A
		  (apply
		   mk-proof-in-ex-intro-form
		   (append
		    (map make-term-in-var-form new-vars) ;xs
		    (list ex-red-prem ;A*
			  (make-proof-in-avar-form u1))))))))))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula))
	    (ex-red-left (formula-to-ex-red-formula left))
	    (ex-red-right (formula-to-ex-red-formula right))
	    (vars-and-kernel1
	     (ex-form-to-vars-and-final-kernel ex-red-left))
	    (vars1 (car vars-and-kernel1))
	    (kernel1 (cadr vars-and-kernel1))
	    (vars-and-kernel2
	     (ex-form-to-vars-and-final-kernel ex-red-right))
	    (vars2 (car vars-and-kernel2))
	    (kernel2 (cadr vars-and-kernel2))
	    (test
	     (and (null? (intersection vars1 (formula-to-free kernel2)))
		  (null? (intersection vars2 (formula-to-free kernel1)))
		  (null? (intersection vars1 vars2))))
	    (new-vars1 (if test vars1 (map var-to-new-var vars1)))
	    (new-varterms1 (map make-term-in-var-form new-vars1))
	    (subst1 (map list vars1 new-varterms1))
	    (new-kernel1
	     (if test kernel1 (formula-substitute kernel1 subst1)))
	    (new-vars2 (if test vars2 (map var-to-new-var vars2)))
	    (new-varterms2 (map make-term-in-var-form new-vars2))
	    (subst2 (map list vars2 new-varterms2))
	    (new-kernel2
	     (if test kernel2 (formula-substitute kernel2 subst2)))
	    (ex-red-formula
	     (apply mk-ex
		    (append new-vars1 new-vars2
			    (list (make-and new-kernel1 new-kernel2)))))
	    (u1 (formula-to-new-avar new-kernel1)) ;A0
	    (u2 (formula-to-new-avar new-kernel2)) ;B0
	    (u3 (formula-to-new-avar formula)) ;A & B
	    (proof-of-left-to-ex-red-left ;A -> A*
	     (formula-to-proof-of-formula-imp-ex-red-formula left))
	    (proof-of-right-to-ex-red-right ;B -> B*
	     (formula-to-proof-of-formula-imp-ex-red-formula right)))
       (cond
	((and (ex-form? ex-red-left) (ex-form? ex-red-right))
	 (make-proof-in-imp-intro-form
	  u3
	  (make-proof-in-imp-elim-form
	   (make-proof-in-imp-elim-form
	    (ex-formulas-and-concl-to-ex-elim-proof ex-red-left ex-red-formula)
	    (make-proof-in-imp-elim-form
	     proof-of-left-to-ex-red-left ;A -> A*
	     (make-proof-in-and-elim-left-form
	      (make-proof-in-avar-form u3))))
	   (apply
	    mk-proof-in-intro-form
	    (append
	     new-vars1
	     (list
	      u1 ;A0
	      (make-proof-in-imp-elim-form
	       (make-proof-in-imp-elim-form
		(ex-formulas-and-concl-to-ex-elim-proof
		 ex-red-right ex-red-formula)
		(make-proof-in-imp-elim-form
		 proof-of-right-to-ex-red-right ;B -> B*
		 (make-proof-in-and-elim-right-form
		  (make-proof-in-avar-form u3))))
	       (apply
		mk-proof-in-intro-form
		(append
		 new-vars2
		 (list u2 ;B0
		       (apply
			mk-proof-in-ex-intro-form
			(append
			 (map make-term-in-var-form new-vars1)
			 (map make-term-in-var-form new-vars2)
			 (list ex-red-formula
			       (make-proof-in-and-intro-form
				(make-proof-in-avar-form u1)
				(make-proof-in-avar-form u2)))))))))))))))
	((and (not (ex-form? ex-red-left)) (ex-form? ex-red-right))
	 (make-proof-in-imp-intro-form
	  u3 ;A & B
	  (make-proof-in-imp-elim-form
	   (make-proof-in-imp-elim-form
	    (ex-formulas-and-concl-to-ex-elim-proof
	     ex-red-right ex-red-formula)
	    (make-proof-in-imp-elim-form
	     proof-of-right-to-ex-red-right ;B -> B*
	     (make-proof-in-and-elim-right-form
	      (make-proof-in-avar-form u3))))
	   (apply
	    mk-proof-in-intro-form
	    (append
	     new-vars2
	     (list
	      u2 ;B0
	      (apply
	       mk-proof-in-ex-intro-form
	       (append
		(map make-term-in-var-form new-vars2)
		(list
		 ex-red-formula
		 (make-proof-in-and-intro-form
		  (make-proof-in-imp-elim-form
		   proof-of-left-to-ex-red-left ;A -> A*
		   (make-proof-in-and-elim-left-form
		    (make-proof-in-avar-form u3)))
		  (make-proof-in-avar-form u2)))))))))))
	((and (ex-form? ex-red-left) (not (ex-form? ex-red-right)))
	 (make-proof-in-imp-intro-form
	  u3 ;A & B
	  (make-proof-in-imp-elim-form
	   (make-proof-in-imp-elim-form
	    (ex-formulas-and-concl-to-ex-elim-proof ex-red-left ex-red-formula)
	    (make-proof-in-imp-elim-form
	     proof-of-left-to-ex-red-left ;A -> A*
	     (make-proof-in-and-elim-left-form
	      (make-proof-in-avar-form u3))))
	   (apply
	    mk-proof-in-intro-form
	    (append
	     new-vars1
	     (list
	      u1 ;A0
	      (apply
	       mk-proof-in-ex-intro-form
	       (append
		(map make-term-in-var-form new-vars1)
		(list
		 ex-red-formula
		 (make-proof-in-and-intro-form
		  (make-proof-in-avar-form u1)
		  (make-proof-in-imp-elim-form
		   proof-of-right-to-ex-red-right ;B -> B*
		   (make-proof-in-and-elim-right-form
		    (make-proof-in-avar-form u3)))))))))))))
	((and (not (ex-form? ex-red-left)) (not (ex-form? ex-red-right)))
	 (make-proof-in-imp-intro-form
	  u3 (make-proof-in-and-intro-form
	      (make-proof-in-imp-elim-form
	       proof-of-left-to-ex-red-left ;A -> A*
	       (make-proof-in-and-elim-left-form
		(make-proof-in-avar-form u3)))
	      (make-proof-in-imp-elim-form
	       proof-of-right-to-ex-red-right ;B -> B*
	       (make-proof-in-and-elim-right-form
		(make-proof-in-avar-form u3))))))
	(else (myerror "formula-to-proof-of-formula-imp-ex-red-formula"
		       "this cannot happen")))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (ex-red-kernel (formula-to-ex-red-formula kernel))
	    (ex-red-formula (formula-to-ex-red-formula formula))
	    (u1 (formula-to-new-avar formula)) ;all x A
	    (proof-of-kernel-to-ex-red-kernel ;A -> A*
	     (formula-to-proof-of-formula-imp-ex-red-formula kernel)))
       (mk-proof-in-intro-form
	u1 var (make-proof-in-imp-elim-form
		proof-of-kernel-to-ex-red-kernel ;A -> A*
		(make-proof-in-all-elim-form
		 (make-proof-in-avar-form u1)
		 (make-term-in-var-form var))))))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (ex-red-kernel (formula-to-ex-red-formula kernel))
	    (ex-red-formula (formula-to-ex-red-formula formula))
	    (u1 (formula-to-new-avar formula)) ;allnc x A
	    (proof-of-kernel-to-ex-red-kernel ;A -> A*
	     (formula-to-proof-of-formula-imp-ex-red-formula kernel)))
       (mk-proof-in-intro-form
	u1 var (make-proof-in-imp-elim-form
		proof-of-kernel-to-ex-red-kernel ;A -> A*
		(make-proof-in-allnc-elim-form
		 (make-proof-in-avar-form u1)
		 (make-term-in-var-form var))))))
    ((ex)
     (let* ((var (ex-form-to-var formula))
	    (kernel (ex-form-to-kernel formula))
	    (ex-red-kernel (formula-to-ex-red-formula kernel))
	    (ex-red-formula (formula-to-ex-red-formula formula))
	    (u1 (formula-to-new-avar kernel)) ;A
	    (u2 (formula-to-new-avar formula)) ;ex x A
	    (proof-of-kernel-to-ex-red-kernel ;A -> A*
	     (formula-to-proof-of-formula-imp-ex-red-formula kernel)))
       (make-proof-in-imp-intro-form
	u2 (make-proof-in-imp-elim-form
	    (make-proof-in-imp-elim-form
	     (ex-formulas-and-concl-to-ex-elim-proof formula ex-red-formula)
	     (make-proof-in-avar-form u2))
	    (make-proof-in-all-intro-form
	     var (make-proof-in-imp-intro-form
		  u1 (make-proof-in-ex-intro-form
		      (make-term-in-var-form var)
		      ex-red-formula
		      (make-proof-in-imp-elim-form
		       proof-of-kernel-to-ex-red-kernel ;A -> A*
		       (make-proof-in-avar-form u1)))))))))
    (else (myerror
	   "formula-to-proof-of-formula-imp-ex-red-formula" "formula expected"
	   formula))))

(define (formula-to-proof-of-ex-red-formula-imp-formula formula)
  (case (tag formula)
    ((predicate atom)
     (let ((u (formula-to-new-avar formula)))
       (make-proof-in-imp-intro-form u (make-proof-in-avar-form u))))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (ex-red-prem (formula-to-ex-red-formula prem))
	    (ex-red-concl (formula-to-ex-red-formula concl))
	    (ex-red-formula (formula-to-ex-red-formula formula))
	    (u1 (formula-to-new-avar prem)) ;A
	    (u2 (formula-to-new-avar ex-red-formula)) ;(A -> B)*
	    (proof-of-ex-red-concl-to-concl ;B* -> B
	     (formula-to-proof-of-ex-red-formula-imp-formula concl))
	    (proof-of-prem-to-ex-red-prem ;A -> A*
	     (formula-to-proof-of-formula-imp-ex-red-formula prem)))
       (if
	(ex-form? ex-red-prem)
	(make-proof-in-imp-intro-form
	 u2 ;(A -> B)*
	 (make-proof-in-imp-intro-form
	  u1 ;A
	  (make-proof-in-imp-elim-form
	   proof-of-ex-red-concl-to-concl ;B* -> B
	   (make-proof-in-imp-elim-form
	    (make-proof-in-imp-elim-form
	     (ex-formulas-and-concl-to-ex-elim-proof ex-red-prem ex-red-concl)
	     (make-proof-in-imp-elim-form
	      proof-of-prem-to-ex-red-prem ;A -> A*
	      (make-proof-in-avar-form u1)))
	    (make-proof-in-avar-form u2)))))
	(make-proof-in-imp-intro-form
	 u2 ;(A -> B)*
	 (make-proof-in-imp-intro-form
	  u1 ;A
	  (make-proof-in-imp-elim-form
	   proof-of-ex-red-concl-to-concl ;B* -> B
	   (make-proof-in-imp-elim-form
	    (make-proof-in-avar-form u2) ;(A -> B)* = A* -> B*
	    (make-proof-in-imp-elim-form
	     proof-of-prem-to-ex-red-prem ;A -> A*
	     (make-proof-in-avar-form u1)))))))))
    ((impnc)
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula))
	    (ex-red-prem (formula-to-ex-red-formula prem))
	    (ex-red-concl (formula-to-ex-red-formula concl))
	    (ex-red-formula (formula-to-ex-red-formula formula))
	    (u1 (formula-to-new-avar prem)) ;A
	    (u2 (formula-to-new-avar ex-red-formula)) ;(A -> B)*
	    (proof-of-ex-red-concl-to-concl ;B* -> B
	     (formula-to-proof-of-ex-red-formula-imp-formula concl))
	    (proof-of-prem-to-ex-red-prem ;A -> A*
	     (formula-to-proof-of-formula-imp-ex-red-formula prem)))
       (if
	(ex-form? ex-red-prem)
	(make-proof-in-imp-intro-form
	 u2 ;(A -> B)*
	 (make-proof-in-impnc-intro-form
	  u1 ;A
	  (make-proof-in-imp-elim-form
	   proof-of-ex-red-concl-to-concl ;B* -> B
	   (make-proof-in-imp-elim-form
	    (make-proof-in-imp-elim-form
	     (ex-formulas-and-concl-to-ex-elim-proof ex-red-prem ex-red-concl)
	     (make-proof-in-imp-elim-form
	      proof-of-prem-to-ex-red-prem ;A -> A*
	      (make-proof-in-avar-form u1)))
	    (make-proof-in-avar-form u2)))))
	(make-proof-in-imp-intro-form
	 u2 ;(A -> B)*
	 (make-proof-in-impnc-intro-form
	  u1 ;A
	  (make-proof-in-imp-elim-form
	   proof-of-ex-red-concl-to-concl ;B* -> B
	   (make-proof-in-impnc-elim-form
	    (make-proof-in-avar-form u2) ;(A -> B)* = A* -> B*
	    (make-proof-in-imp-elim-form
	     proof-of-prem-to-ex-red-prem ;A -> A*
	     (make-proof-in-avar-form u1)))))))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula))
	    (ex-red-left (formula-to-ex-red-formula left))
	    (ex-red-right (formula-to-ex-red-formula right))
	    (vars-and-kernel1
	     (ex-form-to-vars-and-final-kernel ex-red-left))
	    (vars1 (car vars-and-kernel1))
	    (kernel1 (cadr vars-and-kernel1))
	    (vars-and-kernel2
	     (ex-form-to-vars-and-final-kernel ex-red-right))
	    (vars2 (car vars-and-kernel2))
	    (kernel2 (cadr vars-and-kernel2))
	    (test
	     (and (null? (intersection vars1 (formula-to-free kernel2)))
		  (null? (intersection vars2 (formula-to-free kernel1)))
		  (null? (intersection vars1 vars2))))
	    (new-vars1 (if test vars1 (map var-to-new-var vars1)))
	    (new-varterms1 (map make-term-in-var-form new-vars1))
	    (subst1 (map list vars1 new-varterms1))
	    (new-kernel1
	     (if test kernel1 (formula-substitute kernel1 subst1)))
	    (new-vars2 (if test vars2 (map var-to-new-var vars2)))
	    (new-varterms2 (map make-term-in-var-form new-vars2))
	    (subst2 (map list vars2 new-varterms2))
	    (new-kernel2
	     (if test kernel2 (formula-substitute kernel2 subst2)))
	    (ex-red-formula
	     (apply mk-ex
		    (append new-vars1 new-vars2
			    (list (make-and new-kernel1 new-kernel2)))))
	    (u1 (formula-to-new-avar ex-red-formula)) ;(A & B)*
	    (u2 ;A0 & B0
	     (formula-to-new-avar (make-and new-kernel1 new-kernel2)))
	    (proof-of-ex-red-left-to-left ;A* -> A
	     (formula-to-proof-of-ex-red-formula-imp-formula left))
	    (proof-of-ex-red-right-to-right ;B* -> B
	     (formula-to-proof-of-ex-red-formula-imp-formula right)))
       (cond
	((and (ex-form? ex-red-left) (ex-form? ex-red-right))
	 (make-proof-in-imp-intro-form
	  u1
	  (make-proof-in-imp-elim-form
	   (make-proof-in-imp-elim-form
	    (ex-formulas-and-concl-to-ex-elim-proof ex-red-formula formula)
	    (make-proof-in-avar-form u1))
	   (apply
	    mk-proof-in-intro-form
	    (append
	     new-vars1 new-vars2
	     (list
	      u2 ;A0 & B0
	      (make-proof-in-and-intro-form
	       (make-proof-in-imp-elim-form
		proof-of-ex-red-left-to-left ;A* -> A
		(apply
		 mk-proof-in-ex-intro-form
		 (append
		  (map make-term-in-var-form new-vars1)
		  (list
		   ex-red-left
		   (make-proof-in-and-elim-left-form
		    (make-proof-in-avar-form u2))))))
	       (make-proof-in-imp-elim-form
		proof-of-ex-red-right-to-right ;B* -> B
		(apply
		 mk-proof-in-ex-intro-form
		 (append
		  (map make-term-in-var-form new-vars2)
		  (list
		   ex-red-right
		   (make-proof-in-and-elim-right-form
		    (make-proof-in-avar-form u2)))))))))))))
	((and (not (ex-form? ex-red-left)) (ex-form? ex-red-right))
	 (make-proof-in-imp-intro-form
	  u1
	  (make-proof-in-imp-elim-form
	   (make-proof-in-imp-elim-form
	    (ex-formulas-and-concl-to-ex-elim-proof ex-red-formula formula)
	    (make-proof-in-avar-form u1))
	   (apply
	    mk-proof-in-intro-form
	    (append
	     new-vars2
	     (list
	      u2 ;A* & B0
	      (make-proof-in-and-intro-form
	       (make-proof-in-imp-elim-form
		proof-of-ex-red-left-to-left ;A* -> A
		(make-proof-in-and-elim-left-form
		 (make-proof-in-avar-form u2)))
	       (make-proof-in-imp-elim-form
		proof-of-ex-red-right-to-right ;B* -> B
		(apply
		 mk-proof-in-ex-intro-form
		 (append
		  (map make-term-in-var-form new-vars2)
		  (list
		   ex-red-right
		   (make-proof-in-and-elim-right-form
		    (make-proof-in-avar-form u2)))))))))))))
	((and (ex-form? ex-red-left) (not (ex-form? ex-red-right)))
	 (make-proof-in-imp-intro-form
	  u1
	  (make-proof-in-imp-elim-form
	   (make-proof-in-imp-elim-form
	    (ex-formulas-and-concl-to-ex-elim-proof ex-red-formula formula)
	    (make-proof-in-avar-form u1))
	   (apply
	    mk-proof-in-intro-form
	    (append
	     new-vars1
	     (list
	      u2 ;A0 & B*
	      (make-proof-in-and-intro-form
	       (make-proof-in-imp-elim-form
		proof-of-ex-red-left-to-left ;A* -> A
		(apply
		 mk-proof-in-ex-intro-form
		 (append
		  (map make-term-in-var-form new-vars1)
		  (list
		   ex-red-left
		   (make-proof-in-and-elim-left-form
		    (make-proof-in-avar-form u2))))))
	       (make-proof-in-imp-elim-form
		proof-of-ex-red-right-to-right ;B* -> B
		(make-proof-in-and-elim-right-form
		 (make-proof-in-avar-form u2))))))))))
	((and (not (ex-form? ex-red-left)) (not (ex-form? ex-red-right)))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-and-intro-form
	      (make-proof-in-imp-elim-form
	       proof-of-ex-red-left-to-left ;A* -> A
	       (make-proof-in-and-elim-left-form
		(make-proof-in-avar-form u1)))
	      (make-proof-in-imp-elim-form
	       proof-of-ex-red-right-to-right ;B* -> B
	       (make-proof-in-and-elim-right-form
		(make-proof-in-avar-form u1))))))
	(else (myerror "formula-to-proof-of-ex-red-formula-imp-formula"
		       "this cannot happen")))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (ex-red-kernel (formula-to-ex-red-formula kernel))
	    (ex-red-formula (formula-to-ex-red-formula formula))
	    (u1 (formula-to-new-avar ex-red-formula)) ;all x A*
	    (proof-of-ex-red-kernel-to-kernel ;A* -> A
	     (formula-to-proof-of-ex-red-formula-imp-formula kernel)))
       (mk-proof-in-intro-form
	u1 var (make-proof-in-imp-elim-form
		proof-of-ex-red-kernel-to-kernel ;A* -> A
		(make-proof-in-all-elim-form
		 (make-proof-in-avar-form u1)
		 (make-term-in-var-form var))))))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (ex-red-kernel (formula-to-ex-red-formula kernel))
	    (ex-red-formula (formula-to-ex-red-formula formula))
	    (u1 (formula-to-new-avar ex-red-formula)) ;allnc x A*
	    (proof-of-ex-red-kernel-to-kernel ;A* -> A
	     (formula-to-proof-of-ex-red-formula-imp-formula kernel)))
       (mk-proof-in-intro-form
	u1 var (make-proof-in-imp-elim-form
		proof-of-ex-red-kernel-to-kernel ;A* -> A
		(make-proof-in-allnc-elim-form
		 (make-proof-in-avar-form u1)
		 (make-term-in-var-form var))))))
    ((ex)
     (let* ((var (ex-form-to-var formula))
	    (kernel (ex-form-to-kernel formula))
	    (ex-red-kernel (formula-to-ex-red-formula kernel))
	    (ex-red-formula (formula-to-ex-red-formula formula))
	    (u1 (formula-to-new-avar ex-red-kernel)) ;A*
	    (u2 (formula-to-new-avar ex-red-formula)) ;ex x A*
	    (proof-of-ex-red-kernel-to-kernel ;A* -> A
	     (formula-to-proof-of-ex-red-formula-imp-formula kernel)))
       (make-proof-in-imp-intro-form
	u2 (make-proof-in-imp-elim-form
	    (make-proof-in-imp-elim-form
	     (ex-formulas-and-concl-to-ex-elim-proof ex-red-formula formula)
	     (make-proof-in-avar-form u2))
	    (make-proof-in-all-intro-form
	     var (make-proof-in-imp-intro-form
		  u1 (make-proof-in-ex-intro-form
		      (make-term-in-var-form var)
		      formula
		      (make-proof-in-imp-elim-form
		       proof-of-ex-red-kernel-to-kernel ;A* -> A
		       (make-proof-in-avar-form u1)))))))))
    (else (myerror
	   "formula-to-proof-of-ex-red-formula-imp-formula" "formula expected"
	   formula))))

;; 10-7-1. And proofs

(define (and-formula-and-concl-to-and-elim-proof and-formula concl)
  (let* ((and-avar (formula-to-new-avar and-formula))
	 (and-proof (make-proof-in-avar-form and-avar))
	 (lft-proof (make-proof-in-and-elim-left-form and-proof))
	 (rht-proof (make-proof-in-and-elim-right-form and-proof))
	 (step-fla (apply mk-imp (list (and-form-to-left and-formula)
				       (and-form-to-right and-formula)
				       concl)))
	 (step-avar (formula-to-new-avar step-fla))
	 (concl-proof
	  (apply
	   mk-proof-in-elim-form
	   (list (make-proof-in-avar-form step-avar) lft-proof rht-proof))))
    (apply mk-proof-in-intro-form (list and-avar step-avar concl-proof))))

;; 10-7-2.  Generalizing the introduction axioms for defined and, ex

;; formulas-to-and-intro-proof generalizes the introduction axioms for
;; AndD AndL AndR AndNc to more than two conjuncts.  It returns a proof
;; of As -> /\ As where the decorations of the conjunctions depend on
;; whether A_i is c.r. or n.c.

(define (formulas-to-and-intro-proof fla1 fla2 . formulas)
  (if
   (null? formulas) ;Case A B.  Treat directly
   (let* ((cterms (list (make-cterm fla1) (make-cterm fla2)))
	  (name (if (not (formula-of-nulltype? fla1))
		    (if (not (formula-of-nulltype? fla2)) "AndD" "AndL")
		    (if (not (formula-of-nulltype? fla2)) "AndR" "AndNc")))
	  (idpc (idpredconst-name-and-types-and-cterms-to-idpredconst
		 name '() cterms))
	  (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	  (free (union (formula-to-free fla1)
		       (formula-to-free fla2))))
     (apply mk-proof-in-elim-form
	    (make-proof-in-aconst-form aconst)
	    (map make-term-in-var-form free)))
   ;; Case A As with |As|>1.  Recursive call to As
   (let* ((prev (apply formulas-to-and-intro-proof (cons fla2 formulas)))
	  (u (formula-to-new-avar fla1))
	  (us (map formula-to-new-avar (cons fla2 formulas)))
	  (elim-proof1 ;of /\As
	   (apply mk-proof-in-elim-form
		  prev (map make-proof-in-avar-form us)))
	  (and-fla (proof-to-formula elim-proof1))
	  (cterms (list (make-cterm fla1) (make-cterm and-fla)))
	  (name (if (not (formula-of-nulltype? fla1))
		    (if (not (formula-of-nulltype? and-fla)) "AndD" "AndL")
		    (if (not (formula-of-nulltype? and-fla)) "AndR" "AndNc")))
	  (idpc (idpredconst-name-and-types-and-cterms-to-idpredconst
		 name '() cterms))
	  (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	  (free (apply union
		       (map formula-to-free (cons fla1 (cons fla2 formulas)))))
	  (elim-proof2
	   (apply mk-proof-in-elim-form
		  (make-proof-in-aconst-form aconst)
		  (append (map make-term-in-var-form free)
			  (list (make-proof-in-avar-form u)
				elim-proof1)))))
     (apply mk-proof-in-intro-form
	    u (append us (list elim-proof2))))))

;; vars-and-formulas-to-exand-intro-proof generalizes the introduction
;; axioms for ExDT ExLT to more than one variable and finitely many
;; conjuncts.  It proves all xs(As -> ex xs /\ As) where the
;; decorations of the conjunctions depend on whether A_i is c.r. or
;; n.c., and all existential quantifiers are exd except possibly the
;; last one, which is exl iff all As are n.c.

(define (vars-and-formulas-to-exand-intro-proof . vars-and-formulas)
  (let ((variables (list-transform-positive vars-and-formulas var-form?))
	(formulas (list-transform-positive vars-and-formulas formula-form?)))
    (if
     (null? variables)
     (apply formulas-to-and-intro-proof formulas)
     (let ((var (car variables))
	   (vars (cdr variables))	   
	   (fla (if (null? formulas)
		    (myerror "vars-and-formulas-to-exand-intro-proof"
			     "formulas expected")
		    (car formulas)))
	   (flas (cdr formulas)))
       (if (t-deg-zero? (var-to-t-deg var))
	   (myerror "vars-and-formulas-to-exand-intro-proof"
		    "total initial variable expected in" fla))
       (if
	(null? vars) ;ex x /\As with ExD or ExL
	(if
	 (null? flas) ;ex x A.  Treat directly with ExD or ExL
	 (let* ((types (list (var-to-type var)))
		(cterms (list (make-cterm var fla)))
		(name (if (formula-of-nulltype? fla) "ExLT" "ExDT"))
		(idpc (idpredconst-name-and-types-and-cterms-to-idpredconst
		       name types cterms))
		(aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
		(free (formula-to-free (aconst-to-inst-formula aconst))))
	   (apply mk-proof-in-elim-form
		  (make-proof-in-aconst-form aconst)
		  (map make-term-in-var-form free)))
	 ;; ex x /\As.  Use formulas-to-and-intro-proof
	 (let* ((and-intro-proof (apply formulas-to-and-intro-proof formulas))
		(and-fla (proof-to-formula and-intro-proof))
		(us (map formula-to-new-avar formulas))
		(elim-proof1 (apply mk-proof-in-elim-form
				    and-intro-proof
				    (map make-proof-in-avar-form us)))
		(and-fla (proof-to-formula elim-proof1))
		(t-deg (var-to-t-deg var))
		(types (list (var-to-type var)))
		(cterms (list (make-cterm var and-fla)))
		(name (if (not (formula-of-nulltype? and-fla)) "ExDT" "ExLT"))
		(idpc (idpredconst-name-and-types-and-cterms-to-idpredconst
		       name types cterms))
		(aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
		(free (remove var (apply union (map formula-to-free formulas))))
		(elim-proof2 (apply mk-proof-in-elim-form
				    (make-proof-in-aconst-form aconst)
				    (append (map make-term-in-var-form free)
					    (list (make-term-in-var-form var)
						  elim-proof1)))))
	   (apply mk-proof-in-intro-form
		  var (append us (list elim-proof2)))))
	;; ex x xs /\As.  Recursive call to xs As
	(let* ((prev (apply vars-and-formulas-to-exand-intro-proof
			    (append vars formulas)))
	       (us (map formula-to-new-avar formulas))
	       (elim-proof1
		(apply mk-proof-in-elim-form
		       prev (append (map make-term-in-var-form vars)
				    (map make-proof-in-avar-form us))))
	       (exand-fla (proof-to-formula elim-proof1))
	       (cterms (list (make-cterm var exand-fla)))
	       (types (list (var-to-type var)))
	       (name "ExDT")
	       (idpc (idpredconst-name-and-types-and-cterms-to-idpredconst
		      name types cterms))
	       (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	       (free (formula-to-free (aconst-to-inst-formula aconst)))
	       (elim-proof2 (apply mk-proof-in-elim-form
				   (make-proof-in-aconst-form aconst)
				   (append (map make-term-in-var-form free)
					   (list (make-term-in-var-form var)
						 elim-proof1)))))
	  (apply mk-proof-in-intro-form
		 var (append vars us (list elim-proof2)))))))))

;; 10-8. Basic proof constructions
;; ===============================

;; For every formula A, a proof of F -> A (i.e., ex-falso-quodlibet)
;; is constructed, and also proofs that constructors are injective and
;; have disjoint ranges.

;; For every formula A, formula-to-ef-proof returns a proof of F -> A
;; (i.e., ex-falso-quodlibet).

(define (formula-to-ef-proof formula)
  (let* ((u (formula-to-new-avar falsity))
	 (ef-proof (formula-and-falsity-avar-to-ef-proof formula u)))
    (make-proof-in-imp-intro-form u ef-proof)))

(define (formula-and-falsity-avar-to-ef-proof formula u)
  (case (tag formula)
    ((atom)
     (cond
      ((formula=? formula truth)
       (let* ((idpc (make-idpredconst "EqD" (list (make-alg "boole")) '()))
	      (initeqd-aconst ;all p p eqd p
	       (number-and-idpredconst-to-intro-aconst 0 idpc)))
	 (mk-proof-in-elim-form
	  (make-proof-in-aconst-form ;all p(p eqd True -> p)
	   eqd-true-to-atom-aconst)
	  (make-term-in-const-form true-const)
	  (mk-proof-in-elim-form
	   (make-proof-in-aconst-form initeqd-aconst)
	   (make-term-in-const-form true-const)))))
      ((formula=? formula falsity)
       (make-proof-in-avar-form u))
      (else ;use EfAtom: F -> all boole^ boole^
       (let* ((kernel (atom-form-to-kernel formula))
	      (aconst (theorem-name-to-aconst "EfAtom")))
	 (mk-proof-in-elim-form
	  (make-proof-in-aconst-form aconst)
	  (make-proof-in-avar-form u)
	  kernel)))))
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula)))
       (cond
	((or (pvar-form? pred) (predconst-form? pred) ;use global ass. Efq
	     (and (idpredconst-form? pred)
		  (let ((name (idpredconst-to-name pred)))
		    (and (assoc name COIDS)
			 (not (assoc (string-append "Init" name) THEOREMS))))))
	 (let* ((aconst (formula-to-efq-aconst formula))
		(fla (aconst-to-formula aconst))
		(vars (all-allnc-form-to-vars fla)))
	   (apply
	    mk-proof-in-elim-form
	    (make-proof-in-aconst-form aconst)
	    (append
	     (map make-term-in-var-form vars)
	     (list (make-proof-in-avar-form u))))))
	((idpredconst-form? pred)
	 (let ((name (idpredconst-to-name pred)))
	   (cond
	    ((string=? "EqD" name)
	     (let* ((t (car args))
		    (s (cadr args))
		    (type (term-to-type t))
		    (aconst ;F -> allnc alpha^,alpha^0 alpha^ eqd alpha^0
		     (theorem-name-to-aconst "EfEqD"))
		    (tvar (var-to-type
			   (all-allnc-form-to-var
			    (imp-form-to-conclusion
			     (aconst-to-uninst-formula aconst)))))
		    (subst-aconst (aconst-substitute
				   aconst (make-subst tvar type))))
	       (mk-proof-in-elim-form
		(make-proof-in-aconst-form ;F -> allnc n,m n eqd m)
		 subst-aconst)
		(make-proof-in-avar-form u) t s)))
	    ((assoc name IDS)
	     (let* ((init-aconst
		     (let ((info (assoc name COIDS)))
		       (if info ;init-aconst available
			   (let* ((init-name (string-append "Init" name))
				  (info1 (assoc init-name THEOREMS)))
			     (if info1 (cadr info1)
				 (myerror
				  "formula-and-falsity-avar-to-ef-proof"
				  "Theorem expected" init-name)))
			   (number-and-idpredconst-to-intro-aconst 0 pred))))
		    (ef-idpc-proof ;of I ts from u:F
		     (idpc-proof-and-falsity-avar-to-ef-idpc-proof
		      (make-proof-in-aconst-form init-aconst) u))
		    (concl-args (predicate-form-to-args
				 (proof-to-formula ef-idpc-proof)))
		    (eqd-proofs
		     (map
		      (lambda (t s)
			(let* ((type (term-to-type t))
			       (aconst (theorem-name-to-aconst "EfEqD"))
			       (tvar (var-to-type
				      (all-allnc-form-to-var
				       (imp-form-to-conclusion
					(aconst-to-uninst-formula aconst)))))
			       (subst-aconst
				(aconst-substitute
				 aconst (make-subst tvar type))))
			  (mk-proof-in-elim-form
			   (make-proof-in-aconst-form;F -> allnc n,m n eqd m)
			    subst-aconst)
			   (make-proof-in-avar-form u) t s)))
		      concl-args args)))
	       (eqd-proofs-and-predicate-proof-to-proof
		eqd-proofs ef-idpc-proof)))
	    ;; Code discarded 2020-07-15.  Problem: unsharp subst in Gfp
	    ;; ((assoc (idpredconst-to-name pred) COIDS)
	    ;;  (let* ((coidpc-name (idpredconst-to-name pred))
	    ;; 	    (sim-coidpc-names
	    ;; 	     (idpredconst-name-to-simidpc-names coidpc-name))
	    ;; 	    (types (idpredconst-to-types pred))
	    ;; 	    (cterms (idpredconst-to-cterms pred))
	    ;; 	    (sim-coidpcs-wo-coidpc
	    ;; 	     (map
	    ;; 	      (lambda (name)
	    ;; 		(idpredconst-name-and-types-and-cterms-to-idpredconst
	    ;; 		 name types cterms))
	    ;; 	      (remove coidpc-name sim-coidpc-names)))
	    ;; 	    (sorted-sim-coidpcs (cons pred sim-coidpcs-wo-coidpc))
	    ;; 	    (concls
	    ;; 	     (map
	    ;; 	      (lambda (coidpc)
	    ;; 		(let* ((arity (idpredconst-to-arity coidpc))
	    ;; 		       (varterms
	    ;; 			(map (lambda (type)
	    ;; 			       (make-term-in-var-form
	    ;; 				(type-to-new-partial-var type)))
	    ;; 			     (arity-to-types arity))))
	    ;; 		  (apply make-predicate-formula coidpc varterms)))
	    ;; 	      sorted-sim-coidpcs))
	    ;; 	    (imp-formulas
	    ;; 	     (map (lambda (concl) (make-imp falsity concl))
	    ;; 		  concls))
	    ;; 	    (gfp-aconst
	    ;; 	     (apply imp-formulas-to-gfp-aconst imp-formulas))
	    ;; 	    (gfp-proof (make-proof-in-aconst-form gfp-aconst))
	    ;; 	    (costep-formulas
	    ;; 	     (imp-form-to-premises ;drop final conclusion
	    ;; 	      (imp-form-to-conclusion ;drop competitor
	    ;; 	       (all-allnc-form-to-final-kernel ;drop all-allnc
	    ;; 		(aconst-to-inst-formula gfp-aconst)))))
	    ;; 	    (costep-vars-list
	    ;; 	     (map allnc-form-to-vars costep-formulas))
	    ;; 	    (costep-prems ;falsities
	    ;; 	     (map (lambda (fla) (imp-form-to-premise
	    ;; 				 (allnc-form-to-final-kernel fla)))
	    ;; 		  costep-formulas))
	    ;; 	    (costep-prem-avars
	    ;; 	     (map formula-to-new-avar costep-prems))
	    ;; 	    (costep-concls (map (lambda (fla)
	    ;; 				  (imp-form-to-final-conclusion
	    ;; 				   (allnc-form-to-final-kernel fla)))
	    ;; 				costep-formulas))
	    ;; 	    (costep-proofs
	    ;; 	     (map
	    ;; 	      (lambda (costep-vars costep-prem-avar costep-concl)
	    ;; 		(apply mk-proof-in-nc-intro-form
	    ;; 		       (append
	    ;; 			costep-vars
	    ;; 			(list (make-proof-in-imp-intro-form
	    ;; 			       costep-prem-avar
	    ;; 			       (formula-and-falsity-avar-to-ef-proof
	    ;; 				costep-concl costep-prem-avar))))))
	    ;; 	      costep-vars-list costep-prem-avars costep-concls)))
	    ;;    (apply mk-proof-in-elim-form
	    ;; 	      gfp-proof
	    ;; 	      (append args (cons (make-proof-in-avar-form u)
	    ;; 				 costep-proofs)))))
	    (else (myerror "formula-and-falsity-avar-to-ef-proof"
			   "idpredconst expected" pred)))))
	(else (myerror "formula-and-falsity-avar-to-ef-proof"
		       "idpredconst form expected" pred)))))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (prev (formula-and-falsity-avar-to-ef-proof concl u))
	    (v (formula-to-new-avar prem)))
       (make-proof-in-imp-intro-form v prev)))
    ((impnc)
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula))
	    (prev (formula-and-falsity-avar-to-ef-proof concl u))
	    (v (formula-to-new-avar prem)))
       (make-proof-in-impnc-intro-form v prev)))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula))
	    (prev1 (formula-and-falsity-avar-to-ef-proof left u))
	    (prev2 (formula-and-falsity-avar-to-ef-proof right u)))
       (make-proof-in-and-intro-form prev1 prev2)))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (prev (formula-and-falsity-avar-to-ef-proof kernel u)))
       (make-proof-in-all-intro-form var prev)))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (prev (formula-and-falsity-avar-to-ef-proof kernel u)))
       (make-proof-in-allnc-intro-form var prev)))
    ((ex)
     (let* ((var (ex-form-to-var formula))
	    (kernel (ex-form-to-kernel formula))
	    (inhab (type-to-canonical-inhabitant (var-to-type var)))
	    (subst-kernel (formula-subst kernel var inhab))
	    (prev (formula-and-falsity-avar-to-ef-proof subst-kernel u)))
       (make-proof-in-ex-intro-form inhab formula prev)))
    ((exca excl)
     (formula-and-falsity-avar-to-ef-proof (unfold-formula formula) u))
    (else (myerror "formula-and-falsity-avar-to-ef-proof" "formula expected"
		   formula))))

;; idpc-proof-and-falsity-avar-to-ef-idpc-proof expects an idpc-proof
;; of ...-> I ts and u:F.  It returns a proof of I ts from u:F, using
;; formula-and-falsity-avar-to-ef-proof

(define (idpc-proof-and-falsity-avar-to-ef-idpc-proof idpc-proof u)
  (let ((formula (proof-to-formula idpc-proof)))
    (case (tag formula)
      ((predicate) idpc-proof)
      ((imp) ;A -> B -> ... -> I ts
       (let* ((prem (imp-form-to-premise formula)) ;A
	      (concl (imp-form-to-conclusion formula)) ;B -> ... -> I ts
	      (final-concl (imp-impnc-all-allnc-form-to-final-conclusion concl))
	      (pred (if (predicate-form? final-concl)
			(predicate-form-to-predicate final-concl)
			(myerror "idpc-proof-and-falsity-avar-to-ef-idpc-proof"
				 "predicate expected" final-concl)))
	      (idpc-name
	       (if (idpredconst-form? pred)
		   (idpredconst-to-name pred)
		   (myerror "idpc-proof-and-falsity-avar-to-ef-idpc-proof"
			    "idpc expected" final-concl)))
	      (ef-prem-proof ;of A from u:F
	       (formula-and-falsity-avar-to-ef-proof prem u))
	      (prev-idpc-proof ;of B -> ... -> I ts from u:F
	       (make-proof-in-imp-elim-form idpc-proof ef-prem-proof)))
					;return proof of I ts from u:F
	 (idpc-proof-and-falsity-avar-to-ef-idpc-proof prev-idpc-proof u)))
      ((allnc all) ;allnc x^(... -> I ts)
       (let* ((var (all-allnc-form-to-var formula)) ;x^
	      (kernel (all-allnc-form-to-kernel formula)) ;... -> I ts
	      (prev-idpc-proof ;of ... -> I ts from u:F
	       (mk-proof-in-elim-form
		idpc-proof (make-term-in-var-form var))))
	 (idpc-proof-and-falsity-avar-to-ef-idpc-proof prev-idpc-proof u)))
      (else (myerror "idpc-proof-and-falsity-avar-to-ef-idpc-proof"
		     "not implemented for" formula)))))

;; Code discarded 2019-08-20.
;; ;; formula-to-efq-proof proves F -> A for every A.  To make this work
;; ;; easily for (simultaneous) inductive definitions, we assume that
;; ;; taking the initial clause of each idpc produces clauses without
;; ;; recursive calls which are terminating.  This is checked in add-ids.

;; (define (formula-to-efq-proof formula)
;;   (let* ((u (formula-to-new-avar falsity))
;; 	 (efq-proof (formula-and-falsity-avar-to-efq-proof formula u)))
;;     (make-proof-in-imp-intro-form u efq-proof)))

;; ;; (cdp (formula-to-efq-proof (pf "F")))
;; ;; (cdp (formula-to-efq-proof (pf "T")))
;; ;; (cdp (formula-to-efq-proof (pf "n=0")))
;; ;; (cdp (formula-to-efq-proof (pf "exd n n=m")))

;; (define (formula-and-falsity-avar-to-efq-proof formula u)
;;   (case (tag formula)
;;     ((atom)
;;      (cond
;;       ((formula=? formula truth)
;;        (let* ((idpc (make-idpredconst "EqD" (list (make-alg "boole")) '()))
;; 	      (initeqd-aconst ;all p p eqd p
;; 	       (number-and-idpredconst-to-intro-aconst 0 idpc)))
;; 	 (mk-proof-in-elim-form
;; 	  (make-proof-in-aconst-form ;all p(p eqd True -> p)
;; 	   eqd-true-to-atom-aconst)
;; 	  (make-term-in-const-form true-const)
;; 	  (mk-proof-in-elim-form
;; 	   (make-proof-in-aconst-form initeqd-aconst)
;; 	   (make-term-in-const-form true-const)))))
;;       ((formula=? formula falsity)
;;        (make-proof-in-avar-form u))
;;       (else ;use EfqAtom: F -> all boole^ boole^
;;        (let* ((kernel (atom-form-to-kernel formula))
;; 	      (aconst (theorem-name-to-aconst "EfqAtom")))
;; 	 (mk-proof-in-elim-form
;; 	  (make-proof-in-aconst-form aconst)
;; 	  (make-proof-in-avar-form u)
;; 	  kernel)))))
;;     ((predicate)
;;      (let ((pred (predicate-form-to-predicate formula))
;; 	   (args (predicate-form-to-args formula)))
;;        (cond ((or (pvar-form? pred) (predconst-form? pred)) ;use global ass. Efq
;; 	      (let* ((aconst (formula-to-efq-aconst formula))
;; 		     (fla (aconst-to-formula aconst))
;; 		     (vars (all-allnc-form-to-vars fla)))
;; 		(apply
;; 		 mk-proof-in-elim-form
;; 		 (make-proof-in-aconst-form aconst)
;; 		 (append
;; 		  (map make-term-in-var-form vars)
;; 		  (list (make-proof-in-avar-form u))))))
;; 	     ((idpredconst-form? pred)
;; 	      (cond
;; 	       ((string=? "EqD" (idpredconst-to-name pred))
;; 		(let* ((r (car args))
;; 		       (s (cadr args))
;; 		       (type (term-to-type r))
;; 		       (aconst ;F -> all alpha^,alpha^0 alpha^ eqd alpha^0
;; 			(theorem-name-to-aconst "EfqEqD"))
;; 		       (tvar (var-to-type
;; 			      (all-form-to-var
;; 			       (imp-form-to-conclusion
;; 				(aconst-to-uninst-formula aconst)))))
;; 		       (subst-aconst (aconst-substitute
;; 				      aconst (make-subst tvar type))))
;; 		  (mk-proof-in-elim-form
;; 		   (make-proof-in-aconst-form ;F -> all n,m n eqd m)
;; 		    subst-aconst)
;; 		   (make-proof-in-avar-form u) r s)))
;; 	       ((and (assoc (idpredconst-to-name pred) IDS)
;; 		     (not (assoc (idpredconst-to-name pred) COIDS)))
;; 		(let* ((init-aconst
;; 			(number-and-idpredconst-to-intro-aconst 0 pred))
;; 		       (init-aconst-formula (aconst-to-formula init-aconst))
;; 		       (vars (all-allnc-form-to-vars init-aconst-formula))
;; 		       (free (formula-to-free formula))
;; 		       (inhab-terms (map (lambda (var)
;; 					   (if (member var free)
;; 					       (make-term-in-var-form var)
;; 					       (type-to-canonical-inhabitant
;; 						(var-to-type var))))
;; 					 vars))
;; 		       (elim-proof1
;; 			(apply mk-proof-in-elim-form
;; 			       (make-proof-in-aconst-form init-aconst)
;; 			       inhab-terms))
;; 		       (kernel (proof-to-formula elim-proof1))
;; 		       (prems (imp-impnc-form-to-premises kernel))
;; 		       (concl ;I r1 ... rn
;; 			(imp-impnc-form-to-final-conclusion kernel))
;; 		       (concl-args (predicate-form-to-args concl))
;; 		       (ih-proofs
;; 			(map (lambda (prem)
;; 			       (formula-and-falsity-avar-to-efq-proof prem u))
;; 			     prems))
;; 		       (elim-proof ;of I r1 ... rn
;; 			(apply mk-proof-in-elim-form elim-proof1 ih-proofs))
;; 		       (eqd-proofs
;; 			(map
;; 			 (lambda (r s)
;; 			   (let* ((type (term-to-type r))
;; 				  (aconst (theorem-name-to-aconst "EfqEqD"))
;; 				  (tvar (var-to-type
;; 					 (all-form-to-var
;; 					  (imp-form-to-conclusion
;; 					   (aconst-to-uninst-formula aconst)))))
;; 				  (subst-aconst
;; 				   (aconst-substitute
;; 				    aconst (make-subst tvar type))))
;; 			     (mk-proof-in-elim-form
;; 			      (make-proof-in-aconst-form ;F -> all n,m n eqd m)
;; 			       subst-aconst)
;; 			      (make-proof-in-avar-form u) r s)))
;; 			 concl-args args)))
;; 		  (eqd-proofs-and-predicate-proof-to-proof
;; 		   eqd-proofs elim-proof)))
;; 	       ((assoc (idpredconst-to-name pred) COIDS)
;; 		(let* ((coidpc-name (idpredconst-to-name pred))
;; 		       (sim-coidpc-names
;; 			(idpredconst-name-to-simidpc-names coidpc-name))
;; 		       (types (idpredconst-to-types pred))
;; 		       (cterms (idpredconst-to-cterms pred))
;; 		       (sim-coidpcs-wo-coidpc
;; 			(map
;; 			 (lambda (name)
;; 			   (idpredconst-name-and-types-and-cterms-to-idpredconst
;; 			    name types cterms))
;; 			 (remove coidpc-name sim-coidpc-names)))
;; 		       (sorted-sim-coidpcs (cons pred sim-coidpcs-wo-coidpc))
;; 		       (concls
;; 			(map
;; 			 (lambda (coidpc)
;; 			   (let* ((arity (idpredconst-to-arity coidpc))
;; 				  (varterms
;; 				   (map (lambda (type)
;; 					  (make-term-in-var-form
;; 					   (type-to-new-partial-var type)))
;; 					(arity-to-types arity))))
;; 			     (apply make-predicate-formula coidpc varterms)))
;; 			 sorted-sim-coidpcs))
;; 		       (imp-formulas
;; 			(map (lambda (concl) (make-imp falsity concl))
;; 			     concls))
;; 		       (gfp-aconst
;; 			(apply imp-formulas-to-gfp-aconst imp-formulas))
;; 		       (gfp-proof (make-proof-in-aconst-form gfp-aconst))
;; 		       (costep-formulas
;; 			(imp-form-to-premises ;drop final conclusion
;; 			 (imp-form-to-conclusion ;drop competitor
;; 			  (all-allnc-form-to-final-kernel ;drop all-allnc
;; 			   (aconst-to-inst-formula gfp-aconst)))))
;; 		       (costep-vars-list
;; 			(map allnc-form-to-vars costep-formulas))
;; 		       (costep-prems ;falsities
;; 			(map (lambda (fla) (imp-form-to-premise
;; 					    (allnc-form-to-final-kernel fla)))
;; 			     costep-formulas))
;; 		       (costep-prem-avars
;; 			(map formula-to-new-avar costep-prems))
;; 		       (costep-concls (map (lambda (fla)
;; 					     (imp-form-to-final-conclusion
;; 					      (allnc-form-to-final-kernel fla)))
;; 					   costep-formulas))
;; 		       (costep-proofs
;; 			(map
;; 			 (lambda (costep-vars costep-prem-avar costep-concl)
;; 			   (apply mk-proof-in-nc-intro-form
;; 				  (append
;; 				   costep-vars
;; 				   (list (make-proof-in-imp-intro-form
;; 					  costep-prem-avar
;; 					  (formula-and-falsity-avar-to-efq-proof
;; 					   costep-concl costep-prem-avar))))))
;; 			 costep-vars-list costep-prem-avars costep-concls)))
;; 		  (apply mk-proof-in-elim-form
;; 			 gfp-proof
;; 			 (append args (cons (make-proof-in-avar-form u)
;; 					    costep-proofs)))))
;; 	       (else (myerror "formula-and-falsity-avar-to-efq-proof"
;; 			      "idpredconst expected" pred))))
;; 	     (else (myerror "formula-and-falsity-avar-to-efq-proof"
;; 			    "predicate expected" pred)))))
;;     ((imp)
;;      (let* ((prem (imp-form-to-premise formula))
;; 	    (concl (imp-form-to-conclusion formula))
;; 	    (prev (formula-and-falsity-avar-to-efq-proof concl u))
;; 	    (v (formula-to-new-avar prem)))
;;        (make-proof-in-imp-intro-form v prev)))
;;     ((impnc)
;;      (let* ((prem (impnc-form-to-premise formula))
;; 	    (concl (impnc-form-to-conclusion formula))
;; 	    (prev (formula-and-falsity-avar-to-efq-proof concl u))
;; 	    (v (formula-to-new-avar prem)))
;;        (make-proof-in-impnc-intro-form v prev)))
;;     ((and)
;;      (let* ((left (and-form-to-left formula))
;; 	    (right (and-form-to-right formula))
;; 	    (prev1 (formula-and-falsity-avar-to-efq-proof left u))
;; 	    (prev2 (formula-and-falsity-avar-to-efq-proof right u)))
;;        (make-proof-in-and-intro-form prev1 prev2)))
;;     ((all)
;;      (let* ((var (all-form-to-var formula))
;; 	    (kernel (all-form-to-kernel formula))
;; 	    (prev (formula-and-falsity-avar-to-efq-proof kernel u)))
;;        (make-proof-in-all-intro-form var prev)))
;;     ((allnc)
;;      (let* ((var (allnc-form-to-var formula))
;; 	    (kernel (allnc-form-to-kernel formula))
;; 	    (prev (formula-and-falsity-avar-to-efq-proof kernel u)))
;;        (make-proof-in-allnc-intro-form var prev)))
;;     ((ex)
;;      (let* ((var (ex-form-to-var formula))
;; 	    (kernel (ex-form-to-kernel formula))
;; 	    (inhab (type-to-canonical-inhabitant (var-to-type var)))
;; 	    (subst-kernel (formula-subst kernel var inhab))
;; 	    (prev (formula-and-falsity-avar-to-efq-proof subst-kernel u)))
;;        (make-proof-in-ex-intro-form inhab formula prev)))
;;     ((exca excl)
;;      (formula-and-falsity-avar-to-efq-proof (unfold-formula formula) u))
;;     (else (myerror "formula-and-falsity-avar-to-efq-proof" "formula expected"
;; 		   formula))))

(define (make-proof-in-iterated-imp-elim-form init-proof . imp-proofs)
  (if (null? imp-proofs) init-proof
      (let* ((formula (proof-to-formula init-proof)) ;A
	     (imp-proof (car imp-proofs)) ;of A -> B
	     (rest-imp-proofs (cdr imp-proofs)) ;of B -> C, C -> D ...
	     (imp-formula (proof-to-formula imp-proof))
	     (prem (if (imp-impnc-form? imp-formula)
		       (imp-impnc-form-to-premise imp-formula)
		       (myerror "make-proof-in-iterated-imp-elim-form"
				"imp or impnc form expected" imp-formula)))
	     (concl (imp-impnc-form-to-conclusion imp-formula))
	     (concl-proof ;of B
	      (if (classical-formula=? formula prem)
		  (mk-proof-in-elim-form imp-proof init-proof)
		  (myerror "make-proof-in-iterated-imp-elim-form"
			   "equal formulas expected" formula prem))))
	(apply make-proof-in-iterated-imp-elim-form
	       concl-proof rest-imp-proofs))))

;; Given eqd-proofs of r1 eqd s1, ..., rn eqd sn and a predicate-proof
;; of I r1 ... rn we construct a proof of I s1 ... sn using EqDCompat

(define (eqd-proofs-and-predicate-proof-to-proof eqd-proofs predicate-proof)
  (let* ((formula (proof-to-formula predicate-proof))
	 (pred (if (predicate-form? formula)
		   (predicate-form-to-predicate formula)
		   (myerror "eqd-proofs-and-predicate-proof-to-proof"
			    "predicate form expected" formula)))
	 (args (predicate-form-to-args formula))
	 (n (length eqd-proofs))
	 (eqds (map proof-to-formula eqd-proofs))
	 (args-list (map predicate-form-to-args eqds))
	 (rs (map car args-list))
	 (ss (map cadr args-list))
	 (types (if (apply and-op (map (lambda (term1 term2)
					 (term=? term1 term2))
				       rs args))
		    (map term-to-type rs)
		    (apply myerror
			   "eqd-proofs-and-predicate-proof-to-proof"
			   "equal terms expected" (append rs args))))
	 (vars (map type-to-new-partial-var types)) ;x1 ... xn
	 (is (list-tabulate n (lambda (i) i))) ;0 ... n-1
	 (transition-args-list ;(x1 r2 r3) (s1 x2 r3) (s1 s2 x3)
	  (map (lambda (var i)
		 (append (list-head ss i)
			 (list (make-term-in-var-form var))
			 (list-tail rs (+ i 1))))
	       vars is))
	 (cterms ;{x1|I x1 r2 r3} {x2|I s1 x2 r3} {x3|I s1 s2 x3}
	  (map (lambda (var transition-args)
		 (make-cterm
		  var (apply make-predicate-formula pred transition-args)))
	       vars transition-args-list))
	 (aconst (theorem-name-to-aconst "EqDCompat"))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (tvar (var-to-type (allnc-form-to-var uninst-formula)))
	 (final-conclusion
	  (imp-impnc-all-allnc-form-to-final-conclusion uninst-formula))
	 (pvar (predicate-form-to-predicate final-conclusion))
	 (tpsubsts
	  (map (lambda (type cterm)
		 (append (make-subst tvar type)
			 (make-subst-wrt pvar-cterm-equal? pvar cterm)))
	       types cterms))
	 (subst-aconsts (map (lambda (tpsubst)
			       (aconst-substitute aconst tpsubst))
			     tpsubsts))
	 (transition-proofs          ;of I r1 r2 r3 -> I s1 r2 r3,
					;I s1 r2 r3 -> I s1 s2 r3,
					;I s1 s2 r3 -> I s1 s2 s3
	  (map (lambda (subst-aconst r s eqd-proof)
		 (apply
		  mk-proof-in-elim-form
		  (make-proof-in-aconst-form subst-aconst)
		  (append (map make-term-in-var-form
			       (formula-to-free
				(aconst-to-inst-formula subst-aconst)))
			  (list r s eqd-proof))))
	       subst-aconsts rs ss eqd-proofs)))
    (apply make-proof-in-iterated-imp-elim-form
	   predicate-proof transition-proofs)))

(define (constructor-eqd-imp-args-eqd-proof eqd-formula . opt-index)
  (let* ((avar (formula-to-new-avar eqd-formula))
	 (eqd-proof (make-proof-in-avar-form avar)))
    (make-proof-in-imp-intro-form
     avar (apply constructor-eqd-proof-to-args-eqd-proof
		 eqd-proof opt-index))))

(define (constructor-eqd-proof-to-args-eqd-proof eqd-proof . opt-index)
  (let* ((eqd-formula (proof-to-formula eqd-proof))
	 (eqd-args (predicate-form-to-args eqd-formula))
	 (term1 (car eqd-args))
	 (term2 (cadr eqd-args))
	 (alg (term-to-type term1))
	 (alg-name (alg-form-to-name alg))
	 (typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-names (map typed-constr-name-to-name typed-constr-names))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (alg-tvars (alg-name-to-tvars alg-name))
	 (tparams (alg-form-to-types alg))
	 (tsubst (make-substitution alg-tvars tparams))
	 (subst-constr-types (map (lambda (constr-type)
				    (type-substitute constr-type tsubst))
				  constr-types))
	 (alt-vars-list
	  (map (lambda (subst-constr-type)
		 (map type-to-new-partial-var
		      (arrow-form-to-arg-types subst-constr-type)))
	       subst-constr-types))
	 (proj-index (if (null? opt-index) 0 (car opt-index)))
	 (args (term-in-app-form-to-args term1))
	 (arg-types (map term-to-type args))
	 (arg-type (if (and (integer? proj-index)
			    (not (negative? proj-index))
			    (< proj-index (length arg-types)))
		       (list-ref arg-types proj-index)
		       (myerror "constructor-eqd-proof-to-args-eqd-proof"
				"out of range" proj-index "for" term1)))
	 (op (term-in-app-form-to-final-op term1))
	 (const (if (term-in-const-form? op)
		    (term-in-const-form-to-const op)
		    (myerror "constructor-eqd-proof-to-args-eqd-proof"
			     "term in constant form expected" op)))
	 (alts (map (lambda (vars constr-name)
		      (if
		       (string=? constr-name (const-to-name const))
		       (apply mk-term-in-abst-form
			      (append vars (list (make-term-in-var-form
						  (list-ref vars proj-index)))))
		       (apply mk-term-in-abst-form
			      (append vars (list (type-to-canonical-inhabitant
						  arg-type))))))
		    alt-vars-list constr-names))
	 (var1 (type-to-new-partial-var alg))
	 (var2 (type-to-new-partial-var alg))
	 (varterm1 (make-term-in-var-form var1))
	 (varterm2 (make-term-in-var-form var2))
	 (if-term1 (make-term-in-if-form varterm1 alts))
	 (if-term2 (make-term-in-if-form varterm2 alts))
	 (imp-formula (make-imp (make-eqd varterm1 varterm2)
				(make-eqd if-term1 if-term2)))
	 (elim-aconst (imp-formulas-to-elim-aconst imp-formula))
	 (eqd-init-proof
	  (mk-proof-in-nc-intro-form
	   var1 (mk-proof-in-elim-form
		 (make-proof-in-aconst-form
		  (number-and-idpredconst-to-intro-aconst
		   0 (make-idpredconst "EqD" (list arg-type) '())))
		 if-term1))))
    (mk-proof-in-elim-form
     (make-proof-in-aconst-form elim-aconst)
     term1 term2 eqd-proof eqd-init-proof)))

(define (constructors-overlap-imp-falsity-proof eqd-formula)
  (if (not (and (formula? eqd-formula)
		(predicate-form? eqd-formula)
		(let ((pred (predicate-form-to-predicate eqd-formula))
		      (args (predicate-form-to-args eqd-formula)))
		  (and (idpredconst-form? pred)
		       (string=? "EqD" (idpredconst-to-name pred))))))
      (myerror "constructors-overlap-imp-falsity-proof"
	       "eqd-formula expected" eqd-formula))
  (let* ((pred (predicate-form-to-predicate eqd-formula))
	 (args (predicate-form-to-args eqd-formula))
	 (term1 (car args))
	 (term2 (cadr args))
	 (op1 (term-in-app-form-to-final-op term1))
	 (op2 (term-in-app-form-to-final-op term2))
	 (args1 (term-in-app-form-to-args term1))
	 (args2 (term-in-app-form-to-args term2))
	 (constr1 (if (and (term-in-const-form? op1)
			   (eq? 'constr (const-to-kind
					 (term-in-const-form-to-const op1))))
		     (term-in-const-form-to-const op1)
		     (myerror "constructors-overlap-imp-falsity-proof"
			      "constructor expected" op1)))
	 (alg (term-to-type term1))
	 (alg-name (alg-form-to-name alg))
	 (alg-tvars (alg-name-to-tvars alg-name))
	 (alg-types (alg-form-to-types alg))
	 (alg-tsubst (make-substitution alg-tvars alg-types))
	 (typed-constr-names (alg-name-to-typed-constr-names alg-name))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (subst-constr-types (map (lambda (constr-type)
				    (type-substitute constr-type alg-tsubst))
				  constr-types))
	 (subst-constr-arg-types-list
	  (map arrow-form-to-arg-types subst-constr-types))
	 (subst-constr-arg-vars-list
	  (map (lambda (types) (map type-to-new-var types))
	       subst-constr-arg-types-list))
	 (constr-names (map typed-constr-name-to-name typed-constr-names))
	 (boolean-consts (map (lambda (name)
				(if (string=? name (const-to-name constr1))
				    false-const
				    true-const))
			      constr-names))
	 (boolean-terms (map make-term-in-const-form boolean-consts))
	 (abstr-boolean-terms
	  (map (lambda (subst-constr-arg-vars boolean-term)
		 (apply mk-term-in-abst-form
			(append subst-constr-arg-vars (list boolean-term))))
	       subst-constr-arg-vars-list boolean-terms))
	 (if-term1 (make-term-in-if-form term1 abstr-boolean-terms))
	 (var (type-to-new-partial-var alg))
	 (varterm (make-term-in-var-form var))
	 (if-term2 (make-term-in-if-form varterm abstr-boolean-terms))
	 (cterm (make-cterm var (make-eqd if-term1 if-term2)))
	 (aconst (theorem-name-to-aconst "EqDCompat"))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (tvar (var-to-type (allnc-form-to-var uninst-formula)))
	 (final-conclusion
	  (imp-impnc-all-allnc-form-to-final-conclusion uninst-formula))
	 (pvar (predicate-form-to-predicate final-conclusion))
	 (tsubst (make-subst tvar alg))
	 (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm))
	 (inst-aconst (make-aconst (aconst-to-name aconst) ;"EqDCompat"
				   (aconst-to-kind aconst) ;'theorem
				   uninst-formula
				   (append tsubst psubst)))
	 (free (term-to-free term1))
	 (avar (formula-to-new-avar eqd-formula))
	 (idpc (make-idpredconst "EqD" (list (py "boole")) '()))
	 (initeqd-aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	 (initeqd-proof (mk-proof-in-elim-form
			 (make-proof-in-aconst-form initeqd-aconst)
			 if-term1))
	 (elim-proof (apply mk-proof-in-elim-form
			    (make-proof-in-aconst-form inst-aconst)
			    (append (map make-term-in-var-form free)
				    (list term1 term2
					  (make-proof-in-avar-form avar)
					  initeqd-proof)))))
    (apply mk-proof-in-nc-intro-form
	   (append (formula-to-free eqd-formula)
		   (list (make-proof-in-imp-intro-form avar elim-proof))))))

;; Assume that A is folded, in the sense that quantification is over
;; total variables only.  Let A' be the result of unfolding A:

;; all x B(x) unfolds to allnc x^(T x^ -> B'(x^))
;; allnc x B(x) unfolds to allnc x^(T x^ --> B'(x^))
;; exd x B(x) unfolds to exr x^(T x^ andd B'(x^))
;; exl x B(x) unfolds to exr x^(T x^ andl B'(x^))
;; exr x B(x) unfolds to exr x^(T x^ andr B'(x^))
;; exnc x B(x) unfolds to exr x^(T x^ andnc B'(x^))
;; ex x B(x) unfolds to exr x^(T x^ & B'(x^))

;; unfold-total-variables applied to A returns A'.  The total variables
;; x to be replaced by x^ are optional arguments.  This replacement has
;; to be done everywhere, and hence the first argument can be a
;; variable, a term, a formula or a cterm.  fold-total-variables
;; applied to A' returns A.

(define (unfold-total-variables expr . vars)
  (cond
   ((var-form? expr)
    (if (member expr vars)
	(make-var (var-to-type expr)
		  (var-to-index expr)
		  t-deg-zero
		  (var-to-name expr))
	expr))
   ((term-in-var-form? expr)
    (let ((var (term-in-var-form-to-var expr)))
      (make-term-in-var-form (apply unfold-total-variables var vars))))
   ((term-in-const-form? expr) expr)
   ((term-in-abst-form? expr)
    (let ((var (term-in-abst-form-to-var expr))
	  (kernel (term-in-abst-form-to-kernel expr)))
      (make-term-in-abst-form (apply unfold-total-variables var vars)
			      (apply unfold-total-variables kernel vars))))
   ((term-in-app-form? expr)
    (let ((op (term-in-app-form-to-op expr))
	  (arg (term-in-app-form-to-arg expr)))
      (make-term-in-app-form (apply unfold-total-variables op vars)
			     (apply unfold-total-variables arg vars))))
   ((term-in-pair-form? expr)
    (let ((left (term-in-pair-form-to-left expr))
	  (right (term-in-pair-form-to-right expr)))
      (make-term-in-pair-form (apply unfold-total-variables left vars)
			      (apply unfold-total-variables right vars))))
   ((term-in-lcomp-form? expr)
    (let ((kernel (term-in-lcomp-form-to-kernel expr)))
      (make-term-in-lcomp-form (apply unfold-total-variables kernel vars))))
   ((term-in-rcomp-form? expr)
    (let ((kernel (term-in-rcomp-form-to-kernel expr)))
      (make-term-in-rcomp-form (apply unfold-total-variables kernel vars))))
   ((term-in-if-form? expr)
    (let ((test (term-in-if-form-to-test expr))
	  (alts (term-in-if-form-to-alts expr))
	  (rest (term-in-if-form-to-rest expr)))
      (apply make-term-in-if-form
	     (apply unfold-total-variables test vars)
	     (map (lambda (x)
		    (apply unfold-total-variables x vars))
		  (append alts rest)))))
   ((bicon-form? expr) ;to be done before inductively defined predicates
    (let ((bicon (bicon-form-to-bicon expr))
	  (left (bicon-form-to-left expr))
	  (right (bicon-form-to-right expr)))
      (make-bicon bicon
		  (apply unfold-total-variables left vars)
		  (apply unfold-total-variables right vars))))
   ((quant-form? expr) ;to be done before inductively defined predicates
    (let* ((quant (quant-form-to-quant expr))
	   (var (car (quant-form-to-vars expr)))
	   (kernel (quant-form-to-kernel expr))
	   (partial-var (if (t-deg-one? (var-to-t-deg var))
			    (make-var (var-to-type var)
				      (var-to-index var)
				      t-deg-zero
				      (var-to-name var))
			    (myerror "unfold-total-variables"
				     "quantifier over a total variable expected"
				     expr)))
	   (totality-fla
	    (term-to-totality-formula (make-term-in-var-form partial-var)))
	   (unfolded-kernel
	    (apply unfold-total-variables kernel var vars)))
      (cond
       ((all-form? expr)
	(make-allnc partial-var (make-imp totality-fla unfolded-kernel)))
       ((allnc-form? expr)
	(make-allnc partial-var (make-impnc totality-fla unfolded-kernel)))
       ((exdt-form? expr)
	(make-exr partial-var (make-andd totality-fla unfolded-kernel)))
					;commented out (andl still missing)
       ;; ((exlt-form? expr)
       ;;       (make-exr partial-var (make-andl totality-fla unfolded-kernel)))
       ((exrt-form? expr)
	(make-exr partial-var (make-andr totality-fla unfolded-kernel)))
       ((exnct-form? expr)
	(make-exr partial-var (make-andnc totality-fla unfolded-kernel)))
       ((ex-form? expr)
	(make-exr partial-var (make-and totality-fla unfolded-kernel)))
       ((or (exca-form? expr)
	    (excl-form? expr)
	    (excu-form? expr))
	(myerror "unfold-total-variables" "quantifier" quant
		 "should be unfolded"))
       ((or (exd-form? expr)
	    (exl-form? expr)
	    (exr-form? expr)
	    (exnc-form? expr))
	(myerror "unfold-total-variables" "total quantified variable expected"
		 expr))
	(else
	 (myerror "unfold-total-variables" "quantifier expected" quant)))))
   ((predicate-form? expr) ;not an inductively defined bicon or quant
    (let ((pred (predicate-form-to-predicate expr))
	  (args (predicate-form-to-args expr)))
      (cond
       ((or (pvar-form? pred) (predconst-form? pred))
	(apply make-predicate-formula
	       pred (map (lambda (arg)
			   (apply unfold-total-variables arg vars))
			 args)))
       ((idpredconst-form? pred)
	(let* ((name (idpredconst-to-name pred))
	       (types (idpredconst-to-types pred))
	       (cterms (idpredconst-to-cterms pred))
	       (idpc (make-idpredconst
		      name types
		      (map (lambda (cterm)
			     (apply unfold-total-variables cterm vars))
			   cterms))))
	  (apply make-predicate-formula
		 idpc (map (lambda (arg)
			     (apply unfold-total-variables arg vars))
			   args))))
       (else (myerror "unfold-total-variables" "predicate expected" pred)))))
   ((atom-form? expr)
    (let ((kernel (atom-form-to-kernel expr)))
      (make-atomic-formula (apply unfold-total-variables kernel vars))))
   ((cterm-form? expr)
    (apply
     make-cterm
     (append (map (lambda (var)
		    (apply unfold-total-variables var vars))
		  (cterm-to-vars expr))
	     (list (apply unfold-total-variables
			  (cterm-to-formula expr) vars)))))
   (else (myerror "unfold-total-variables"
		  "variable, term, formula or cterm expected"
		  expr))))

(define (fold-total-variables expr . vars)
  (cond
   ((var-form? expr)
    (if (member expr vars)
	(make-var (var-to-type expr)
		  (var-to-index expr)
		  t-deg-one
		  (var-to-name expr))
	expr))
   ((term-in-var-form? expr)
    (let ((var (term-in-var-form-to-var expr)))
      (make-term-in-var-form (apply fold-total-variables var vars))))
   ((term-in-const-form? expr) expr)
   ((term-in-abst-form? expr)
    (let ((var (term-in-abst-form-to-var expr))
	  (kernel (term-in-abst-form-to-kernel expr)))
      (make-term-in-abst-form (apply fold-total-variables var vars)
			      (apply fold-total-variables kernel vars))))
   ((term-in-app-form? expr)
    (let ((op (term-in-app-form-to-op expr))
	  (arg (term-in-app-form-to-arg expr)))
      (make-term-in-app-form (apply fold-total-variables op vars)
			     (apply fold-total-variables arg vars))))
   ((term-in-pair-form? expr)
    (let ((left (term-in-pair-form-to-left expr))
	  (right (term-in-pair-form-to-right expr)))
      (make-term-in-pair-form (apply fold-total-variables left vars)
			      (apply fold-total-variables right vars))))
   ((term-in-lcomp-form? expr)
    (let ((kernel (term-in-lcomp-form-to-kernel expr)))
      (make-term-in-lcomp-form (apply fold-total-variables kernel vars))))
   ((term-in-rcomp-form? expr)
    (let ((kernel (term-in-rcomp-form-to-kernel expr)))
      (make-term-in-rcomp-form (apply fold-total-variables kernel vars))))
   ((term-in-if-form? expr)
    (let ((test (term-in-if-form-to-test expr))
	  (alts (term-in-if-form-to-alts expr))
	  (rest (term-in-if-form-to-rest expr)))
      (apply make-term-in-if-form
	     (apply fold-total-variables test vars)
	     (map (lambda (x)
		    (apply fold-total-variables x vars))
		  (append alts rest)))))
   ((bicon-form? expr) ;to be done before inductively defined predicates
    (let ((bicon (bicon-form-to-bicon expr))
	  (left (bicon-form-to-left expr))
	  (right (bicon-form-to-right expr)))
      (make-bicon bicon
		  (apply fold-total-variables left vars)
		  (apply fold-total-variables right vars))))
   ((quant-form? expr) ;to be done before inductively defined predicates
    (let* ((quant (quant-form-to-quant expr))
	   (var (car (quant-form-to-vars expr)))
	   (kernel (quant-form-to-kernel expr))
	   (total-var (if (t-deg-zero? (var-to-t-deg var))
			  (make-var (var-to-type var)
				    (var-to-index var)
				    t-deg-one
				    (var-to-name var))
			  (myerror "fold-total-variables"
				   "quantifier over a partial variable expected"
				   expr)))
	   (totality-fla
	    (term-to-totality-formula (make-term-in-var-form var))))
      (cond
       ((allnc-form? expr)
	(cond
	 ((and (imp-form? kernel)
	       (formula=? (imp-form-to-premise kernel) totality-fla))
	  (make-all total-var
		    (apply fold-total-variables
			   (imp-form-to-conclusion kernel)
			   (cons var vars))))
	 ((and (impnc-form? kernel)
	       (formula=? (impnc-form-to-premise kernel) totality-fla))
	  (make-allnc total-var
		      (apply fold-total-variables
			     (imp-form-to-conclusion kernel)
			     (cons var vars))))
	 (else (make-allnc var (apply fold-total-variables kernel vars)))))
       ((and (all-form? expr) (formula-of-nulltype? kernel))
	(make-all var (apply fold-total-variables kernel vars)))
       ((exr-form? expr)
	(cond
	 ((and (andd-form? kernel)
	       (formula=? (andd-form-to-left kernel) totality-fla))
	  (make-exd
	   total-var (apply fold-total-variables
			    (andd-form-to-right kernel)
			    (cons var vars))))
					;commented out (andl still missing)
	 ((and (andr-form? kernel)
	       (formula=? (andr-form-to-left kernel) totality-fla))
	  (make-exr
	   total-var (apply fold-total-variables
			    (andr-form-to-right kernel)
			    (cons var vars))))
	 ((and (andnc-form? kernel)
	       (formula=? (andnc-form-to-left kernel) totality-fla))
	  (make-exnc
	   total-var (apply fold-total-variables
			    (andnc-form-to-right kernel)
			    (cons var vars))))
	 ((and (and-form? kernel)
	       (formula=? (and-form-to-left kernel) totality-fla))
	  (make-ex
	   total-var (apply fold-total-variables
			    (and-form-to-right kernel)
			    (cons var vars))))
	 (else (myerror "fold-total-variables"
			"appropriate and form with totality premise expected"
			kernel))))
       (else (myerror "fold-total-variables" "allnc or exr form expected"
		      expr)))))
   ((predicate-form? expr) ;not an inductively defined bicon or quant
    (let ((pred (predicate-form-to-predicate expr))
	  (args (predicate-form-to-args expr)))
      (cond
       ((or (pvar-form? pred) (predconst-form? pred))
	(apply make-predicate-formula
	       pred (map (lambda (arg)
			   (apply fold-total-variables arg vars))
			 args)))
       ((idpredconst-form? pred)
	(let* ((name (idpredconst-to-name pred))
	       (types (idpredconst-to-types pred))
	       (cterms (idpredconst-to-cterms pred))
	       (idpc (make-idpredconst
		      name types
		      (map (lambda (cterm)
			     (apply fold-total-variables cterm vars))
			   cterms))))
	  (apply make-predicate-formula
		 idpc (map (lambda (arg)
			     (apply fold-total-variables arg vars))
			   args))))
       (else (myerror "fold-total-variables" "predicate expected" pred)))))
   ((atom-form? expr)
    (let ((kernel (atom-form-to-kernel expr)))
      (make-atomic-formula (apply fold-total-variables kernel vars))))
   ((cterm-form? expr)
    (apply
     make-cterm
     (append (map (lambda (var)
		    (apply fold-total-variables var vars))
		  (cterm-to-vars expr))
	     (list (apply fold-total-variables (cterm-to-formula expr) vars)))))
   (else (myerror "fold-total-variables"
		  "variable, term, formula or cterm expected"
		  expr))))

;; fold-to-unfold expects a proof M of a total formula A.  It returns a
;; proof (containing M) of the unfolded formula A'.

(define (fold-to-unfold proof . vars)
  (let ((fla (proof-to-formula proof)))
    (cond
     ((imp-form? fla)
      (let* ((prem (imp-form-to-premise fla))
	     (concl (imp-form-to-conclusion fla))
	     (unfolded-prem (apply unfold-total-variables prem vars))
	     (u (formula-to-new-avar unfolded-prem)))
	(make-proof-in-imp-intro-form
	 u (apply fold-to-unfold
		  (make-proof-in-imp-elim-form
		   proof (apply unfold-to-fold
				(make-proof-in-avar-form u)
				vars))
		  vars))))
     ((bicon-form? fla) ;not imp
      (myerror "fold-to-unfold" "not implemented for proofs of" fla))
     ((all-form? fla)
      (let* ((var (all-form-to-var fla))
	     (kernel (all-form-to-kernel fla))
	     (type (var-to-type var))
	     (partial-var (if (t-deg-one? (var-to-t-deg var))
			      (make-var type
					(var-to-index var)
					t-deg-zero
					(var-to-name var))
			      (myerror
			       "fold-to-unfold"
			       "quantifier over a total variable expected"
			       fla)))
	     (totality-avar
	      (formula-to-new-avar
	       (term-to-totality-formula (make-term-in-var-form partial-var))))
	     (alltotal-elim-formula (aconst-to-formula alltotal-elim-aconst))
	     (tvar (car (formula-to-tvars alltotal-elim-formula)))
	     (pvar (car (formula-to-pvars alltotal-elim-formula)))
	     (subst-kernel
	      (formula-subst kernel var (make-term-in-var-form partial-var)))
	     (tpsubst (make-substitution
		       (list tvar pvar)
		       (list type (make-cterm partial-var subst-kernel))))
	     (subst-aconst (aconst-substitute alltotal-elim-aconst tpsubst))
	     (inst-formula (aconst-to-inst-formula subst-aconst))
	     (free (formula-to-free inst-formula)))
	(make-proof-in-allnc-intro-form
	 partial-var
	 (make-proof-in-imp-intro-form
	  totality-avar
	  (apply
	   fold-to-unfold
	   (apply mk-proof-in-elim-form
		  (make-proof-in-aconst-form subst-aconst)
		  (append (map make-term-in-var-form free)
			  (list proof
				(make-term-in-var-form partial-var)
				(make-proof-in-avar-form totality-avar))))
	   (cons var vars))))))
     ((quant-form? fla) ;not all
      (myerror "fold-to-unfold" "not implemented for proofs of" fla))
     ((predicate-form? fla) ;not an inductively defined bicon or quant
      (let ((pred (predicate-form-to-predicate fla))
	    (args (predicate-form-to-args fla)))
	(cond
	 ((or (pvar-form? pred) (predconst-form? pred))
	  proof)
	 ((idpredconst-form? pred)
	  (if (null? (idpredconst-to-cterms pred))
	      proof
	      (myerror "fold-to-unfold" "not implemented for proofs of" fla)))
	 (else (myerror "fold-to-unfold" "predicate expected" pred)))))
     ((atom-form? fla) proof)
     (else (myerror "fold-to-unfold" "not implemented for proofs of" fla)))))

;; unfold-to-fold expects a proof M of the result A' of unfolding a
;; total formula A.  It returns a proof (containing M) of the folded
;; formula A.

(define (unfold-to-fold proof . vars)
  (let ((fla (proof-to-formula proof)))
    (cond
     ((imp-form? fla)
      (let* ((prem (imp-form-to-premise fla))
	     (concl (imp-form-to-conclusion fla))
	     (folded-prem (apply fold-total-variables prem vars))
	     (u (formula-to-new-avar folded-prem)))
	(make-proof-in-imp-intro-form
	 u (apply unfold-to-fold
		  (make-proof-in-imp-elim-form
		   proof (fold-to-unfold
			  (make-proof-in-avar-form u)))
		  vars))))
     ((impnc-form? fla)
      (let* ((prem (impnc-form-to-premise fla))
	     (concl (impnc-form-to-conclusion fla))
	     (folded-prem (apply fold-total-variables prem vars))
	     (u (formula-to-new-avar unfolded-prem)))
	(make-proof-in-impnc-intro-form
	 u (apply unfold-to-fold
		  (make-proof-in-impnc-elim-form
		   proof (fold-to-unfold
			  (make-proof-in-avar-form u)))
		  vars))))
     ((bicon-form? fla) ;not imp, impnc
      (myerror "unfold-to-fold" "not implemented for proofs of" fla))
     ((allnc-form? fla)
      (let* ((var (allnc-form-to-var fla))
	     (kernel (allnc-form-to-kernel fla))
	     (type (var-to-type var))
	     (total-var (if (t-deg-zero? (var-to-t-deg var))
			    (make-var type
				      (var-to-index var)
				      t-deg-one
				      (var-to-name var))
			    (myerror
			     "unfold-to-fold"
			     "quantifier over a partial variable expected"
			     fla)))
	     (alltotal-intro-formula (aconst-to-formula alltotal-intro-aconst))
	     (tvar (car (formula-to-tvars alltotal-intro-formula)))
	     (pvar (car (formula-to-pvars alltotal-intro-formula))))
	(cond
	 ((and
	   (imp-form? kernel)
	   (formula=? (imp-form-to-premise kernel)
		      (term-to-totality-formula (make-term-in-var-form var))))
	  (let* ((concl (imp-form-to-conclusion kernel))
		 (tpsubst (make-substitution
			   (list tvar pvar)
			   (list type (make-cterm var concl))))
		 (subst-aconst
		  (aconst-substitute alltotal-intro-aconst tpsubst))
		 (inst-formula (aconst-to-inst-formula subst-aconst))
		 (free (formula-to-free inst-formula)))
	    (make-proof-in-all-intro-form
	     total-var (apply unfold-to-fold
			      (apply mk-proof-in-elim-form
				     (make-proof-in-aconst-form subst-aconst)
				     (append (map make-term-in-var-form free)
					     (list proof (make-term-in-var-form
							  total-var))))
			      (cons var vars)))))
	 ((and
	   (impnc-form? kernel)
	   (formula=? (impnc-form-to-premise kernel)
		      (term-to-totality-formula (make-term-in-var-form var))))
	  (let* ((concl (impnc-form-to-conclusion kernel))
		 (tpsubst (make-substitution
			   (list tvar pvar)
			   (list type (make-cterm var concl))))
		 (subst-aconst
		  (aconst-substitute alltotal-intro-aconst tpsubst))
		 (inst-formula (aconst-to-inst-formula subst-aconst))
		 (free (formula-to-free inst-formula)))
	    (make-proof-in-allnc-intro-form
	     total-var (apply unfold-to-fold
			      (apply mk-proof-in-elim-form
				     (make-proof-in-aconst-form subst-aconst)
				     (append (map make-term-in-var-form free)
					     (list proof (make-term-in-var-form
							  total-var))))
			      (cons var vars)))))
	 (else
	  (myerror "unfold-to-fold" "not implemented for proofs of" fla)))))
     ((quant-form? fla) ;not allnc
      (myerror "unfold-to-fold" "not implemented for proofs of" fla))
     ((predicate-form? fla) ;not an inductively defined bicon or quant
      (let ((pred (predicate-form-to-predicate fla)))
	(cond
	 ((or (pvar-form? pred) (predconst-form? pred))
	  proof)
	 ((idpredconst-form? pred)
	  (if (null? (idpredconst-to-cterms pred))
	      proof
	      (myerror "unfold-to-fold" "not implemented for proofs of" fla)))
	 (else (myerror "unfold-to-fold" "predicate expected" pred)))))
     ((atom-form? fla) proof)
     (else (myerror "unfold-to-fold" "not implemented for proofs of" fla)))))

;; fold-imp-unfold-proof expects a folded formula A and returns a proof
;; of A -> A'.

(define (fold-imp-unfold-proof fla)
  (let* ((avar (formula-to-new-avar fla))
	 (proof (fold-to-unfold (make-proof-in-avar-form avar))))
    (make-proof-in-imp-intro-form avar proof)))

;; For a pconst of t-deg-one we construct a totality proof using
;; alltotal-intro-aconst

(define (pconst-to-totality-proof pconst)
  (let* ((unfolded-tty-fla
	  (term-to-totality-formula (make-term-in-const-form pconst)))
	 (folded-tty-fla
	  (if (or (andl-form? unfolded-tty-fla) (andnc-form? unfolded-tty-fla))
	      (fold-total-variables (bicon-form-to-left unfolded-tty-fla))
	      (fold-total-variables unfolded-tty-fla)))
	 (concl (imp-form-to-final-conclusion
		 (all-form-to-final-kernel folded-tty-fla)))
	 (applied-pconst-term (car (predicate-form-to-args concl)))
	 (val-type (arrow-form-to-final-val-type (const-to-type pconst)))
	 (alltotal-intro-formula (aconst-to-formula alltotal-intro-aconst))
	 (tvar (car (formula-to-tvars alltotal-intro-formula)))
	 (pvar (car (formula-to-pvars alltotal-intro-formula)))
	 (var (type-to-new-partial-var val-type))
	 (totality-formula (term-to-totality-formula
			    (make-term-in-var-form var)))
	 (tpsubst (make-substitution
		   (list tvar pvar)
		   (list val-type (make-cterm var totality-formula))))
	 (subst-aconst (aconst-substitute alltotal-intro-aconst tpsubst))
	 (aconst-proof (make-proof-in-aconst-form subst-aconst))
	 (avar (make-avar totality-formula -1 "u"))
	 (intro-proof (make-proof-in-allnc-intro-form
		       var (make-proof-in-imp-intro-form
			    avar (make-proof-in-avar-form avar))))
	 (total-var-proof ;similar to boole-total-var-proof in ets.scm
	  (mk-proof-in-elim-form aconst-proof intro-proof))
	 (inst-total-var-proof ;here we need that pconst has t-deg-one
	  (make-proof-in-all-elim-form
	   total-var-proof applied-pconst-term))
	 (imp-proof (fold-imp-unfold-proof folded-tty-fla)))
    (make-proof-in-imp-elim-form
     imp-proof
     (apply mk-proof-in-intro-form
	    (append (all-form-to-vars folded-tty-fla)
		    (list inst-total-var-proof))))))

(define (totality-thm-to-extnc-thm name)
  (define (eqp-avar-to-intro-triple eqp-avar)
    (let* ((fla (avar-to-formula eqp-avar))
	   (args (predicate-form-to-args fla))
	   (vars (map term-in-var-form-to-var args)))
      (append vars (list eqp-avar))))
  (let* ((info (assoc name THEOREMS))
	 (aconst (if info (cadr info)
		     (myerror "totality-thm-to-extnc-proof"
			      "theorem name expected" name)))
	 (fla (aconst-to-formula aconst))
	 (vars1 (imp-impnc-all-allnc-form-to-vars fla)) ;(n^ n^0)
	 (vars2 (map var-to-new-var vars1))
	 (varterms1 (map make-term-in-var-form vars1))
	 (varterms2 (map make-term-in-var-form vars2))
	 (eqp-flas (map make-eqpnc varterms1 varterms2))
	 (unfolded-eqp-flas (map unfold-formula eqp-flas))
	 (eqp-avars (map formula-to-new-avar unfolded-eqp-flas))
	 (eqd-proofs ;of n^ eqd n^0 from n^ eqp n^0 with EqPAlgNcToEqD
	  (map (lambda (varterm1 varterm2 eqp-avar)
		 (let* ((type (term-to-type varterm1))
			(alg-name
			 (if (alg-form? type)
			     (alg-form-to-name type)
			     (myerror "totality-thm-to-extnc-proof"
				      "algebra form expected" type)))
			(eqpnctoeqd-name
			 (string-append
			  "EqP" (string-capitalize-first
				 (rename-parentheses-and-spaces alg-name))
			  "NcToEqD"))
			(info1 (assoc eqpnctoeqd-name THEOREMS))
			(aconst1 (if info1 (cadr info1)
				     (myerror "totality-thm-to-extnc-proof"
					      "theorem name expected"
					      eqpnctoeqd-name))))
		   (mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst1)
		    varterm1 varterm2
		    (make-proof-in-avar-form eqp-avar))))
	       varterms1 varterms2 eqp-avars))
	 (tty-proofs ;of T n^ from n^ eqp n^0 with EqPAlgNcToTotalNcLeft
	  (map (lambda (varterm1 varterm2 eqp-avar)
		 (let* ((type (term-to-type varterm1))
			(alg-name (alg-form-to-name type))
			(eqpnctototalleft-name
			 (string-append
			  "EqP" (string-capitalize-first
				 (rename-parentheses-and-spaces alg-name))
			  "NcToTotalNcLeft"))
			(info2 (assoc eqpnctototalleft-name THEOREMS))
			(aconst2 (if info2 (cadr info2)
				     (myerror "totality-thm-to-extnc-proof"
					      "theorem name expected"
					      eqpnctototalleft-name))))
		   (mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst2)
		    varterm1 varterm2
		    (make-proof-in-avar-form eqp-avar))))
	       varterms1 varterms2 eqp-avars))
	 (tty-proof ;of TotalNat(n^ +n^0) from tty-proofs with aconst
	  (apply mk-proof-in-elim-form
		 (make-proof-in-aconst-form aconst)
		 (zip varterms1 tty-proofs)))
	 (final-concl (imp-impnc-all-allnc-form-to-final-conclusion fla))
	 (arg (car (predicate-form-to-args final-concl)))
	 (eqp-proof ;of n^ +n^0 eqp n^ +n^0 from T n^ with EqPAlgNcRefl
	  (let* ((val-type (term-to-type arg))
		 (val-alg-name
		  (if (alg-form? val-type)
		      (alg-form-to-name val-type)
		      (myerror "totality-thm-to-extnc-proof"
			       "algebra form expected" val-type)))
		 (eqpncrefl-name
		  (string-append
		   "EqP" (string-capitalize-first
			  (rename-parentheses-and-spaces val-alg-name))
		   "NcRefl"))
		 (info3 (assoc eqpncrefl-name THEOREMS))
		 (aconst3 (if info3 (cadr info3)
			      (myerror "totality-thm-to-extnc-proof"
				       "theorem name expected"
				       eqpncrefl-name))))
	    (mk-proof-in-elim-form
	     (make-proof-in-aconst-form aconst3) ;allnc m^(Tm^ -> m^ eqp m^)
	     arg ;n^ +n^0
	     tty-proof)))
	 (subst (make-substitution vars1 varterms2))
	 (subst-arg (term-substitute arg subst))
	 (eqp-fla (terms-to-pure-eqpnc-formula arg subst-arg))
	 (cterm (apply make-cterm (append vars2 (list eqp-fla))))
	 (arity (apply make-arity (map var-to-type vars1)))
	 (pvar (arity-to-new-harrop-pvar arity))
	 (psubst (make-subst pvar cterm))
	 (pred-avar (formula-to-new-avar
		     (apply make-predicate-formula pvar varterms1)))
	 (compat-proof
	  (eqd-proofs-and-predicate-proof-to-proof
	   eqd-proofs (make-proof-in-avar-form pred-avar)))
	 (asubst (make-subst (rac (proof-to-free-avars compat-proof)) eqp-proof))
	 (pasubst (append psubst asubst))
	 (subst-compat-proof (proof-substitute compat-proof pasubst))
	 (eqp-avars (reverse (rdc (proof-to-free-avars compat-proof))))
	 (intro-args (apply append (map eqp-avar-to-intro-triple eqp-avars)))
	 (closed-proof (apply mk-proof-in-nc-intro-form-without-impnc
			      (append intro-args (list subst-compat-proof))))
	 (extnc-name (string-replace-substring name "Total" "ExtNc"))
	 (info4 (assoc extnc-name THEOREMS)))
    (save extnc-name closed-proof)))

;; (proof-and-formula-to-proof proof formula) replaces the end formula
;; of proof by formula.  It should only be applied when both are equal
;; in the sense of having a common reduct.  However, a test via
;; (classical-formula=? (proof-to-formula proof) formula) involves
;; normalization and can lead to non-termination, e.g. for Fix

(define (proof-and-formula-to-proof proof formula)
  ;; (if (not (classical-formula=? (proof-to-formula proof) formula))
  ;;     (myerror "proof-and-formula-to-proof" "equal formulas expected"
  ;; 	       (proof-to-formula proof) formula))
  (cons (tag proof) (cons formula (cddr proof))))

(define (pconst-name-and-number-to-comprule-proof name n)
  (let* ((comprules (pconst-name-to-comprules name)) ;involves check
	 (rule (if (< n (length comprules))
		   (list-ref comprules n)
		   (myerror "pconst-name-and-number-to-comprule-proof"
			    "out of range" n)))
	 (lhs (rule-to-lhs rule))
	 (rhs (rule-to-rhs rule))
	 (lhs-with-partial-vars (term-to-term-with-partial-vars lhs))
	 (rhs-with-partial-vars (term-to-term-with-partial-vars rhs))
	 (partial-vars (term-to-free lhs-with-partial-vars))
	 (type (term-to-type lhs))
	 (idpc (make-idpredconst "EqD" (list type) '()))
	 (initeqd-aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	 (eqd-fla (make-eqd lhs-with-partial-vars rhs-with-partial-vars)))
    (apply mk-proof-in-intro-form
	   (append
	    partial-vars
	    (list (proof-and-formula-to-proof
		   (mk-proof-in-elim-form
		    (make-proof-in-aconst-form initeqd-aconst)
		    lhs-with-partial-vars)
		   eqd-fla))))))

(define (pconst-name-and-number-to-rewrule-proof name n)
  (let* ((rewrules (pconst-name-to-rewrules name)) ;involves check
	 (rule (if (< n (length rewrules))
		   (list-ref rewrules n)
		   (myerror "pconst-name-and-number-to-rewrule-proof"
			    "out of range" n)))
	 (lhs (rule-to-lhs rule))
	 (rhs (rule-to-rhs rule))
	 (vars (term-to-free lhs))
	 (type (term-to-type lhs)))
    (if
     (finalg? type)
     (let* ((idpc (make-idpredconst "EqD" (list (make-alg "boole")) '()))
	    (initeqd-aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	    (=-term (make-=-term lhs rhs))
	    (eqd-fla (make-eqd =-term (make-term-in-const-form true-const))))
       (apply mk-proof-in-intro-form
	      (append
	       vars
	       (list (mk-proof-in-elim-form
		      (make-proof-in-aconst-form eqd-true-to-atom-aconst)
		      =-term
		      (proof-and-formula-to-proof
		       (mk-proof-in-elim-form
			(make-proof-in-aconst-form initeqd-aconst)
			=-term)
		       eqd-fla))))))
					;else as in comprule case
     (let* ((idpc (make-idpredconst "EqD" (list type) '()))
	    (initeqd-aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	    (eqd-fla (make-eqd lhs rhs)))
       (apply mk-proof-in-intro-form
	      (append
	       vars
	       (list (proof-and-formula-to-proof
		      (mk-proof-in-elim-form
		       (make-proof-in-aconst-form initeqd-aconst)
		       lhs)
		      eqd-fla))))))))

;; Proofs always have the form (tag formula ...) where ... is a list
;; with further information.  proof-to-proof-with-new-formula just
;; changes the end formula into an equal one (classical-formula=?).

(define (proof-to-proof-with-new-formula proof new-fla)
  (if (classical-formula=? (proof-to-formula proof) new-fla)
      (cons (car proof) (cons new-fla (cddr proof)))
      (myerror "proof-to-proof-with-new-formula" "equal formulas expected"
	       (proof-to-formula proof) new-fla)))

