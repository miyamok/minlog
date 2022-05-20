;; 2022-04-28.  prop.scm
;; 13. Ein Beweiser fuer Aussagenlogik
;; ===================================

;; @article{Vorobev64,
;; 		author="Vorob'ev, N. N.",
;; 		title="A new algorithm for derivability in a constructive
;; 			propositional calculus ({Russian})",
;; 		year=1964,
;; 		journal="Trudy Mat. Inst. Steklov",
;; 		volume="72",
;; 		pages="195--227",
;; 		note="Translation  {\em American Mathematical Society
;; 			Translations. Series 2}, 94 (1970), 37--71"
;; }

;; @Phdthesis{Hudelmaier89,
;; Author = "Hudelmaier, Joerg",
;; Title = "Bounds for Cut Elimination in Intuitionistic Propositional Logic",
;; School = "Mathematische Fakultaet, Eberhard--Karls--Universitaet Tuebingen",
;; Note = "accepted for publ.in the AML --- 1992",
;; Year = 1989}

;; @Article{Hudelmaier92,
;; Author = "Hudelmaier, Joerg",
;; Title = "Bounds for Cut Elimination in Intuitionistic Propositional Logic",
;; Journal = "AML",
;; Volume = 31,
;; Pages = "331--354",
;; Year = 1992}

;; @Article{Dyckhoff92,
;; Author = "Roy Dyckhoff",
;; Title = "Contraction--free sequent calculi for intuitionistic logic",
;; Journal = "JSL",
;; Volume = 57,
;; Pages = "793--807",
;; Note = "compare Hudelmaier's thesis",
;; Year = 1992}

;; @Misc{Buchholz90b,
;; Author = "Buchholz, W.",
;; Title = "Zu Kapitel 1 der Dissertation Hudelmaier",
;; Year = 1990}

;; @Misc{Buchholz90c,
;; Author = "Buchholz, W.",
;; Title = "Zu Kapitel 2 der Dissertation Hudelmaier",
;; Year = 1990}

;; @Inproceedings{Schwichtenberg91b,
;; Author = "Schwichtenberg, Helmut",
;; Title = "Normalization",
;; Booktitle = "Logic, Algebra, and Computation.
;;  Proceedings of the International Summer School {M}arktoberdorf,{G}ermany,
;;  July 25 --August 6, 1989",
;; Series = "Series F: Computer and Systems Sciences, Vol 79",
;; Editor = "F.L. Bauer",
;; Pages = "201--237",
;; Organization = "NATO Advanced Study Institute",
;; Publisher = "Springer--Verlag",
;; Address = "Berlin",
;; Year = 1991}

;; Eine Formel heisse elementar, wenn sie atomar, mit einem Praedikatensymbol
;; gebildet oder quantifiziert ist.  Entsprechend definieren wir

(define (elem-form? object)
  (or (atom-form? object) (predicate-form? object) (quant-form? object)))

(define (elem-imp-form? object)
  (and (imp-form? object) (elem-form? (imp-form-to-premise object))))

(define (and-imp-form? object)
  (and (imp-form? object) (and-form? (imp-form-to-premise object))))

(define (leftit-imp-form? object)
  (and (imp-form? object) (imp-form? (imp-form-to-premise object))))

(define (formula-to-elem-subformulas formula)
  (case (tag formula)
    ((atom predicate) (list formula))
    ((imp)
     (append (formula-to-elem-subformulas (imp-form-to-premise formula))
	     (formula-to-elem-subformulas (imp-form-to-conclusion formula))))
    ((and)
     (append (formula-to-elem-subformulas (and-form-to-left formula))
	     (formula-to-elem-subformulas (and-form-to-right formula))))
    ((all ex allnc exca excl) (list formula))
    (else (myerror "formula-to-elem-subformulas" "formula expected"
		   formula))))

(map formula-to-string
     (formula-to-elem-subformulas (pf "all boole T -> T & T")))

;; Die Hauptfunktion zum Aufruf des Beweisers fuer die minimale
;; Aussagenlogik ist prop.  Sie bewirkt eine Sortierung der Annahmen in
;; - elementare Annahmen,
;; - Annahmen der Form A&B oder A&B->C,
;; - Annahmen der Form E->A mit E elementar, und
;; - Annahmen der Form (A->B)->C, also linksiterierte Implikationen.
;; Mit den so sortierten Annahmen wird prop0 aufgerufen und damit geprueft,
;; ob die Formel in der minimalen Aussagenlogik herleitbar ist.

;; Wenn nicht, wird zunaechst geprueft, ob bot oder F ausserhalb von
;; Quantoren vorkommen.  Wenn nicht, ist die Formel auch nicht in der
;; intuitionistischen Aussagenlogik herleitbar.  Wenn ja, wird geprueft,
;; ob die Formel in der intuitionistischen Aussagenlogik herleitbar ist,
;; indem fuer jede elementare Teilformel E neue Annahmen u:bot->E und
;; u':F->E hinzugenommen werden.  Im Erfolgsfall werden die benutzten
;; neuen Annahmen ersetzt durch eine Instanz von efq-log:bot->p bzw. von
;; efq:F->p bzw. durch Herleitungen aus efq-thm:all pp^.F->pp^,
;; falls E atomar ist.

;; Falls der Test auf intuitionistische Herleitbarkeit nein ergibt, wird
;; geprueft, ob die Formel in der klassischen Aussagenlogik herleitbar
;; ist, indem fuer jede elementare Teilformel E neue Annahmen
;; u:((E->bot)->bot)->E und u':((E->F )->F)->E hinzugenommen werden.  Im
;; Erfolgsfall werden die benutzten neuen Annahmen ersetzt durch eine
;; Instanz von stab-log:((p->bot)->bot)->p bzw. durch eine Instanz von
;; stab:((p->F)->F)->p bzw. durch Herleitungen aus
;; stab-thm:all pp^.((pp^->F)->F)->pp^, falls E atomar ist.

(define (prop)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (num-goal (car num-goals))
	 (number (num-goal-to-number num-goal))
	 (goal (cadr num-goal))
	 (context (goal-to-context goal))
	 (avars (map normalize-avar (context-to-avars context)))
	 (goal-formula (normalize-formula (goal-to-formula goal)))
	 (prop-m-result (prop-m-intern num-goals proof maxgoal)))
    (if
     prop-m-result
     (begin
       (set! PPROOF-STATE prop-m-result)
       (pproof-state-history-push PPROOF-STATE)
       (display-comment
	"ok, " DEFAULT-GOAL-NAME "_" (number-to-string number)
	" is proved in minimal propositional logic.")
       (if
	COMMENT-FLAG
	(if (null? (pproof-state-to-num-goals))
	    (begin (display "  Proof finished.") (newline))
	    (begin (display "  The active goal now is") (newline)
		   (display-num-goal
		    (car (pproof-state-to-num-goals)))))))
     (let ((elem-subfors
	    (apply union-wrt
		   (cons formula=?
			 (map formula-to-elem-subformulas
			      (cons goal-formula
				    (map avar-to-formula avars)))))))
       (display-comment "Not provable in minimal propositional logic.")
       (if COMMENT-FLAG (newline))
       (if
	(or (member-wrt formula=? falsity-log elem-subfors)
	    (member-wrt formula=? falsity elem-subfors))
	(let ((prop-i-result (prop-i-intern num-goals proof maxgoal)))
	  (if
	   prop-i-result
	   (begin
	     (set! PPROOF-STATE prop-i-result)
	     (pproof-state-history-push PPROOF-STATE)
	     (display-comment
	      "ok, " DEFAULT-GOAL-NAME "_" (number-to-string number)
	      " is proved in intuitionistic propositional logic.")
	     (if
	      COMMENT-FLAG
	      (if (null? (pproof-state-to-num-goals))
		  (begin (display "  Proof finished.") (newline))
		  (begin (newline) (display-comment "The active goal now is")
			 (newline) (display-num-goal
				    (car (pproof-state-to-num-goals)))))))
	   (let ((prop-c-result (prop-c-intern num-goals proof maxgoal)))
	     (display-comment
	      "Not provable in intuitionistic propositional logic.")
	     (if COMMENT-FLAG (newline))
	     (if
	      prop-c-result
	      (begin
		(set! PPROOF-STATE prop-c-result)
		(pproof-state-history-push PPROOF-STATE)
		(display-comment
		 "ok, " DEFAULT-GOAL-NAME "_" (number-to-string number)
		 " is proved in classical propositional logic.")
		(if
		 COMMENT-FLAG
		 (if (null? (pproof-state-to-num-goals))
		     (begin (display "  Proof finished.") (newline))
		     (begin (display "  The active goal now is") (newline)
			    (display-num-goal
			     (car (pproof-state-to-num-goals)))))))
	      (display-comment
	       "Not provable in classical propositional logic")))))
	(let ((prop-c-result (prop-c-intern num-goals proof maxgoal)))
	  (display-comment "No bot or F outside quantifiers, hence also")
	  (if COMMENT-FLAG (newline))
	  (display-comment
	   "not provable in intuitionistic propositional logic.")
	  (if COMMENT-FLAG (newline))
	  (if
	   prop-c-result
	   (begin
	     (set! PPROOF-STATE prop-c-result)
	     (pproof-state-history-push PPROOF-STATE)
	     (display-comment
	      "ok, " DEFAULT-GOAL-NAME "_" (number-to-string number)
	      " is proved in classical propositional logic.")
	     (if
	      COMMENT-FLAG
	      (if (null? (pproof-state-to-num-goals))
		  (begin (display "  Proof finished.") (newline))
		  (begin (display "  The active goal now is") (newline)
			 (display-num-goal
			  (car (pproof-state-to-num-goals)))))))
	   (display-comment
	    "Not provable in classical propositional logic"))))))))

(define (prop-m-intern num-goals proof maxgoal)
  (let* ((num-goal (car num-goals))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (avars (map normalize-avar (context-to-avars context)))
	 (goal-formula (normalize-formula (goal-to-formula goal)))
	 (elems (list-transform-positive avars
		  (lambda (x) (elem-form? (avar-to-formula x)))))
	 (ands-and-and-imps (list-transform-positive avars
			      (lambda (x)
				(let ((formula (avar-to-formula x)))
				  (or (and-form? formula)
				      (and-imp-form? formula))))))
	 (elem-imps (list-transform-positive avars
		      (lambda (x) (elem-imp-form? (avar-to-formula x)))))
	 (leftit-imps (list-transform-positive avars
			(lambda (x) (leftit-imp-form? (avar-to-formula x)))))
	 (avar-lists (list elems ands-and-and-imps elem-imps leftit-imps))
	 (proof1-or-f (prop0 avar-lists goal-formula)))
    (if (not proof1-or-f) #f
	(make-pproof-state (cdr num-goals)
			   (goal-subst proof goal proof1-or-f)
			   maxgoal))))

(define (prop-i-intern num-goals proof maxgoal)
  (let* ((num-goal (car num-goals))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (avars (map normalize-avar (context-to-avars context)))
	 (goal-formula (normalize-formula (goal-to-formula goal)))
	 (elems (list-transform-positive avars
		  (lambda (x) (elem-form? (avar-to-formula x)))))
	 (ands-and-and-imps (list-transform-positive avars
			      (lambda (x)
				(let ((formula (avar-to-formula x)))
				  (or (and-form? formula)
				      (and-imp-form? formula))))))
	 (elem-imps (list-transform-positive avars
		      (lambda (x) (elem-imp-form? (avar-to-formula x)))))
	 (leftit-imps (list-transform-positive avars
			(lambda (x) (leftit-imp-form? (avar-to-formula x)))))
	 (elem-subfors (apply union-wrt
			      (cons formula=?
				    (map formula-to-elem-subformulas
					 (cons goal-formula
					       (map avar-to-formula avars))))))
	 (elem-subfors-without-botFT
	  (remove-wrt formula=? falsity-log
		      (remove-wrt formula=? truth
				  (remove-wrt formula=? falsity
					      elem-subfors))))
	 (efqs (do ((x elem-subfors-without-botFT (cdr x))
                    (res '()
			 (cons (formula-to-new-avar
				(mk-imp falsity-log (car x)))
			       (cons (formula-to-new-avar
				      (mk-imp falsity (car x)))
				     res))))
		   ((null? x) (reverse res))))
	 (avar-lists (list elems ands-and-and-imps elem-imps leftit-imps))
	 (proof1-or-f (prop0 (list elems ands-and-and-imps
				   (union-wrt avar=? efqs elem-imps)
				   leftit-imps)
			     goal-formula)))
    (if (not proof1-or-f) #f
	(let* ((used-efqs
		(intersection-wrt
		 avar=? (proof-to-free-avars proof1-or-f) efqs))
	       (subst-proof1
		(do ((x used-efqs (cdr x))
		     (res
		      proof1-or-f
		      (let* ((formula (avar-to-formula (car x)))
			     (prem (imp-form-to-premise formula))
			     (concl (imp-form-to-conclusion formula)))
			(proof-subst
			 res (car x)
			 (cond
			  ((formula=? falsity-log prem)
			   (proof-of-efq-log-at concl))
			  ((formula=? falsity prem)
			   (proof-of-efq-at concl))
			  (else (myerror "prop-i: F or bot expected"
					 concl)))))))
		    ((null? x) res))))
	  (make-pproof-state (cdr num-goals)
			     (goal-subst proof goal subst-proof1)
			     maxgoal)))))

(define (prop-c-intern num-goals proof maxgoal)
  (let* ((num-goal (car num-goals))
	 (goal (num-goal-to-goal num-goal))
	 (context (goal-to-context goal))
	 (avars (map normalize-avar (context-to-avars context)))
	 (goal-formula (normalize-formula (goal-to-formula goal)))
	 (elems (list-transform-positive avars
		  (lambda (x) (elem-form? (avar-to-formula x)))))
	 (ands-and-and-imps (list-transform-positive avars
			      (lambda (x)
				(let ((formula (avar-to-formula x)))
				  (or (and-form? formula)
				      (and-imp-form? formula))))))
	 (elem-imps (list-transform-positive avars
		      (lambda (x) (elem-imp-form? (avar-to-formula x)))))
	 (leftit-imps (list-transform-positive avars
			(lambda (x) (leftit-imp-form? (avar-to-formula x)))))
	 (elem-subfors (apply union-wrt
			      (cons formula=?
				    (map formula-to-elem-subformulas
					 (cons goal-formula
					       (map avar-to-formula avars))))))
	 (elem-subfors-without-botFT
	  (remove-wrt formula=? falsity-log
		      (remove-wrt formula=? truth
				  (remove-wrt formula=? falsity
					      elem-subfors))))
	 (stabs
	  (do ((x elem-subfors-without-botFT (cdr x))
	       (res
		'()
		(if
		 (or
		  (member-wrt formula=? falsity-log
			      (append (formula-to-elem-subformulas goal-formula)
				      elems))
		  (member-wrt formula=? falsity-log
			      (apply
			       append
			       (map formula-to-elem-subformulas
				    (append ands-and-and-imps elem-imps))))
		  (member-wrt formula=? falsity-log
			      (apply
			       append
			       (map formula-to-elem-subformulas
				    (map avar-to-formula leftit-imps)))))
		 (cons (formula-to-new-avar
			(mk-imp (mk-neg-log (mk-neg-log (car x))) (car x)))
		       res)
		 (cons (formula-to-new-avar
			(mk-imp (mk-neg (mk-neg (car x))) (car x)))
		       res))))
	      ((null? x) (reverse res))))
	 (proof1-or-f (prop0 (list elems ands-and-and-imps elem-imps
				   (union-wrt formula=? stabs leftit-imps))
			     goal-formula)))
    (if (not proof1-or-f) #f
	(let* ((used-stabs
		(intersection-wrt
		 avar=? (proof-to-free-avars proof1-or-f) stabs))
	       (subst-proof1
		(do ((x used-stabs (cdr x))
		     (res
		      proof1-or-f
		      (let* ((stab-for (avar-to-formula (car x)))
			     (f-prime (imp-form-to-conclusion
				       (imp-form-to-premise stab-for)))
			     (concl (imp-form-to-conclusion stab-for)))
			(proof-subst
			 res (car x)
			 (cond
			  ((formula=? falsity-log f-prime)
			   (proof-of-stab-log-at concl))
			  ((formula=? falsity f-prime)
			   (proof-of-stab-at concl))
			  (else (myerror "prop-c: F or bot expected"
					 f-prime)))))))
		    ((null? x) res))))
	  (make-pproof-state (cdr num-goals)
			     (goal-subst proof goal subst-proof1)
			     maxgoal)))))

;; Mit prop0 wird zunaechst die Zielformel auf elementare Form gebracht.

(define (prop0 avar-lists goal-formula)
  (cond ((elem-form? goal-formula) (prop1 avar-lists goal-formula))
        ((imp-form? goal-formula)
         (let* ((avar (formula-to-new-avar (imp-form-to-premise goal-formula)))
		(prev (prop0 (add-to-avar-lists avar avar-lists)
			     (imp-form-to-conclusion goal-formula))))
           (if (not prev)
               #f
	       (make-proof-in-imp-intro-form avar prev))))
	((and-form? goal-formula)
         (let* ((prev1 (prop0 avar-lists (and-form-to-left goal-formula))))
           (if (not prev1)
               #f
               (let* ((prev2
		       (prop0 avar-lists (and-form-to-right goal-formula))))
                 (if (not prev2)
                     #f
		     (make-proof-in-and-intro-form prev1 prev2))))))
	(else (myerror "prop0: elementary or imp- or and-formula expected"
		       goal-formula))))

;; Hierbei haben wir benutzt

(define (add-to-avar-lists avar avar-lists)
  (let ((formula (avar-to-formula avar))
	(elems (car avar-lists))
        (ands-and-and-imps (cadr avar-lists))
        (elem-imps (caddr avar-lists))
        (leftit-imps (cadddr avar-lists)))
    (cond
     ((elem-form? formula)
      (list (cons avar elems) ands-and-and-imps elem-imps leftit-imps))
     ((or (and-form? formula) (and-imp-form? formula))
      (list elems (cons avar ands-and-and-imps) elem-imps leftit-imps))
     ((elem-imp-form? formula)
      (list elems ands-and-and-imps (cons avar elem-imps) leftit-imps))
     ((leftit-imp-form? formula)
      (list elems ands-and-and-imps elem-imps (cons avar leftit-imps)))
     (else (myerror
	    "add-to-avar-lists: elementary or imp- or and-formula expected"
	    formula)))))

;; prop1 sucht nach einer Annahme u:A&B oder u:A&B->C.
;; Im Fall u:A&B wird diese Annahme entfernt und stattdessen werden die
;; neuen Annahmen u1:A und u2:B gemacht.  Damit wird prop1 wieder aufgerufen.
;; Im Fall u:A&B->C  wird diese Annahme entfernt und stattdessen wird die
;; neue Annahme u1:A->B->C gemacht.  Damit wird prop1 wieder aufgerufen.
;; Wenn keine Annahme u:A&B oder u:A&B->C existiert, wird prop2 aufgerufen.

(define (prop1 avar-lists elem-goal-formula)
  (let* ((elems (car avar-lists))
         (ands-and-and-imps (cadr avar-lists))
         (elem-imps (caddr avar-lists))
         (leftit-imps (cadddr avar-lists)))
    (if (null? ands-and-and-imps)
        (prop2 avar-lists elem-goal-formula)
        (let* ((u (car ands-and-and-imps))
	       (for (avar-to-formula u)))
          (cond ((and-form? for)
                 (let* ((left (and-form-to-left for))
                        (right (and-form-to-right for))
                        (u1 (formula-to-new-avar left))
			(u2 (formula-to-new-avar right))
			(new-avar-lists ;without u:A&B, with u1:A, u2:B
                         (add-to-avar-lists
                          u1 (add-to-avar-lists
			      u2 (list elems (cdr ands-and-and-imps)
				       elem-imps leftit-imps))))
                        (prev (prop1 new-avar-lists elem-goal-formula)))
                   (if (not prev)
                       #f
		       (proof-substitute
			prev
			(make-substitution
			 (list u1 u2)
			 (list (make-proof-in-and-elim-left-form
				(make-proof-in-avar-form u))
			       (make-proof-in-and-elim-right-form
				(make-proof-in-avar-form u))))))))
		((and-imp-form? for)
                 (let* ((prem (imp-form-to-premise for))
                        (concl (imp-form-to-conclusion for))
                        (left (and-form-to-left prem))
                        (right (and-form-to-right prem))
                        (u1 (formula-to-new-avar (mk-imp left right concl)))
			(u2 (formula-to-new-avar left))
                        (u3 (formula-to-new-avar right))
                        (new-avar-lists ;without u:A&B->C, with u1:A->B->C
                         (add-to-avar-lists
			  u1 (list elems (cdr ands-and-and-imps)
				   elem-imps leftit-imps)))
                        (prev (prop1 new-avar-lists elem-goal-formula)))
                   (if (not prev)
                       #f
		       (proof-subst
			prev u1
			(mk-proof-in-intro-form
			 u2 u3 (make-proof-in-imp-elim-form
				(make-proof-in-avar-form u)
				(make-proof-in-and-intro-form
				 (make-proof-in-avar-form u2)
				 (make-proof-in-avar-form u3))))))))
		(else (myerror "prop1: and-imp-form or and-form expected"
			       for)))))))

;; prop2 prueft zunaechst, ob die (elementare) Zielformel gleich T ist
;; oder ob sie unter den Annahmen vorkommt.  Wenn ja, wird truth-axiom-symbol
;; bzw. das zugehoerige Annahmensymbol zurueckgegeben.  Wenn nein, wird
;; nach einer Annahme v:E->A gesucht, fuer die auch u:E unter den elementaren
;; Annahmen vorkommt oder gleich T ist.  Wenn eine gefunden ist, wird die
;; Annahme E->A entfernt und stattdessen die Annahme A gemacht, und prop1 auf
;; diese neuen Annahmen und die alte Zielformel angewandt.  Wenn keine solche
;; Annahme vorhanden ist, wird prop3 aufgerufen

(define (prop2 avar-lists elem-goal-formula)
  (if
   (formula=? truth elem-goal-formula)
   (make-proof-in-aconst-form truth-aconst)
   (let* ((elems (car avar-lists))
	  (ands-and-and-imps (cadr avar-lists))
	  (elem-imps (caddr avar-lists))
	  (leftit-imps (cadddr avar-lists))
	  (info1 (list-transform-positive elems
		   (lambda (x) (formula=? elem-goal-formula
					  (avar-to-formula x))))))
     (if
      (pair? info1)
      (make-proof-in-avar-form (car info1))
      (do ((x elem-imps (cdr x))
	   (y '() (cons (car x) y))
	   (test
	    '()
	    (let* ((v (car x))
		   (formula (avar-to-formula v))
		   (prem (imp-form-to-premise formula))
		   (concl (imp-form-to-conclusion formula))
		   (info2 (list-transform-positive elems
			    (lambda (x) (formula=? prem
						   (avar-to-formula x))))))
	      (if (or ;otherwise '();; i.e. continue loop
		   (formula=? truth prem) (pair? info2))
		  (let* ((u1 (formula-to-new-avar concl))
			 (new-elem-imps ;without v:E->A
			  (append (reverse y) (cdr x)))
			 (new-avar-lists (list elems ands-and-and-imps
					       new-elem-imps leftit-imps))
			 (prev (prop1 (add-to-avar-lists u1 new-avar-lists)
				      elem-goal-formula)))
		    (if (not prev)
			#f
			(proof-subst
			 prev u1
			 (make-proof-in-imp-elim-form
			  (make-proof-in-avar-form v)
			  (if (formula=? truth prem)
			      (make-proof-in-aconst-form truth-aconst)
			      (make-proof-in-avar-form (car info2)))))))
		  '()))))
	  ((or (pair? test) (null? x))
	   (if (pair? test) test (prop3 avar-lists elem-goal-formula))))))))

;; prop3 erhaelt Annahmen, die nicht mehr gemaess prop1 oder prop2 reduzierbar
;; sind.  prop3 prueft zunaechst, ob noch eine linksiterierte Implikation
;; als Annahme vorkommt.  Wenn nicht, wird sofort #f zurueckgegeben.
;; Nehmen wir jetzt an, u:(A1->A2)->A3 ist eine solche Annahme.
;; Sei B die (elementare) Zielformel.  Wir entfernen die Annahme
;; u:(A1->A2)->A3 und pruefen zunaechst durch einen Aufruf von prop1,
;; ob B with der zusaetzlichen Annahme u3:A3 herleitbar ist.
;; Wenn nein, gehen wir gleich zur naechsten linksiterierten Implikation ueber.
;; Wenn ja, pruefen wir als naechstes durch einen Aufruf von prop0, ob
;; A1->A2 with der zusaetzlichen Annahme u2:A2->A3 herleitbar ist.
;; Wenn nein, gehen wir wieder zur naechsten linksiterierten Implikation ueber.
;; Wenn ja, erhalten wir wie folgt eine Herleitung von B aus den neuen
;; Annahmen:
;;                                     u3:A2
;;                                    --------   imp-intro u4:A1
;;             u:(A1 -> A2) -> A3     A1 -> A2
;;             -------------------------------
;;                             A3
;;                          --------   imp-intro u3:A2
;;                          A2 -> A3
;;                             |
;;                             | prev2
;;                             |
;;   u:(A1 -> A2) -> A3     A1 -> A2
;;   -------------------------------
;;                   A3
;;                   |
;;                   | prev1
;;                   |
;;                   B

(define (prop3 avar-lists elem-goal-formula)
  (let* ((elems (car avar-lists))
	 (ands-and-and-imps (cadr avar-lists))
	 (elem-imps (caddr avar-lists))
	 (leftit-imps (cadddr avar-lists)))
    (let f ((x leftit-imps) (y '()))
      (if (null? x)
	  #f
	  (let* ((u (car x))
		 (leftit-imp (avar-to-formula u))
		 (prem (imp-form-to-premise leftit-imp))
		 (A1 (imp-form-to-premise prem))
		 (A2 (imp-form-to-conclusion prem))
		 (A3 (imp-form-to-conclusion leftit-imp))
		 (new-leftit-imps ;without u:(A1->A2)->A3
		  (append (reverse y) (cdr x)))
		 (new-avar-lists (list elems ands-and-and-imps
				       elem-imps new-leftit-imps))
		 (u1 (formula-to-new-avar A3))
		 (u2 (formula-to-new-avar (mk-imp A2 A3)))
		 (u3 (formula-to-new-avar A2))
		 (u4 (formula-to-new-avar A1))
		 (prev1 (prop1 (add-to-avar-lists u1 new-avar-lists)
			       elem-goal-formula)))
	    (if prev1 ;otherwise: continue immediately with leftit-imps
		(let ((prev2 (prop0 (add-to-avar-lists u2 new-avar-lists)
				    (mk-imp A1 A2))))
		  (if prev2 ;otherwise: continue immediately with leftit-imps
		      (proof-subst
		       prev1 u1
		       (make-proof-in-imp-elim-form
			(make-proof-in-avar-form u)
			(proof-subst
			 prev2 u2
			 (make-proof-in-imp-intro-form
			  u3 (make-proof-in-imp-elim-form
			      (make-proof-in-avar-form u)
			      (make-proof-in-imp-intro-form
			       u4 (make-proof-in-avar-form u3)))))))
		      (f (cdr x) (cons (car x) y))))
		(f (cdr x) (cons (car x) y))))))))

;; (define (prop3 avar-lists elem-goal-formula)
;;   (call/cc
;;    (lambda (return)
;;      (let* ((elems (car avar-lists))
;;             (ands-and-and-imps (cadr avar-lists))
;;             (elem-imps (caddr avar-lists))
;;             (leftit-imps (cadddr avar-lists)))
;;        (do ((x leftit-imps (cdr x))
;;             (y '() (cons (car x) y)))
;;            ((null? x) (return #f))
;;          (let* ((u (car x))
;; 		(leftit-imp (avar-to-formula u))
;; 		(prem (imp-form-to-premise leftit-imp))
;;                 (A1 (imp-form-to-premise prem))
;;                 (A2 (imp-form-to-conclusion prem))
;;                 (A3 (imp-form-to-conclusion leftit-imp))
;;                 (new-leftit-imps ;without u:(A1->A2)->A3
;;                  (append (reverse y) (cdr x)))
;;                 (new-avar-lists (list elems ands-and-and-imps
;; 				      elem-imps new-leftit-imps))
;;                 (u1 (formula-to-new-avar A3))
;; 		(u2 (formula-to-new-avar (mk-imp A2 A3)))
;; 		(u3 (formula-to-new-avar A2))
;; 		(u4 (formula-to-new-avar A1))
;; 		(prev1 (prop1 (add-to-avar-lists u1 new-avar-lists)
;;                               elem-goal-formula)))
;;            (if prev1 ;otherwise: continue immediately with leftit-imps
;;                (let ((prev2 (prop0 (add-to-avar-lists u2 new-avar-lists)
;; 				   (mk-imp A1 A2))))
;;                  (if prev2 ;otherwise: continue immediately with leftit-imps
;;                      (return
;; 		      (proof-subst
;; 		       prev1 u1
;; 		       (make-proof-in-imp-elim-form
;; 			(make-proof-in-avar-form u)
;; 			(proof-subst
;; 			 prev2 u2
;; 			 (make-proof-in-imp-intro-form
;; 			  u3 (make-proof-in-imp-elim-form
;; 			      (make-proof-in-avar-form u)
;; 			      (make-proof-in-imp-intro-form
;; 			       u4 (make-proof-in-avar-form u3)))))))))))))))))

;; Einige Beispielsformeln stehen in ~/minlog/examples/prop.scm.


