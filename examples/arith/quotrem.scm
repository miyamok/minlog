;; 2022-06-18.  quotrem.scm

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "k" (py "nat"))

;; QR
(set-goal "all m,n exd k exl l(n=(m+1)*k+l andnc l<m+1)")
(assume "m")
(ind)
;; 3,4
;; Base
(intro 0 (pt "0"))
(intro 0 (pt "0"))
(split)
(use "Truth")
(use "Truth")
;; 4
;; Step
(assume "n" "IH")
(by-assume "IH" "k" "kProp")
(by-assume "kProp" "l" "klProp")
(cases (pt "l<m"))
;; 16,17
;; Case l<m
(assume "l<m")
(intro 0 (pt "k"))
(intro 0 (pt "l+1"))
(ng)
(split)
(use "klProp")
(use "l<m")
;; 17
;; Case l<m -> F
(assume "l<m -> F")
(intro 0 (pt "k+1"))
(intro 0 (pt "0"))
(ng)
(split)
(assert "l=m")
 (use "NatLeAntiSym")
 (use "NatLtSuccToLe")
 (use "klProp")
 (use "NatNotLtToLe")
 (use "l<m -> F")
(assume "l=m")
(simphyp-with-to "klProp" "l=m" "klPropSimp")
(use "klPropSimp")
(use "Truth")
;; Proof finished.
;; (cp)
(save "QR")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "QR")))
(add-var-name "nm" (py "nat yprod nat"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [n,n0]
;;  (Rec nat=>nat yprod nat)n0(0 pair 0)
;;  ([n1,nm]
;;    [case nm
;;      (n2 pair n3 -> 
;;      [case (n3<n) (True -> n2 pair Succ n3) (False -> Succ n2 pair 0)])])

(pp (nt (mk-term-in-app-form neterm (pt "2") (pt "7"))))
(pp (nt (mk-term-in-app-form neterm (pt "5") (pt "7"))))
(pp (nt (mk-term-in-app-form neterm (pt "6") (pt "54"))))
(pp (nt (mk-term-in-app-form neterm (pt "6") (pt "754")))) 
;; 107 pair 5

(define expr (term-to-scheme-expr neterm))

;; (lambda (n)
;;   (lambda (n0)
;;     (((natRec n0) (cons 0 0))
;;       (lambda (n1)
;;         (lambda (nm)
;;           (((lambda (n2)
;;               (lambda (n3)
;;                 (if (< n3 n) (cons n2 (+ n3 1)) (cons (+ n2 1) 0))))
;;              (car nm))
;;             (cdr nm)))))))

(((ev expr) 6) 754)
;; (107 . 5)
