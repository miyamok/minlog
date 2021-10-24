;; 2021-03-04.  examples/analysis/sdav.scm

(load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")
;; (set! COMMENT-FLAG #t)

(load "~/git/minlog/examples/analysis/digits.scm")
(load "~/git/minlog/examples/analysis/sdcode.scm")
(load "~/git/minlog/examples/analysis/JK.scm")
(load "~/git/minlog/examples/analysis/sdavaux.scm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Haskell translation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; terms-to-haskell-program (written by Fredrik Nordvall-Forsberg)
;; generates a Haskell file (here sdavtest.hs).  To run it, in a
;; terminal type ghci sdavtest.hs.  Then in *Main> one can evaluate
;; the Haskell functions in sdavtest.hs.  To quit type *Main> :q

'(
(animate "RealToCoI")
(animate "RealToCoIAux")
(animate "ApproxSplitZeroMinusPtFive")
(animate "ApproxSplitZeroPtFive")
(animate "ApproxSplit")
(animate "Rht")
(animate "CoIAvToAvc")
(animate "CoIClosure")
(animate "CoIAvcToCoI")
(animate "CoIAvcSatCoICl")
(animate "CoIAvcSatCoIClAuxK")
(animate "CoIAvcSatCoIClAuxJ")
(animate "Lft")
(animate "IntPlusSdToSdtwo")

(terms-to-haskell-program
 "~/temp/sdavtest.hs"
 (list (list CoIAverage-eterm "coiav")
       (list RealToCoI-eterm "realtocoi")
       (list RatToCoI-eterm "rattocoi")
       (list (pt "SdMs") "sdms")
       (list (pt "PtFive") "ptfive")
       (list (pt "MPtFive") "mptfive")
       (list (pt "OneSdR") "onesdr")
       (list (pt "OneSdL") "onesdl")
       (list (pt "SqrtTwoOverTwo") "stot")
       (list (pt "IrrStr") "irrstr")
       (list (pt "AiToReal") "aitoreal")
       (list (pt "TakeStr") "takestr")
       (list (pt "ListSdToRat") "listsdtorat")))

(deanimate "RealToCoI")
(deanimate "RealToCoIAux")
(deanimate "ApproxSplitZeroMinusPtFive")
(deanimate "ApproxSplitZeroPtFive")
(deanimate "ApproxSplit")
(deanimate "Rht")
(deanimate "CoIAvToAvc")
(deanimate "CoIClosure")
(deanimate "CoIAvcToCoI")
(deanimate "CoIAvcSatCoICl")
(deanimate "CoIAvcSatCoIClAuxK")
(deanimate "CoIAvcSatCoIClAuxJ")
(deanimate "Lft")
(deanimate "IntPlusSdToSdtwo")
)

;; ghci sdavtest.hs
;; takestr 10 (coiav (realtocoi stot) ptfive)
;; [SdR,SdM,SdR,SdM,SdL,SdR,SdL,SdM,SdR,SdM]

;; listsdtorat (takestr 10 (coiav (realtocoi stot) ptfive))
;; 309 % 512

;; (exact->inexact 309/512)
;; 0.603515625

;; (/ (+ (* (sqrt 2) 0.5) 0.5) 2)
;; 0.6035533905932737

;; takestr 18 (coiav (realtocoi (aitoreal (irrstr (\ n -> (n + 1)) 0))) (onesdl 1))

;; SdM,SdR,SdM,SdL,SdM,SdM,SdR,SdM,SdM,SdM,SdR,SdM,SdM,SdM,SdM,SdR,SdM,SdM

;; takestr 18 (coiav (realtocoi (aitoreal (irrstr (\ n -> (n + 1)) 0))) mptfive)

;; SdM,SdM,SdM,SdR,SdM,SdM,SdR,SdM,SdM,SdM,SdR,SdM,SdM,SdM,SdM,SdR,SdM,SdM

;; takestr 18 (coiav (realtocoi (aitoreal (irrstr (\ n -> (n + 1)) 0))) (realtocoi (aitoreal (irrstr (\ n -> (n + 1)) 1))))

;; SdR,SdM,SdR,SdM,SdL,SdM,SdR,SdM,SdR,SdM,SdR,SdM,SdM,SdR,SdM,SdR,SdM,SdM
