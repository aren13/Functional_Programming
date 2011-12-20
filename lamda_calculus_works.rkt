#lang plai
;; Arda Eren
;; Lambda Calculus Works. 
;; TODO: Add Readme and make a video tutorial.
;; Most important parts are f and g. 
;; Part f ->writing a func. that carries out leftmost  β-transformation.
;; Part g -> writing function that repetadly applies until it reachs normal form.

;; Part (a) Grammer definition of λ-calculus
#|
Lamda rules
λ -> i
λ -> (λ λ)
λ -> (λ i λ)
|#

(define-type L
  [id (i symbol?)]
  [app (fun-expr L?) (arg-expr L?)]
  [def (param symbol?) (body L?)])

;;parse: s-expr --> L-expr
; s-expr : Scheme expression  
; L-expr : our L language expression
; It's our parser and it consumes s-expr then returns L-expr

(define (parse sexp)
  (cond 
    ((symbol? sexp) (id sexp))
    ((and (list? sexp) (= (length sexp) 2))
     (app (parse (first sexp)) (parse (second sexp))))
    ((and (list sexp) (= (length sexp) 3) (symbol=? (first sexp) 'λ) (not (list? (second sexp))))
     (def (second sexp) (parse (third sexp))))
    (else (error 'parse "invalid expression"))
    )) 

;; Add test and edit code for invalid expressions 
"parser Tests"
;λ-> i
(test (parse 'a) (id 'a))
; λ-> (λ λ)
(test (parse '(j p)) (app (id 'j) (id 'p)))
; λ -> λ i λ
(test (parse '(λ i (i p))) (def 'i (app (id 'i) (id 'p))))
(test (parse '(λ i (λ j (i j)))) (def 'i (def 'j (app (id 'i) (id 'j)))))
;; error Tests
(test/exn (parse '(5)) "parse: invalid expression") ;; user try to give an scheme number 
(test/exn (parse '(λ (i y) (j p))) "parse: invalid expression") ;; user try to give two argument to  case that (λ i λ)


;; unparse : L-expr -> s-expr
;; Let's reverse our parse operation , it's not needed for project but in future, it's very helpful when trying understand the lamda functions outputs (especially if it's not returns the expected value.)

(define (unparse lexpr)
  (type-case L lexpr
    [id (i) i]
    [app (l r) (list (unparse l) (unparse r))]
    [def (p b) (list 'λ p (unparse b))]))


;;; ------------------------------------ 
;;; begining set operations & free/bound identifiers which is helper function for setting free-identifiers and bound-identifiers 
;; remove-same ; los -> los 
;; it's a helper function for set-union function , it takes a list-of-symbol and then filter according to is there any same one or not. 

(define (remove-same ls)
  (cond
    ((empty? ls) empty)
    (else
     (cons (first ls) 
           (remove-same (filter (lambda (x) (not (symbol=? (first ls) x))) (rest ls)))))))


"remove-same Test"

(test (remove-same '(a b a c a k b)) '(a b c k))

;;set-union : list-of-symbol  los -> list-of-symbol
;; It's simply apply the math set rules append two sets (they are here list data type) then remove the same elements of sets. 

(define (set-union los1 los2)
  (remove-same (append los1 los2)))

;;free-identifier : L-expr --> list-of-symbol
;; it consumes L-expr and then returns list-of-symbol which are free identifier in given expression using lambda rules . 

(define (free-id lexp)
  (type-case L lexp
    [id (i) (list i)]
    [app (fun-expr arg-expr) (set-union (free-id fun-expr) (free-id arg-expr))]
    [def (param body) (filter (lambda (sym) (not (symbol=? sym param))) (free-id body))]))

"free-identifier Tests"
;; case 1
(test (free-id (id 'a)) '( a ))
;;case 2 
(test (free-id (app (id 'j) (id 'p))) '(j p ))
(test (free-id (app (def 'i (app (id 'i) (id 'k))) (def 'j (app (id 'k) (id 'o))))) '(k o))
;; case 3
(test (free-id (def 'i (id 'k))) '(k))

;;bound-id: L-expr --> list-of-symbol
;; it consumes L-expr and then returns list-of-symbol which are free identifier in given expression with using lambda rules . 

(define (bound-id lexp)
  (type-case L lexp
    [id (i) empty]
    [app (fun-expr arg-expr) (set-union (bound-id fun-expr) (bound-id arg-expr))]
    [def (param body) (set-union (list param) (bound-id body))]))


"Bound-id tests"
;;case 1
(test (bound-id (id 'i)) '())
;;case 2 
(test (bound-id (app (id 'j) (id 'p))) '())
(test (bound-id (app (def 'i (app (id 'i) (id 'k))) (def 'j (app (id 'k) (id 'o))))) '(i  j ))
;; case 3
(test (bound-id (def 'i (id 'k)))  '(i))


;; ---------------------------------------------; 


;; subst : L-expr symb L-expr -> L-expr
;; It 's implements the rules for substituion in λ-calculus.  (PART D of assignment)


(define (subst M i N)
  (type-case L M
    [id (j) (if (symbol=? j i) N M)]
    [app (P Q) (app (subst P i N) (subst Q i N))]
    [def (j P) (if (symbol=? i j)
                   M
                   (if (and (member i (free-id P)) (member j (free-id N)))
                       (local ((define new-sym (gensym)))
                         (def new-sym (subst (subst P j (id new-sym)) i N)))
                       (def j (subst P i N))))]))

"subst Tests"
; id
(test (subst (parse 'j) 'j (parse 'i)) (id 'i))
(test (subst (parse 'j) 'i (parse 'i)) (id 'j))
; app
(test (subst (app (id 'j) (id 'p)) 'j (id 'o)) (app (id 'o) (id 'p)))
(test (subst (app (id 'j) (id 'p)) 'j (id 'o)) (app (id 'o) (id 'p)))
; def
(test (subst (def 'j (id 'm)) 'j (id 'a)) (def 'j (id 'm)))
(test (subst (def 'i  (app (id 'j) (id 'p))) 'i (def 'k (id 'a))) (def 'i (app (id 'j) (id 'p))))
; !! ; (test (subst (parse '(λ j i)) 'i (parse 'j)) (def 'generatedSymbol (id 'j))) --->  cannot test now beacuse of gensym function produce unique symbol everytime
(test (subst (parse '(λ j i)) 'i (parse '(λ k a))) (parse '(λ j (λ k a)))) ;; -> No id capture here.
(test (subst (parse '(λ j i)) 'j (parse  '(λ i i))) (parse '(λ j i)))


;; B-subst-one-step : L-expr -> L-expr
; Single B-transformation for given L-expr .

(define (B-subst-one-step lexp)
  (type-case L lexp
    [id (i) lexp]
    [app (fun-expr arg-expr)
         (cond
           ((def? fun-expr) (subst (def-body fun-expr) (def-param fun-expr) arg-expr))
           ((id? fun-expr) (app fun-expr (B-subst-one-step arg-expr)))
           (else
            (app (B-subst-one-step fun-expr) arg-expr)))]
    [def (param body) 
      (def param (B-subst-one-step body))]))


"B-subst-one-step Tests"
(test (B-subst-one-step (parse '((λ j j) k))) (parse 'k))
(test (B-subst-one-step (parse '(a b))) (parse '(a b)))
(test (B-subst-one-step (parse '(((λ j j) k) o))) (parse '(k o)))
(test (B-subst-one-step (parse '(((λ j j) (o a)) ((λ h h) u)))) (parse '((o a) ((λ h h) u))))
(test (B-subst-one-step (parse '((λ k u) ((λ x (x x)) (λ x (x x)))))) (parse 'u))
(test (B-subst-one-step (parse '((λ x (x x)) (λ x (x x))))) (parse '((λ x (x x)) (λ x (x x)))))
(test (B-subst-one-step (parse '((λ t ((((λ h h) (λ k k)) ((λ y y) (λ u u))) t)) ((λ i i) (λ p p)))))
      (parse '((λ t (((λ k k) ((λ y y) (λ u u))) t)) ((λ i i) (λ p p)))))
(test (B-subst-one-step (parse '((λ t (((λ h h) j) t)) ((λ i i) o)))) (parse '((λ t (j t)) ((λ i i) o)))) 


;; PART F / G  
;; B-subst : L-expr -> L-expr 
;; it repeadly applies B-subst-one-step B-transformation function until a normal form is reached.

(define (B-subst lexp)
  (type-case L lexp
    [id (i) lexp]
    [app (fun-expr arg-expr)
         (cond 
           ((id? fun-expr) (app fun-expr (B-subst arg-expr)))
           (else
            (B-subst (B-subst-one-step lexp))))]
    [def (param body) 
      (def param (B-subst body))]))

"B-subt Test"
(test (B-subst (parse 'p)) (parse 'p))
(test (B-subst (parse '((λ t (((λ h h) o) t)) p))) (parse '(o p)))
(test (B-subst (parse '(λ i j))) (parse '(λ i j)))
(test (B-subst (parse '(λ i ((λ j j) k)))) (parse '(λ i k)))
(test (B-subst (parse '(a b))) (parse '(a b)))
(test (B-subst (parse '(((λ i i) k) b))) (parse '(k b)))
(test (B-subst (parse '(a ((λ i i) b)))) (parse '(a b)))
(test (B-subst (parse '(((λ j u) (λ i i)) ((λ y t) (λ h r))))) (parse '(u t))) 
(test (B-subst (parse '(((λ j j) (λ i i)) ((λ y y) (λ h r))))) (parse '(λ h r)))
(test (B-subst (parse '((λ k j) ((λ x (x x)) (λ x (x x)))))) (parse 'j))

;; ------ Part H --- 
;; 
(define zero '(λ f (λ x x)))
(define one '(λ f (λ x (f x))))
(define two '(λ f (λ x (f (f x)))))
(define three '(λ f (λ x (f (f (f x))))))
(define four '(λ f (λ x (f (f (f (f x)))))))
(define five '(λ f (λ x (f (f (f (f (f x))))))))
(define six '(λ f (λ x (f (f (f (f (f (f x)))))))))


;; succ ; 

(define SUCC '(λ n (λ f (λ x (f ((n f) x))))))

" succ Tests"
(test (B-subst (parse `(,SUCC ,one))) (parse two))

;; add; 

(define ADD `(λ m (λ n ((m ,SUCC) n))))

"add Test"
(test (B-subst (parse `((,ADD ,one) ,two))) (parse three))

(define TRUE '(λ x (λ y x)))
(define FALSE '(λ x (λ y y)))

(define CONS '(λ x (λ y (λ f ((f x) y)))))
(define FIRST `(λ p (p ,TRUE)))
(define SECOND `(λ p (p ,FALSE)))

(define IF '(λ test (λ truth (λ falsity ((test truth) falsity)))))

(define ZERO? `(λ n ((n (λ x ,FALSE)) ,TRUE)))

(test (B-subst (parse `(,ZERO? ,zero))) (parse TRUE))

(define step `(λ x ((,CONS (,SECOND x)) (,SUCC (,SECOND x)))))

(define PRED `(λ n (,FIRST ((n ,step) ((,CONS ,zero) ,zero)))))

(test (B-subst (parse `(,PRED ,two))) (parse one))
(test (B-subst (parse `(,PRED ,three))) (parse two))
(test (B-subst (parse `(,PRED ,four))) (parse three))
(test (B-subst (parse `(,PRED ,six))) (parse five))

;; mul

(define MUL `(λ m (λ n (λ f (m (n f))))))

(test (B-subst (parse `((,MUL ,two) ,three))) (parse six))

(define Y '(λ f ((λ x (f (x x))) (λ x (f (x x))))))

(define fact `(,Y (λ fact (λ n (((,IF (,ZERO? n)) ,one) ((,MUL n) (fact (,PRED n))))))))

(unparse (B-subst (parse `(,fact ,five)))) ;; Wait for it, İt's fascinating.