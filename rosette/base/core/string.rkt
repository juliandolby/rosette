#lang racket

(require "term.rkt" "union.rkt")
(require "bool.rkt" "polymorphic.rkt" "type.rkt" "real.rkt")

(provide @string-length @string=? T*->string? @string? @string=? @substring @string-contains? @string-prefix? @string-suffix? @str-to-int @int-to-str)

;; ----------------- String type ----------------- ;; 
(define-lifted-type @string? 
  #:base string?
  #:is-a? (instance-of? string? @string?)
  #:methods
  [(define (solvable-default self) "")
   (define (type-applicable? self) #t)
   (define (type-eq? self u v) (@string=? u v)) 
   (define (type-equal? self u v) (@string=? u v))
   (define (type-cast self v [caller 'type-cast])
     (match v
       [(? string?) v]
       [(term _ (== self)) v]
       [(union : [g (and (or (? string?) (term _ (== self))) u)] _ ...)
        (@assert g (thunk (raise-argument-error caller "expected a string?" v)))
        u]
       [_  (@assert #f (thunk (raise-argument-error caller "expected a string?" v)))]))
   (define (type-compress self force? ps)
     (match ps
    [(list _) ps]
    [(list (cons g a) (cons (expression (== !) g) b)) (list (cons #t (ite g a b)))]
    [(list (cons (expression (== !) g) b) (cons g a)) (list (cons #t (ite g a b)))]
    [(list (cons g a) ...)
     (list (cons (apply || g)
                 (apply @string-append (for/list ([guard g][str a]) (ite guard str "")))))]))])


;; ----------------- Lifting utilities ----------------- ;; 

(define (lift-op op)
  (define caller (object-name op))
  (case (procedure-arity op)
    [(1)  (lambda (x) (op (type-cast @string? x caller)))]
    [(2)  (lambda (x y) (op (type-cast @string? x caller) (type-cast @string? y caller)))]
    [else (case-lambda [() (op)]
                       [(x) (op (type-cast @string? x caller))]
                       [(x y) (op (type-cast @string? x caller) (type-cast @string? y caller))]
                       [xs (apply op (for/list ([x xs]) (type-cast @string? x caller)))])]))

; A generic typing procedure for a lifted operator that takes N >= 0 arguments of type T
; and returns a @string?. See term.rkt.
(define (T*->string? . xs) @string?)

(define-syntax-rule (define-lifted-operator @op $op type)
  (define-operator @op
    #:identifier (string->symbol (substring (symbol->string '@op) 1))
    #:range type
    #:unsafe $op
    #:safe (lift-op $op)))

(define-syntax-rule (define-quantifier @op $op)
  (define-operator @op
    #:identifier '$op
    #:range T*->string?
    #:unsafe $op
    #:safe
    (lambda (@vars @body)
      (match* (@vars (type-cast @string? @body '$op))
        [((list (constant _ (? primitive-solvable?)) (... ...)) body)
         ($op @vars body)]
        [(_ _)
         (@assert
          #f
          (thunk
           (raise-argument-error
            '$op
            "expected a list of symbolic constants of primitive solvable types" @vars)))]))))

;; ----------------- Predicates ----------------- ;; 

(define ($string=? x y)
  (match* (x y)
	  [((? string?) (? string?)) (string=? x y)]
	  [(_ _) (expression @string=? x y)]))

(define-lifted-operator @string=?  $string=? T*->boolean?)

(define ($string-contains? x y)
  (match* (x y)
	  [((? string?) (? string?)) (string-contains? x y)]
	  [(_ _) (expression @string-contains? x y)]))

(define-lifted-operator @string-contains?  $string-contains? T*->boolean?)

(define ($string-prefix? x y)
  (match* (x y)
	  [((? string?) (? string?)) (string-prefix? x y)]
	  [(_ _) (expression @string-prefix? x y)]))

(define-lifted-operator @string-prefix?  $string-prefix? T*->boolean?)

(define ($string-suffix? x y)
  (match* (x y)
	  [((? string?) (? string?)) (string-suffix? x y)]
	  [(_ _) (expression @string-suffix? x y)]))

(define-lifted-operator @string-suffix?  $string-suffix? T*->boolean?)

;; ----------------- String Operators ----------------- ;; 

(define ($substring x i j)
  (match* (x i j)
	 [((? string?) (? integer?) (? integer?)) (substring x i j)]
	 [(_ _ _) (expression @substring x i j)]))

(define-operator @substring
   #:identifier 'substring
   #:range T*->string?
   #:unsafe $substring
   #:safe (lambda (s i j) ($substring (type-cast @string? s 'substring) (type-cast @integer? i 'substring) (type-cast @integer? j 'substring))))
   
(define ($string-length x)
  (match x
	 [(? string?) (string-length x)]
	 [_ (expression @string-length x)]))

(define-lifted-operator @string-length $string-length T*->integer?)

(define ($string-append x y)
  (match* (x y)
	  [((? string?) (? string?)) (string-append x y)]
	  [(_ _) (expression @string-append x y)]))

(define-lifted-operator @string-append  $string-append T*->string?)

;; ----------------- String Conversions ----------------- ;;

(define (int-to-str i)
  (if (and i (integer? i) (>= i 0))
      (number->string i)
      ""))

(define ($int-to-str i)
  (match i
     [(? integer? i) (int-to-str i)]
     [_ (expression @int-to-str i)]))

(define-operator @int-to-str
   #:identifier 'int-to-str
   #:range T*->string?
   #:unsafe $int-to-str
   #:safe (lambda (i) ($int-to-str (type-cast @integer? i 'int-to-str))))

(define (str-to-int s)
  (let ((n (string->number s)))
    (if (and n (integer? n) (>= n 0)) n -1)))

(define ($str-to-int x)
  (match x
	 [(? string?) (str-to-int x)]
	 [_ (expression @str-to-int x)]))

(define-lifted-operator @str-to-int $str-to-int T*->integer?)

