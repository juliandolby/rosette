#lang racket

(require "term.rkt" "op.rkt" "union.rkt" "bool.rkt" "any.rkt" "generic.rkt" "merge.rkt"
         (only-in "bitwise.rkt" define-not define-and define-or))

(provide 
 @bitvector?           
 @bveq @bvslt @bvsle    
 @bvsgt @bvsge  
 @bvadd @bvsub @bvmul @bvsdiv @bvsrem                  
 @bvshl @bvashr @bvlshr
 @bvnot @bvand @bvor @bvxor
 @expt @bvsqrt @bvabs @bvsgn 
 current-bitwidth ignore-division-by-0)

(define ignore-division-by-0
  (make-parameter #f))

(define current-bitwidth
  (make-parameter 5 
                  (lambda (bw) 
                    (unless (and (integer? bw) (positive? bw))
                      (raise-argument-error 'current-bitwidth "positive integer" bw))
                    bw)))

(define (num/cast v)
  (match v
    [(? number?) (values #t v)]
    [(term _ (== @bitvector?)) (values #t v)]
    [(union : [g (and (app type-of (== @bitvector?)) u)] _ ...) (values g u)]
    [_ (values #f v)]))

(define simplify-ite
  (case-lambda 
    [(p) (let* ([g (car p)]
                [v (cdr p)]
                [w (simplify-ite g v)])
           (if (equal? v w) p (cons g w)))]
    [(g v) (match* (g v)
             [(a (expression (== ite) a x _)) x]
             [(a (expression (== ite) (expression (== !) a) _ x)) x]
             [((expression (== !) a) (expression (== ite) a _ x)) x]
             ;[(a (expression (== ite) b x y))
             ; (match* ((simplify-ite a x) (simplify-ite a y))
             ;   [((== x) (== y)) v]
             ;   [(m n) (ite b m n)])]
             [(_ _) v])]))

(define (num/compress force? ps) ; force? is ignored since numbers are immutable and therefore always merged
  ;(printf "num/compress ~a ~a\n" (length ps) ps)
  (match ps
    [(list _) ps]
    [(list (cons g a) (cons (expression (== !) g) b)) (list (cons #t (ite g a b)))]
    [(list (cons (expression (== !) g) b) (cons g a)) (list (cons #t (ite g a b)))]
    [(or (list (cons (expression (== &&) g h) x) (cons (expression (== &&) g f) y)) 
         (list (cons (expression (== &&) g h) x) (cons (expression (== &&) f g) y)) 
         (list (cons (expression (== &&) h g) x) (cons (expression (== &&) g f) y)) 
         (list (cons (expression (== &&) h g) x) (cons (expression (== &&) f g) y)))
     (list (cons g (match* (h f)
                     [(_ (expression (== !) h)) (ite h x y)]
                     [((expression (== !) f) _) (ite f y x)]
                     [(_ _) (@bvor (ite h x 0) (ite f y 0))])))]
    [(list (app simplify-ite (cons g x)) (app simplify-ite (cons h y))) 
     (list (cons (|| g h) (if (equal? x y) x (@bvor (ite g x 0) (ite h y 0)))))]
    [(list (app simplify-ite (cons a x)) (app simplify-ite (cons b y)) ...)
     (list (cons (apply || a b)
                 (if (andmap (curry equal? x) y)
                     x
                     (apply @bvor (ite a x 0) (map (curryr ite 0) b y)))))]))

(define (num/eq? x y) (@bveq x y))
  
(define-primitive-type @bitvector? 
  #:pred     (instance-of? number? @bitvector?) 
  #:least-common-supertype (lambda (t) (if (eq? t @bitvector?) @bitvector? @any?))
  #:eq?      num/eq?
  #:equal?   num/eq?
  #:cast     num/cast
  #:compress num/compress)

(define binary-predicate-type (op/-> (@bitvector? @bitvector?) @boolean?))
(define nary-type (op/-> (#:rest @bitvector?) @bitvector?))
(define binary-type (op/-> (@bitvector? @bitvector?) @bitvector?))
(define unary-type (op/-> (@bitvector?) @bitvector?))

(define-syntax-rule (sort/expression op x y) 
  (if (term<? x y) 
      (expression op x y)
      (expression op y x)))

(define-op @bveq  
  #:name '= 
  #:type binary-predicate-type
  #:op   (lambda (x y)
           (match* (x y)
             [((? number?) (? number?)) (= x y)]
             [((? number?) (? term?)) (expression @bveq x y)]
             [((? term?) (? number?)) (expression @bveq y x)]
             [(_ _) (or (equal? x y) (sort/expression @bveq x y))])))
  
(define-op @bvslt  #:name '<  #:type binary-predicate-type #:op (lambda (x y) (cmp @bvslt < x y)))
(define-op @bvsle #:name '<= #:type binary-predicate-type #:op (lambda (x y) (cmp @bvsle <= x y)))
(define-op @bvsgt  #:name '>  #:type binary-predicate-type #:op (lambda (x y) (@bvslt y x)))
(define-op @bvsge #:name '>= #:type binary-predicate-type #:op (lambda (x y) (@bvsle y x)))

(define-syntax-rule (cmp @op num/op x y) 
  (match* (x y)
    [((? number?) (? number?)) (num/op x y)]
    [((? number?) (expression (== ite) b (? number? t) (? number? f))) (merge b (num/op x t) (num/op x f))] 
    [((expression (== ite) b (? number? t) (? number? f)) (? number?)) (merge b (num/op t y) (num/op f y))]
    [(_ _) (let ([z (@bvsub y x)])
             (if (number? z) 
                 (num/op 0 z) 
                 (expression @op x y)))]))

(define (op-match op x)
  (if (expression? x op) (term-child x) (list x)))

(define-op @bvadd 
  #:name '+ 
  #:type nary-type 
  #:op (case-lambda [(a b) (binary:+/* @bvadd @bvadd-info a b)] 
                    [args  (nary:+/*   @bvadd @bvadd-info args)]))
           
(define-op @bvmul 
  #:name '* 
  #:type nary-type 
  #:op (case-lambda [(a b) (binary:+/* @bvmul @bvmul-info a b)] 
                    [args  (nary:+/*   @bvmul @bvmul-info args)]))

(define-op @bvsub 
  #:name '- 
  #:type nary-type 
  #:op (case-lambda [(x) (match x 
                           [(? number?) (- x)]
                           [(expression (== @bvmul) -1 y) y] 
                           [_ (@bvmul -1 x)])] 
                    [(x . y) (apply @bvadd x (map @bvsub y))]))                  

(define (non-zero? x)
  (if (number? x)
      (not (equal? x 0))
      (! (@bveq x 0)))) 

(define-op  @bvsrem 
  #:name '% 
  #:type binary-type
  #:pre  (lambda (x y) (non-zero? y))
  #:op   (match-lambda** [(x 0) (if (ignore-division-by-0) 
                                    (expression @bvsrem x 0)
                                    (error '@bvsrem "% undefined for 0"))]
                         [((? integer? x) (? integer? y)) (remainder x y)]
                         [(x 1) 0]
                         [(x x) 0]
                         [((or (? integer? x) (? term? x)) 
                           (or (? integer? y) (? term? y))) (expression @bvsrem x y)]))

(define-op  @bvsdiv 
  #:name 'div 
  #:type binary-type
  #:pre  (op-pre @bvsrem)
  #:op   (match-lambda** [(x 0) (if (ignore-division-by-0) 
                                    (expression @bvsdiv x 0)
                                    (error '@bvsdiv "/ undefined for 0"))]
                         [((? integer? x) (? integer? y)) (quotient x y)]
                         [(x 1) x]
                         [(x x) 1]  
                         [((or (? integer? x) (? term? x)) 
                           (or (? integer? y) (? term? y))) (expression @bvsdiv x y)]))

(define-op  @expt 
  #:name 'expt 
  #:type binary-type
  #:pre  (lambda (x y) (=> (@bveq x 0) (@bvsge y 0)))
  #:op   (match-lambda** [((? number? x) (? number? y)) (expt x y)]
                         [(_ 0) 1]
                         [(0 _) 0]
                         [(x 1) x]
                         [((expression (== @expt) x y) z) (@expt x (@bvmul y z))]
                         [(x y) (expression @expt x y)]))

(define (mask x)
  (bitwise-and x (bitwise-not (arithmetic-shift -1 (current-bitwidth)))))

(define-op @bvshl
  #:name '<<
  #:type binary-type
  #:op   (match-lambda** [(x 0) x]
                         [(0 _) 0]
                         [((? number? x) (? number? y)) 
                          (if (> y 0) (arithmetic-shift x y) 0)]
                         [(x y) (expression @bvshl x y)]))

(define-op @bvlshr
  #:name '>>>
  #:type binary-type
  #:op   (match-lambda** [(x 0) x]
                         [(0 _) 0]
                         [((? number? x) (? number? y)) 
                          (if (< y 0) 0 (arithmetic-shift (mask x) (- y)))]
                         [(x y) (expression @bvlshr x y)]))


(define-op @bvashr
  #:name '>>
  #:type binary-type
  #:op   (match-lambda** [(x 0) x]
                         [(0 _) 0]
                         [(-1 _) -1]
                         [((? number? x) (? number? y)) 
                          (cond [(> y 0) (arithmetic-shift x (- y))]
                                [(> x 0) 0]
                                [else -1])]
                         [(x y) (expression @bvashr x y)]))

(define-not @bvnot 'bitwise-not @bitvector? number? bitwise-not)
(define-and @bvand 'bitwise-and @bvor @bvnot -1 @bitvector? number? bitwise-and)
(define-or  @bvor 'bitwise-ior @bvand @bvnot 0 @bitvector? number? bitwise-ior)

(define-op @bvxor 
  #:name 'bitwise-xor 
  #:type nary-type 
  #:op   (case-lambda [() 0]
                      [(x) x]
                      [(x y) (match* (x y)
                               [((? number?) (? number?)) (bitwise-xor x y)]
                               [(_ (== x)) 0]
                               [(_ 0) x]
                               [(0 _) y]
                               [(_ -1) (@bvnot x)]
                               [(-1 _) (@bvnot y)]
                               [(_ (expression (== @bvnot) (== x))) -1]
                               [((expression (== @bvnot) (== y)) _) -1]
                               [((? term?) (? number?)) (expression @bvxor y x)]
                               [((? number?) (? term?)) (expression @bvxor x y)]
                               [(_ _) (sort/expression @bvxor x y)])]
                      [args (let-values ([(syms vals) (partition term? args)])
                              (if (null? vals) 
                                  (apply expression @bvxor (sort syms term<?))
                                  (let ([val (apply bitwise-xor vals)])
                                    (match syms
                                      [(list) val]
                                      [(list n) (@bvxor val n)]
                                      [_        (apply expression @bvxor val (sort syms term<?))]))))]))
                    
(define-syntax-rule (define-idempotent-unary-op id name racket-op)
  (define-op id 
    #:name name 
    #:type unary-type 
    #:op (match-lambda [(? number? x) (racket-op x)]
                       [(and (expression (== id) y) x) x]
                       [x (expression id x)])))
                         
(define-idempotent-unary-op @bvabs 'abs abs)
(define-idempotent-unary-op @bvsgn 'sgn sgn)

(define-op @bvsqrt
  #:name 'sqrt
  #:type unary-type
  #:op
  (match-lambda
    [(? number? x) (sqrt (max 0 x))]
    [(expression (== @bvmul) x x) (@bvabs x)]
    [(expression (== @expt) x (and (? integer?) (? even?) k)) (@expt (@bvabs x) (/ k 2))]
    [x (define n (arithmetic-shift (current-bitwidth) -1))
       (let loop ([res 0] [add (arithmetic-shift 1 (sub1 n))] [i n])
         (if (<= i 0) 
             res
             (let ([tmp (@bvor res add)])
               (loop (merge (@bvsge x (@bvmul tmp tmp)) tmp res) 
                     (arithmetic-shift add -1) 
                     (sub1 i)))))]))
                


(define @bvadd-info (list + 0 #f @bvmul    (lambda (e) (match e 
                                                       [(expression (== @bvmul) (? number? n) x) (list x n)]
                                                       [_ #f]))))
(define @bvmul-info (list * 1 0  @expt (lambda (e) (match e 
                                                       [(expression (== @expt) x (? number? n)) (list x n)]
                                                       [_ #f]))))

; Applies the binary +/* operator to the given arguments.
(define (binary:+/* op op-info a b)
  (or (simplify-arithmetic op op-info a b) 
      (cond [(number? a) (expression op a b)]
            [(number? b) (expression op b a)]
            [else (sort/expression op a b)])))

; Applies the nary +/* operator to the given arguments.
(define (nary:+/* op op-info args)
  (let*-values ([(primitive-op identity annihilator) (values (first op-info) (second op-info) (third op-info))]
                [(num-args term-args) (partition number? args)]    
                [(num-fold) (foldl primitive-op identity num-args)])
    (cond [(null? term-args) num-fold]
          [(equal? num-fold annihilator) annihilator]
          ;[else (expression op (cons num-fold (sort term-args term<?)))])))
          [else (let*-values ([(num-simp term-simp) (partition number? (simplify-arithmetic-fp op op-info term-args))]
                              [(term-out) (sort term-simp term<?)]
                              [(num-out) (primitive-op num-fold (foldl primitive-op identity num-simp))])
                             (cond [(null? term-out) num-out]
                                   [(= num-out identity) (if (null? (cdr term-out)) 
                                                             (car term-out) 
                                                             (apply expression op term-out))]
                                   [else (apply expression op (cons num-out term-out))]))])))

; Applies (simplify-arithmetic op op-info) to the given arguments until it reaches a fix point.
; This function assumes that a given argument can be paired up with at most one other 
; argument for the purposes of simplification.
(define (simplify-arithmetic-fp op op-info args)
  (define (simplify head tail)
    (cond [(null? tail) head]
          [(null? (cdr tail)) (append head tail)]
          [else (let simplify-tail ([a (car tail)] [b-head '()] [b-tail (cdr tail)])
                  (if (null? b-tail)
                      (simplify (append head (list a)) b-head)
                      (let ([simp (simplify-arithmetic op op-info a (car b-tail))])
                        (if simp 
                            (simplify head (append b-head (cons simp (cdr b-tail))))
                            (simplify-tail a (append b-head (list (car b-tail))) (cdr b-tail))))))]))
  (let ([simp (simplify '() args)])
    (if (equal? simp args) 
        args 
        (simplify-arithmetic-fp op op-info simp))))

; Applies basic arithmetic simplifications to two arguments, a and b, assuming that op is @bvadd or 
; @bvmul.  The op-info list must contain 5 values:  
; (0) primitive-op, which is the primitive Racket operator corresponding to op;
; (1) identity, which is the identity element for op; 
; (2) annihilator, which is an element such that (op e annihilator) = annihilator, or #f if no such element exists;
; (3) agg-op, which is an operator such that (op x (agg-op x -1)) = identity, and (agg-op x n) = (op x ...), where x occurs n times; and, 
; (4) agg?, which is a function that returns (list x n) when applied to an expression of the form (agg-op x n) or 
;    (agg-op n x), or #f otherwise.
; Returns #f if no simplifications are applicable; otherwise returns the simplified result.
(define (simplify-arithmetic op op-info a b)
  (match op-info
    [(list primitive-op identity annihilator agg-op agg?)               
     (match* (a b) 
       [((? number? a) (? number? b)) (primitive-op a b)]
       [((== annihilator) b) annihilator]
       [(a (== annihilator)) annihilator]
       [((== identity) b) b]
       [(a (== identity)) a]
       [(_ (== a)) (agg-op a 2)]
       [((? number? a) (? expression? b)) 
        (match b
          [(expression (== op) (? number? n) x) (op (primitive-op a n) x)]
          [(app agg? (list (expression (== op) (? number? n) x) -1)) (op (op a (agg-op n -1)) (agg-op x -1))]
          [(expression (== ite) c (? number? x) (? number? y)) (ite c (primitive-op a x) (primitive-op a y))]
          [_ #f])]
       [((? expression? a) (? number? b)) (simplify-arithmetic op op-info b a)] 
       [((? term? a) (? term? b)) 
        (let basic-laws ([a a] [b b] [try-again #t])
          (match b
            [(expression (== op) x (? (curry cancel? agg? a))) x]
            [(expression (== op) (? (curry cancel? agg? a)) y) y]
            [(app agg? (list (expression (== op) x (== a)) -1)) (agg-op x -1)]
            [(app agg? (list (expression (== op) (== a) y) -1)) (agg-op y -1)]
            [(app agg? (list y (? number? n))) 
             (match a 
               [(== y) (agg-op a (+ n 1))]
               [(app agg? (list (== y) (? number? m))) (agg-op y (+ n m))]             
               [_ (and try-again (expression? a) (basic-laws b a #f))])]
            [_ (and try-again (expression? a) (basic-laws b a #f))]))]
       [(_ _) #f])]))

(define (cancel? agg? a b)
  (match* (a b)
    [(_ (app agg? (list (== a) -1))) #t]
    [((app agg? (list (== b) -1)) _) #t]
    [(_ _) #f]))

