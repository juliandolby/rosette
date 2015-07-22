#lang racket

(require "term.rkt" "op.rkt" "union.rkt" "bool.rkt" "any.rkt" "generic.rkt" "merge.rkt"
         (only-in "bitwise.rkt" define-not define-and define-or))

(provide 
 @bitvector?           
 @bveq @bvslt @bvsle @bvsgt @bvsge @bvult @bvule @bvugt @bvuge
 @bvadd @bvsub @bvmul @bvurem @bvudiv @bvsdiv @bvsrem @bvsmod                 
 @bvshl @bvashr @bvlshr
 @bvnot @bvand @bvor @bvxor
 current-bitwidth ignore-division-by-0)

(define ignore-division-by-0
  (make-parameter #f))

(define current-bitwidth
  (make-parameter 5 
                  (lambda (bw) 
                    (unless (and (integer? bw) (positive? bw))
                      (raise-argument-error 'current-bitwidth "positive integer" bw))
                    bw)))

(define (sfinitize num) 
  (match num
    [(? integer? v) 
     (let* ([bitwidth (current-bitwidth)]
              [mask (arithmetic-shift -1 bitwidth)]
              [masked (bitwise-and (bitwise-not mask) v)])
         (if (bitwise-bit-set? masked (- bitwidth 1))
             (bitwise-ior mask masked)  
             masked))]
    [_ num]))

(define (ufinitize num) 
  (match num
    [(? integer? v) 
     (let* ([bitwidth (current-bitwidth)]
            [mask (arithmetic-shift -1 bitwidth)]
            [masked (bitwise-and (bitwise-not mask) v)])
       masked)]
    [_ num]))

(define (bv/cast v)
  (match v
    [(? integer?) (values #t (sfinitize v))]
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
             [(_ _) v])]))

(define (bv/compress force? ps) ; force? is ignored since numbers are immutable and therefore always merged
  ;(printf "bv/compress ~a ~a\n" (length ps) ps)
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

(define (bv/eq? x y) (@bveq x y))
  
(define-primitive-type @bitvector? 
  #:pred     (instance-of? integer? @bitvector?) 
  #:least-common-supertype (lambda (t) (if (eq? t @bitvector?) @bitvector? @any?))
  #:eq?      bv/eq?
  #:equal?   bv/eq?
  #:cast     bv/cast
  #:compress bv/compress)

(define binary-predicate-type (op/-> (@bitvector? @bitvector?) @boolean?))
(define nary-type (op/-> (#:rest @bitvector?) @bitvector?))
(define binary-type (op/-> (@bitvector? @bitvector?) @bitvector?))
(define unary-type (op/-> (@bitvector?) @bitvector?))

(define-syntax-rule (sort/expression op x y) 
  (if (term<? x y) 
      (expression op x y)
      (expression op y x)))

(define-op @bveq  
  #:name 'bveq 
  #:type binary-predicate-type
  #:op   (lambda (a b)
           (match* ((sfinitize a) (sfinitize b))
             [((? integer? x) (? integer? y)) (= x y)]
             [((? integer? x) (? term? y)) (expression @bveq x y)]
             [((? term? x) (? integer? y)) (expression @bveq y x)]
             [(x y) (or (equal? x y) (sort/expression @bveq x y))])))

(define-op @bvult #:name 'bvult #:type binary-predicate-type #:op (lambda (x y) (bvcmp @bvult <  #t ufinitize x y)))
(define-op @bvule #:name 'bvule #:type binary-predicate-type #:op (lambda (x y) (bvcmp @bvule <= #f ufinitize x y)))
(define-op @bvslt #:name 'bvslt #:type binary-predicate-type #:op (lambda (x y) (bvcmp @bvslt <  #t sfinitize x y)))
(define-op @bvsle #:name 'bvsle #:type binary-predicate-type #:op (lambda (x y) (bvcmp @bvsle <= #f sfinitize x y)))
(define-op @bvugt #:name 'bvugt #:type binary-predicate-type #:op (lambda (x y) (@bvult y x)))
(define-op @bvuge #:name 'bvuge #:type binary-predicate-type #:op (lambda (x y) (@bvule y x)))
(define-op @bvsgt #:name 'bvsgt #:type binary-predicate-type #:op (lambda (x y) (@bvslt y x)))
(define-op @bvsge #:name 'bvsge #:type binary-predicate-type #:op (lambda (x y) (@bvsle y x)))

(define (bvcmp @op op strict? finitize a b)
  (match* ((finitize a) (finitize b))
    [(x x) (not strict?)]
    [((? integer? x) (? integer? y)) (op x y)]
    [((? integer? x) (expression (== ite) b (? integer? t) (? integer? f))) 
     (merge b (op x (finitize t)) (op x (finitize f)))] 
    [((expression (== ite) b (? integer? t) (? integer? f)) (? integer? y))
     (merge b (op (finitize t) y) (op (finitize f) y))]
    [(x y) (expression @op x y)]))

(define-op @bvneg
  #:name 'bvneg
  #:type unary-type
  #:op
  (lambda (a)
    (match (sfinitize a)
      [(? integer? x) (sfinitize (- x))]
      [(expression (== @bvneg) x) x]
      [x (expression @bvneg x)])))

(define-op @bvadd 
  #:name 'bvadd 
  #:type nary-type 
  #:op (commutative-associative-nary-operator @bvadd + simplify-bvadd 0))

; Simplifies the addition of a and b, if possible. Returns #f if no simplification is possible.
(define (simplify-bvadd a b)
  (match* (a b)
    [((? integer? x) (? integer? y)) (sfinitize (+ (sfinitize x) (sfinitize y)))]
    [(0 y) (sfinitize y)]
    [(x 0) (sfinitize x)]
    [(x (expression (== @bvneg) x)) 0]
    [((expression (== @bvneg) x) x) 0]
    [(x (expression (== @bvadd) u ... (expression (== @bvneg) x) v ...)) 
     (apply @bvadd (append u v))]
    [((expression (== @bvneg) x) (expression (== @bvadd) u ... x v ...)) 
     (apply @bvadd (append u v))]
    [((expression (== @bvadd) u ... (expression (== @bvneg) x) v ...) x) 
     (apply @bvadd (append u v))]
    [((expression (== @bvadd) u ... x v ...) (expression (== @bvneg) x)) 
     (apply @bvadd (append u v))]
    [(_ _) #f]))


(define-op @bvmul 
  #:name 'bvmul 
  #:type nary-type 
  #:op (commutative-associative-nary-operator @bvmul * simplify-bvmul 1))

; Simplifies the multiplication of a and b, if possible, assuming that both have already been finitized.
; Returns #f if no simplification is possible.
(define (simplify-bvmul a b)
  (match* (a b)
    [(0 _) 0]
    [(_ 0) 0]
    [(1 y) (sfinitize y)]
    [(x 1) (sfinitize x)]
    [(-1 y) (@bvneg y)]
    [(x -1) (@bvneg x)]
    [((? integer? x) (? integer? y)) (sfinitize (* (sfinitize x) (sfinitize y)))]
    [((expression (== @bvneg) x) (expression (== @bvneg) y)) (sort/expression @bvmul x y)]
    [(_ _) #f]))

(define-op @bvsub 
  #:name 'bvsub 
  #:type nary-type 
  #:op 
  (case-lambda 
    [(x) (@bvneg x)]
    [(x y) (@bvadd x (@bvneg y))]
    [(x . y) (apply @bvadd x (map @bvneg y))]))                  

(define (second-non-zero? x y)
  (if (integer? y)
      (not (= y 0))
      (! (@bveq y 0)))) 

(define-op  @bvurem 
  #:name 'bvurem 
  #:type binary-type
  #:pre  second-non-zero?
  #:op   (lambda (x y)
           (match* (x y)
             [(x 0) (if (ignore-division-by-0) 
                        (expression @bvurem x 0)
                        (error '@bvurem "bvurem undefined for 0"))]
             [((? integer? x) (? integer? y)) (sfinitize (remainder (ufinitize x) (ufinitize y)))]
             [(0 x) 0]
             [(x 1) 0]
             [(x x) 0]
             [((? integer? x) (? term? y)) (expression @bvurem (ufinitize x) y)]
             [((? term? x) (? integer? y)) (expression @bvurem x (ufinitize y))]
             [((? term? x) (? term? y))    (expression @bvurem x y)])))

(define-syntax-rule (bv-signed-remainder @op op)
  (lambda (x y)
    (match* (x y)
      [(x 0) (if (ignore-division-by-0) 
                 (expression @op x 0)
                 (error (object-name @op) "undefined for 0"))]
      [((? integer? x) (? integer? y)) (sfinitize (op (sfinitize x) (sfinitize y)))]
      [(0 x) 0]
      [(x 1) 0]
      [(x -1) 0]
      [(x x) 0]
      [(x (expression (== @bvneg x))) 0]
      [((expression (== @bvneg x)) x) 0]
      [((? integer? x) (? term? y)) (expression @op (sfinitize x) y)]
      [((? term? x) (? integer? y)) (expression @op x (sfinitize y))]
      [((? term? x) (? term? y))    (expression @op x y)])))

(define-op  @bvsrem 
  #:name 'bvsrem 
  #:type binary-type
  #:pre  second-non-zero?
  #:op   (bv-signed-remainder @bvsrem remainder))

(define-op  @bvsmod 
  #:name 'bvsmod 
  #:type binary-type
  #:pre  second-non-zero?
  #:op   (bv-signed-remainder @bvsrem modulo))

(define-op  @bvsdiv ; Common simplifications, such as (bvsdiv x x) = 1 do not work, due to 
  #:name 'bvsdiv    ; undefined behavior for division by 0.
  #:type binary-type
  #:pre  second-non-zero?
  #:op   (lambda (x y)
           (match* (x y)
             [(x 0) (if (ignore-division-by-0) 
                        (expression @bvsdiv x 0)
                        (error '@bvsdiv "bvsdiv undefined for 0"))]
             [((? integer? x) (? integer? y)) (sfinitize (quotient (sfinitize x) (sfinitize y)))]
             [(x 1) (sfinitize x)]
             [(x -1) (@bvneg x)]
             [((? integer? x) (? term? y)) (expression @bvsdiv (sfinitize x) y)]
             [((? term? x) (? integer? y)) (expression @bvsdiv x (sfinitize y))]
             [((? term? x) (? term? y))    (expression @bvsdiv x y)])))

(define-op  @bvudiv 
  #:name 'bvudiv 
  #:type binary-type
  #:pre  second-non-zero?
  #:op   (lambda (x y)
           (match* (x y)
             [(x 0) (if (ignore-division-by-0) 
                        (expression @bvudiv x 0)
                        (error '@bvudiv "bvudiv undefined for 0"))]
             [((? integer? x) (? integer? y)) (sfinitize (quotient (ufinitize x) (ufinitize y)))]
             [(x 1) (sfinitize x)]
             [((? integer? x) (? term? y)) (expression @bvudiv (ufinitize x) y)]
             [((? term? x) (? integer? y)) (expression @bvudiv x (ufinitize y))]
             [((? term? x) (? term? y))    (expression @bvudiv x y)])))

(define-op @bvshl
  #:name 'bvshl
  #:type binary-type
  #:op  
  (lambda (x y)
    (match* (x y)
      [(x 0) (sfinitize x)]
      [(0 _) 0]
      [(x (? integer? y))
       (let ([y (ufinitize y)])
         (if (< y (current-bitwidth)) 
             (if (integer? x)
                 (sfinitize (arithmetic-shift (sfinitize x) y)) 
                 (expression @bvshl x y))
             0))]
      [((? integer? x) y) (expression @bvshl (sfinitize x) y)]
      [(x y) (expression @bvshl x y)])))

(define-op @bvlshr
  #:name 'bvlshr
  #:type binary-type
  #:op   
  (lambda (x y)
    (match* (x y)
      [(x 0) (sfinitize x)]
      [(0 _) 0]
      [(x (? integer? y))
       (let ([y (ufinitize y)])
         (if (< y (current-bitwidth))
             (if (integer? x)
                 (sfinitize (arithmetic-shift (ufinitize x) (- y)))
                 (expression @bvlshr x y))
             0))]
      [((? integer? x) y) (expression @bvlshr (sfinitize x) y)]
      [(x y) (expression @bvlshr x y)])))

(define-op @bvashr
  #:name 'bvashr
  #:type binary-type
  #:op   
  (lambda (x y)
    (match* (x y)
      [(x 0) (sfinitize x)]
      [(0 _) 0]
      [(-1 _) -1]
      [((? integer? x) (? integer? y))
       (let ([y (ufinitize y)])
         (if (< y (current-bitwidth))
             (arithmetic-shift (sfinitize x) (- y))
             (if (>= (sfinitize x) 0) 0 -1)))] 
      [(x (? integer? y)) (expression @bvashr x (ufinitize y))]
      [((? integer? x) y) (expression @bvashr (sfinitize x) y)]
      [(x y) (expression @bvashr x y)])))

(define-op @bvnot
  #:name 'bvnot
  #:type unary-type
  #:op
  (lambda (x)
    (match x
      [(? integer? x) (sfinitize (bitwise-not x))]
      [(expression (== @bvnot) x) x]
      [x (expression @bvnot x)])))

(define-op @bvand
  #:name 'bvand
  #:type nary-type 
  #:op   
  (local [(define (simplify-bvand a b)  
            (simplify-bitwise @bvand bitwise-and @bvor -1 0 a b))]
    (commutative-associative-nary-operator @bvand bitwise-and simplify-bvand -1)))

(define-op @bvor
  #:name 'bvor
  #:type nary-type 
  #:op   
  (local [(define (simplify-bvor a b)  
            (simplify-bitwise @bvor bitwise-ior @bvand 0 -1 a b))]
    (commutative-associative-nary-operator @bvor bitwise-ior simplify-bvor 0)))

(define (simplify-bitwise @op op @co identity annihilator a b [commute? #t])
   (match* (a b)
    [((? integer? x) (? integer? y)) (sfinitize (op (sfinitize x) (sfinitize y)))]
    [((== annihilator) _) annihilator]
    [((== identity) y) y]
    [(x x)  x]
    [(x (expression (== @bvnot) x)) annihilator]   
    [(x (expression (== @op) _ ... x _ ...)) b]
    [(x (expression (== @op) _ ... (expression (== @bvnot) x) _ ...)) annihilator] 
    [(x (expression (== @bvnot) (expression (== @co) _ ... x _ ...))) annihilator]
    [(x (expression (== @bvnot) (expression (== @co) _ ... (expression (== @bvnot) x) _ ...))) b]
    [((expression (== @bvnot) x) (expression (== @op) _ ... x _ ...)) annihilator]
    [((expression (== @bvnot) x) (expression (== @bvnot) (expression (== @co) _ ... x _ ...))) b]    
    [((expression (== @op) _ ... x _ ...) 
      (expression (== @op) _ ... (expression (== @bvnot) x) _ ...)) annihilator]   
    [((expression (== @bvnot) (expression (== @co) _ ... x _ ...)) 
      (expression (== @bvnot) (expression (== @co) _ ... (expression (== @bvnot) x) _ ...))) annihilator]   
    [((expression (== @op) _ ... x _ ...) 
      (expression (== @bvnot) (expression (== @co) _ ... x _ ...))) annihilator]
    [(_ _) (and commute? (simplify-bitwise @op op @co identity annihilator a b #f))]))
    
(define-op @bvxor 
  #:name 'bvxor
  #:type nary-type 
  #:op   (commutative-associative-nary-operator @bvxor bitwise-xor simplify-bvxor 0))

(define (simplify-bvxor x y)
  (match* (x y)
    [((? integer?) (? integer?)) (sfinitize (bitwise-xor (sfinitize x) (sfinitize y)))]
    [(_ (== x)) 0]
    [(_ 0) (sfinitize x)]
    [(0 _) (sfinitize y)]
    [(_ -1) (@bvnot x)]
    [(-1 _) (@bvnot y)]
    [(_ (expression (== @bvnot) (== x))) -1]
    [((expression (== @bvnot) (== y)) _) -1] 
    [(_ _) #f]))
    
(define-syntax-rule (commutative-associative-nary-operator @op op simplify-op identity)
  (case-lambda
    [() identity]
    [(x) (sfinitize x)]
    [(x y)
     (or (simplify-op x y)
         (cond [(integer? x) (expression @op (sfinitize x) y)]
               [(integer? y) (expression @op (sfinitize y) x)]
               [else (sort/expression @op x y)]))]
    [args
     (let*-values ([(num-args term-args) (partition integer? args)]
                   [(num-term) (sfinitize (apply op (map sfinitize num-args)))])
       (cond [(null? term-args) num-term]
             [else 
              (match (simplify-fp simplify-op (cons num-term term-args))
                [(list t) t]
                [(list a (... ...) (? integer? n) b (... ...)) (apply expression @op n (sort (append a b) term<?))]
                [other (apply expression @op (sort other term<?))])]))]))

; Simplifies the given list of terms using the given simplification procedure
; until fixed point and returns the resulting list of values.  The simplification 
; procedure should return #f if no simplifications are applicable.  
(define (simplify-fp simplifier args)
  ;(printf "simplify-fp* ~a\n" args)
  (define (simplify head tail)
    ;(printf "simplify ~a ~a\n" head tail)
    (cond [(null? tail) head]
          [(null? (cdr tail)) (append head tail)]
          [else (let simplify-tail ([a (car tail)] [b-head '()] [b-tail (cdr tail)])
                  ;(printf "simplify-tail ~a ~a ~a\n" a b-head b-tail)
                  (if (null? b-tail)
                      (simplify (append head (list a)) b-head)
                      (let ([simp (simplifier a (car b-tail))])
                        (if simp 
                            (simplify head (append b-head (cons simp (cdr b-tail))))
                            (simplify-tail a (append b-head (list (car b-tail))) (cdr b-tail))))))]))
  (let ([simp (simplify '() args)])
    (if (equal? simp args) 
        args 
        (simplify-fp simplifier simp))))
     
     