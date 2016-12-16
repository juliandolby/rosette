#lang rosette

(define-symbolic x string?)
(define-symbolic y string?)
(define-symbolic z integer?)

(current-bitwidth #f)

(define (show msg ex . strs)
  (define model (solve (apply ex strs)))
  (apply printf msg (map model strs)))

(define (ex1 x)
  (assert (equal? (string-append x "ab") (string-append "ba" x)))
  (assert (= (string-length x) 7)))

(define (ex2 x y)
  (assert (not (equal? x y)))
  (assert (= (string-length x) 3))
  (assert (= (string-length x) (string-length y))))

(define (ex3 x y)
  (assert (not (equal? (string-append x y) (string-append y x)))))

(define (ex6 x y)
  (assert (and (> (string-length y) 0) (string-prefix? x y) (not (equal? x y)))))

(define (ex7 x y)
  (assert (and (= (string-length x) 10) (= (string-length y) 5) (string-prefix? x y))))

(define (ex8 x y)
  (assert (and (> (string-length y) 0) (string-suffix? x y) (not (equal? x y)))))

(define (ex9 x y)
  (assert (and (= (string-length x) 10) (= (string-length y) 5) (string-suffix? x y))))


(show "Find an assignment for x, where x.\"ab\"=\"ba\".x and the length of x equals to 7:\n x = ~s\n" ex1 x)
(show "Find assignments for x and y, where x and y are distinct and their lengths are equal:\n x = ~s, y = ~s\n" ex2 x y)
(show "Find assignments for x and y, where x.y != y.x.\n x = ~s, y = ~s\n" ex3 x y)
(show "Find a string and a prefix.\n x = ~s, y = ~s\n" ex6 x y)     
(show "Find a string and a prefix.\n x = ~s, y = ~s\n" ex7 x y)     
(show "Find a string and a suffix.\n x = ~s, y = ~s\n" ex8 x y)     
(show "Find a string and a suffix.\n x = ~s, y = ~s\n" ex9 x y)  
