#lang plai-typed

; Bool-Core data type ;
(define-type BoolC
   [boolC (b : boolean)]
   [notC (e : BoolC)]
   [orC (l : BoolC) (r : BoolC)])

; Bool-Surface data type ;
(define-type BoolS
   [boolS (b : boolean)]
   [notS (e : BoolS)]
   [orS (l : BoolS) (r : BoolS)]
   [andS (l : BoolS) (r : BoolS)])

; Parser (s-expr -> BoolS) ;
(define (parse [s : s-expression]) : BoolS
    (cond
      [(s-exp-boolean? s) (boolS (s-exp->boolean s))]
      [(s-exp-list? s)
       (let ([sl (s-exp->list s)])
         (case (s-exp->symbol (first sl))
           [(!)  (notS (parse (second sl)))]
           [(&&) (andS (parse (second sl)) (parse (third sl)))]
           [(||) (orS (parse (second sl)) (parse (third sl)))]
           [else (error 'parse "invalid list input")]))]
      [else (error 'parse "invalid input")]))

; Desugarer (BoolS -> BoolC) ;
(define (desugar [as : BoolS]) : BoolC
    (type-case BoolS as
      [boolS (b) (boolC b)]
      [orS (l r) (orC  (desugar l)
                       (desugar r))]
      [andS (l r) (notC (orC  (notC (desugar l))
                              (notC (desugar r))))]
      [notS (e)  (notC (desugar e))]))

; Interpreter (BoolC -> boolean) ;
 (define (interp [a : BoolC]) : boolean
    (type-case BoolC a
      [boolC (b) b]
      [orC (l r) (or (interp l) (interp r))]
      [notC (e) (not (interp e))]))

; Tests ;
(test (interp (desugar (parse '(! #f)))) #t)
(test (interp (desugar (parse '(! #t)))) #f)
(test (interp (desugar (parse '(|| #f (|| #f #f))))) #f)
(test (interp (desugar (parse '(|| (|| #f #t) (|| #f #f))))) #t)

(test (interp (desugar (parse '(&& #f #f)))) #f)
(test (interp (desugar (parse '(&& #t #f)))) #f)
(test (interp (desugar (parse '(&& #f #t)))) #f)
(test (interp (desugar (parse '(&& #t #t)))) #t)

(test (interp (desugar (parse '(&& (&& #t #t) (&& #t #t))))) #t)

