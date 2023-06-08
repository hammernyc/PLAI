#lang plai-typed
; Arithmetic-Core data type ;
(define-type ArithC
   [numC (n : number)]
   [plusC (l : ArithC) (r : ArithC)]
   [multC (l : ArithC) (r : ArithC)])

; Arithmetic-Surface data type ;
(define-type ArithS
   [numS (n : number)]
   [plusS (l : ArithS) (r : ArithS)]
   [multS (l : ArithS) (r : ArithS)]
   [uminusS (e : ArithS)]
   [bminusS (l : ArithS) (r : ArithS)])

; Parser (s-expr -> ArithS) ;
(define (parse [s : s-expression]) : ArithS
    (cond
      [(s-exp-number? s) (numS (s-exp->number s))]
      [(s-exp-list? s)
       (let ([sl (s-exp->list s)])
         (case (s-exp->symbol (first sl))
           [(+) (plusS (parse (second sl)) (parse (third sl)))]
           [(*) (multS (parse (second sl)) (parse (third sl)))]
           [(-) (if (> (length sl) 2)
                    (bminusS (parse (second sl)) (parse (third sl)))
                    (uminusS (parse (second sl))))]
           [else (error 'parse "invalid list input")]))]
      [else (error 'parse "invalid input")]))

; Desugarer (ArithS -> ArithC) ;
(define (desugar [as : ArithS]) : ArithC
    (type-case ArithS as
      [numS (n) (numC n)]
      [plusS (l r) (plusC (desugar l)
                          (desugar r))]
      [multS (l r) (multC (desugar l)
                          (desugar r))]
      [uminusS (e) (multC (numC -1) (desugar e))]
      [bminusS (l r) (plusC (desugar l)
                            (multC (numC -1) (desugar r)))]))

; Interpreter (ArithC -> number) ;
 (define (interp [a : ArithC]) : number
    (type-case ArithC a
      [numC (n) n]
      [plusC (l r) (+ (interp l) (interp r))]
      [multC (l r) (* (interp l) (interp r))]))

; Tests ;
(test (interp (desugar (parse '(+ 1 (+ 2 (+ 3 4)))))) 10)
(test (interp (desugar (parse '(* 1 (* 2 (* 3 4)))))) 24)
(test (interp (desugar (parse '(- 1 (- 2 (- 3 4)))))) -2)
(test (interp (desugar (parse '(- 7)))) -7)
