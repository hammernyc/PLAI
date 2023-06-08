#lang plai-typed

; Expression-Core data type ;
(define-type ExprC
   [numC  (n : number)]
   [notC  (e : ExprC)]
   [plusC (l : ExprC) (r : ExprC)]
   [multC (l : ExprC) (r : ExprC)]
   [eqC   (l : ExprC) (r : ExprC)]
   [ltC   (l : ExprC) (r : ExprC)]
   [ifC   (n : ExprC) (t : ExprC) (f : ExprC)])

; Expression-Surface data type ;
(define-type ExprS
   [numS (n : number)]
   [boolS (b : boolean)]
   [notS (e : ExprS)]
   [andS (l : ExprS) (r : ExprS)]
   [orS (l : ExprS) (r : ExprS)]
   [plusS (l : ExprS) (r : ExprS)]
   [multS (l : ExprS) (r : ExprS)]
   [uminusS (e : ExprS)]
   [bminusS (l : ExprS) (r : ExprS)]
   [eqS (l : ExprS) (r : ExprS)]
   [ltS (l : ExprS) (r : ExprS)]
   [gtS (l : ExprS) (r : ExprS)]
   [lteS (l : ExprS) (r : ExprS)]
   [gteS (l : ExprS) (r : ExprS)]
   [ifS (b : ExprS) (t : ExprS) (f : ExprS)])

; Parser (s-expr -> ExprS) ;
(define (parse [s : s-expression]) : ExprS
    (cond
      [(s-exp-number?  s) (numS  (s-exp->number  s))]
      [(s-exp-boolean? s) (boolS (s-exp->boolean s))]
      [(s-exp-list? s)
       (let ([sl (s-exp->list s)])
         (case (s-exp->symbol (first sl))
           [(+)   (plusS (parse (second sl)) (parse (third sl)))]
           [(*)   (multS (parse (second sl)) (parse (third sl)))]
           [(-)   (if (> (length sl) 2)
                      (bminusS (parse (second sl)) (parse (third sl)))
                      (uminusS (parse (second sl))))]
           [(*)   (multS (parse (second sl)) (parse (third sl)))]
           [(not) (notS (parse (second sl)))]
           [(and) (andS (parse (second sl)) (parse (third sl)))]
           [(or)  (orS (parse (second sl)) (parse (third sl)))]
           [(=)   (eqS (parse (second sl)) (parse (third sl)))]
           [(<)   (ltS (parse (second sl)) (parse (third sl)))]
           [(<=)  (lteS (parse (second sl)) (parse (third sl)))]
           [(>)   (gtS (parse (second sl)) (parse (third sl)))]
           [(>=)  (gteS (parse (second sl)) (parse (third sl)))]
           [(if)  (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
           [else  (error 'parse "invalid list input")]))]
      [else (error 'parse "invalid input")]))

; Desugarer (ExprS -> ExprC) ;
(define (desugar [as : ExprS]) : ExprC
    (type-case ExprS as
      ;; core
      [numS  (n)  (numC n)]
      [notS (e)   (notC (desugar e))]
      [plusS (l r) (plusC (desugar l)
                          (desugar r))]
      [multS (l r) (multC (desugar l)
                          (desugar r))]
      [eqS (l r) (eqC (desugar l)
                      (desugar r))]
      [ltS (l r) (ltC (desugar l)
                      (desugar r))]
      [ifS (c t f)  (ifC (desugar c) (desugar t) (desugar f))]
      
      ;; syntactic sugar
      [boolS (b) (if b (numC 1) (numC 0))]
      [andS (l r) (multC (desugar l)
                         (desugar r))]
      ; (A or B) == not (not A and not B)
      [orS (l r) (notC (multC (notC (desugar l))
                              (notC (desugar r))))]
      [gtS (l r) (multC (notC (ltC (desugar l) (desugar r)))
                        (notC (eqC (desugar l) (desugar r))))]
      [gteS (l r) (notC (ltC (desugar l) (desugar r)))]
      [lteS (l r) (notC (multC (notC (ltC (desugar l) (desugar r)))
                               (notC (eqC (desugar l) (desugar r)))))]
      [uminusS (e) (multC (numC -1) (desugar e))]
      [bminusS (l r) (plusC (desugar l)
                            (multC (numC -1) (desugar r)))]))

; Interpreter (ExprC -> number) ;
 (define (interp [a : ExprC]) : number
    (type-case ExprC a
      [numC (n) n]
      [notC (e) (if (= (interp e) 0) 1 0)]
      [plusC (l r) (+ (interp l) (interp r))]
      [multC (l r) (* (interp l) (interp r))]
      [eqC (l r) (if (= (interp l) (interp r)) 1 0)]
      [ltC (l r) (if (< (interp l) (interp r)) 1 0)]
      [ifC (c t f) (if (> (interp c) 0) (interp t) (interp f))]))

; Tests ;
(test (interp (desugar (parse '(+ 1 (+ 2 (+ 3 4)))))) 10)
(test (interp (desugar (parse '(* 1 (* 2 (* 3 4)))))) 24)
(test (interp (desugar (parse '(- 1 (- 2 (- 3 4)))))) -2)
(test (interp (desugar (parse '(- 7)))) -7)

(test (interp (desugar (parse '(if (< 3 2) (+ 1 2) (+ 3 4))))) 7)
(test (interp (desugar (parse '(if (>= 3 2) (+ 1 2) (+ 3 4))))) 3)

