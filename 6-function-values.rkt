#lang plai-typed

; Value ;
(define-type Value
    [numV (n : number)]
    [closV (arg : symbol) (body : ExprC) (env : Env)])

(define (num+ [l : Value] [r : Value]) : Value
    (cond
      [(and (numV? l) (numV? r))
       (numV (+ (numV-n l) (numV-n r)))]
      [else
       (error 'num+ "one argument was not a number")]))

(define (num* [l : Value] [r : Value]) : Value
    (cond
      [(and (numV? l) (numV? r))
       (numV (* (numV-n l) (numV-n r)))]
      [else
       (error 'num+ "one argument was not a number")]))

; Expression-Core data type ;
(define-type ExprC
   [numC  (n : number)]
   [idC   (s : symbol)]
   [plusC (l : ExprC) (r : ExprC)]
   [multC (l : ExprC) (r : ExprC)]
   [lamC  (arg : symbol) (body : ExprC)]
   [appC  (fun : ExprC) (arg : ExprC)])

; Environment ;
(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

(define (lookup [for : symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "name not found")]
    [else (cond
            [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

; Expression-Surface data type ;
(define-type ExprS
   [numS (n : number)]
   [idS   (s : symbol)]
   [plusS (l : ExprS) (r : ExprS)]
   [multS (l : ExprS) (r : ExprS)]
   [uminusS (e : ExprS)]
   [bminusS (l : ExprS) (r : ExprS)]
   [lamS (arg : symbol) (body : ExprS)]
   [letS (s : symbol) (v : ExprS) (body : ExprS)]
   [appS  (fun : ExprS) (arg : ExprS)])

; Parser (s-expr -> ExprS) ;
(define (parse [s : s-expression]) : ExprS
    (cond
      [(s-exp-number?  s) (numS  (s-exp->number  s))]
      [(s-exp-symbol? s) (idS (s-exp->symbol s))]
      [(s-exp-list? s)
       (let ([sl (s-exp->list s)])
         (case (s-exp->symbol (first sl))
           [(+)   (plusS (parse (second sl)) (parse (third sl)))]
           [(*)   (multS (parse (second sl)) (parse (third sl)))]
           [(-)   (if (> (length sl) 2)
                      (bminusS (parse (second sl)) (parse (third sl)))
                      (uminusS (parse (second sl))))]
           [(*)   (multS (parse (second sl)) (parse (third sl)))]
           [else  (appS (parse (first sl)) (parse (second sl)))]))] ; sketchy
      [else (error 'parse "invalid input")]))

; Desugarer (ExprS -> ExprC) ;
(define (desugar [as : ExprS]) : ExprC
    (type-case ExprS as
      ;; core
      [numS  (n)     (numC n)]
      [idS   (s)     (idC s)]
      [plusS (l r)   (plusC (desugar l)
                            (desugar r))]
      [multS (l r)   (multC (desugar l)
                            (desugar r))]
      [lamS  (a b)   (lamC a (desugar b))]
      [appS  (f a)   (appC (desugar f) (desugar a))]
      
      ;; syntactic sugar
      [letS (s v b)  (appC (lamC s (desugar b)) (desugar v))] ; ?
      [uminusS (e)   (multC (numC -1) (desugar e))]
      [bminusS (l r) (plusC (desugar l)
                            (multC (numC -1) (desugar r)))]))

; Interpreter (ExprC -> number) ;
 (define (interp [expr : ExprC] [env : Env]) : Value
    (type-case ExprC expr
      [numC (n) (numV n)]
      [idC (n) (lookup n env)]
      [plusC (l r) (num+ (interp l env) (interp r env))]
      [multC (l r) (num* (interp l env) (interp r env))]
      [lamC (a b) (closV a b env)]
      [appC (f a) (local ([define f-value (interp f env)])
                    (if (closV? f-value)
                         (interp (closV-body f-value)
                            (extend-env (bind (closV-arg f-value)
                                             (interp a env))
                            (closV-env f-value)))
                         (error 'appC "one argument was not a number")))]))

(test (interp (desugar (parse '(+ 1 (+ 2 (+ 3 4))))) mt-env) (numV 10))
(test (interp (desugar (parse '(* 1 (* 2 (* 3 4))))) mt-env) (numV 24))
(test (interp (desugar (parse '(- 1 (- 2 (- 3 4))))) mt-env) (numV -2))
(test (interp (desugar (parse '(- 7))) mt-env) (numV -7))

(test (interp (plusC (numC 10) (appC (lamC '_ (numC 5)) (numC 10)))
                mt-env)
        (numV 15))

(test (interp (appC (lamC 'x (appC (lamC 'y (plusC (idC 'x) (idC 'y)))
                                          (numC 4)))
                        (numC 3))
                  mt-env)
          (numV 7))

; 8

(test (interp (desugar (plusS (numS 10) (appS (lamS '_ (numS 5)) (numS 10))))
                mt-env)
        (numV 15))
