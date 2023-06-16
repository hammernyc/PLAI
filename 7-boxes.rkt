#lang plai-typed
; Types ;
(define-type-alias Location number)

(define-type Value
    [numV (n : number)]
    [closV (arg : symbol) (body : ExprC) (env : Env)]
    [boxV (l : Location)])

(define-type Storage
  [cell (location : Location) (val : Value)])
(define-type-alias Store (listof Storage))

(define-type Result
    [v*s (v : Value) (s : Store)])


; Value ;

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
   [appC  (fun : ExprC) (arg : ExprC)]
   [plusC (l : ExprC) (r : ExprC)]
   [multC (l : ExprC) (r : ExprC)]
   [lamC  (arg : symbol) (body : ExprC)]
   [boxC (arg : ExprC)]
   [unboxC (arg : ExprC)]
   [setboxC (b : ExprC) (v : ExprC)]
   [seqC (b1 : ExprC) (b2 : ExprC)])

; Environment ;

(define-type Binding
  [bind (name : symbol) (val : Location)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

(define (lookup [for : symbol] [env : Env]) : Location
  (cond
    [(empty? env) (error 'lookup "name not found")]
    [else (cond
            [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

; Store ;
(define mt-store empty)
(define override-store cons)

(define (fetch [loc : Location] [sto : Store]) : Value
  (cond
    [(empty? sto) (error 'fetch "location not found")]
    [else (cond
            [(= loc (cell-location (first sto)))
             (cell-val (first sto))]
            [else (fetch loc (rest sto))])]))


(define new-loc
  (let ([n (box 0)])
    (lambda ()
      (begin
          (set-box! n (+ (unbox n) 1))
          (unbox n)))))



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
   [beginS (first : ExprS) (second : ExprS)]
   [appS  (fun : ExprS) (arg : ExprS)]
   [boxS (arg : ExprS)]
   [unboxS (arg : ExprS)]
   [setboxS (b : ExprS) (v : ExprS)]
   [seqS (b1 : ExprS) (b2 : ExprS)])

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
      [boxS (a)      (boxC (desugar a))]
      [unboxS (a)    (unboxC (desugar a))]
      [setboxS (b v) (setboxC (desugar b) (desugar v))]
      [seqS (b1 b2)  (seqC (desugar b1) (desugar b2))]       
      
      ;; syntactic sugar
      [letS (s v b)  (appC (lamC s (desugar b)) (desugar v))] ; ?
      [beginS (f s)   (desugar (letS '_ f s))] ;?
      [uminusS (e)   (multC (numC -1) (desugar e))]
      [bminusS (l r) (plusC (desugar l)
                            (multC (numC -1) (desugar r)))]))

; Interpreter (ExprC -> number) ;
 (define (interp [expr : ExprC] [env : Env] [sto : Store]) : Result
    (type-case ExprC expr
      [numC (n) (v*s (numV n) sto)]
      [idC (n) (v*s (fetch (lookup n env) sto) sto)]
      [plusC (l r) (type-case Result (interp l env sto)
               [v*s (v-l s-l)
                    (type-case Result (interp r env s-l)
                      [v*s (v-r s-r)
                           (v*s (num+ v-l v-r) s-r)])])]
      [multC (l r) (type-case Result (interp l env sto)
               [v*s (v-l s-l)
                    (type-case Result (interp r env s-l)
                      [v*s (v-r s-r)
                           (v*s (num* v-l v-r) s-r)])])]
      [lamC (a b) (v*s (closV a b env) sto)]
      [appC (f a)
            (type-case Result (interp f env sto)
              [v*s (v-f s-f)
                   (type-case Result (interp a env s-f)
                     [v*s (v-a s-a)
                          (let ([where (new-loc)])
                            (interp (closV-body v-f)
                                    (extend-env (bind (closV-arg v-f)
                                                      where)
                                                (closV-env v-f))
                                    (override-store (cell where v-a) s-a)))])])]
      [boxC (a) (type-case Result (interp a env sto)
              [v*s (v-a s-a)
                   (let ([where (new-loc)])
                     (v*s (boxV where)
                          (override-store (cell where v-a)
                                          s-a)))])]
      [unboxC (a) (type-case Result (interp a env sto)
                [v*s (v-a s-a)
                     (v*s (fetch (boxV-l v-a) s-a) s-a)])]
      [setboxC (b v) (type-case Result (interp b env sto)
                   [v*s (v-b s-b)
                        (type-case Result (interp v env s-b)
                          [v*s (v-v s-v)
                               (v*s v-v ; returns value, not box?
                                    (override-store (cell (boxV-l v-b) v-v) s-v))])])]
      [seqC (b1 b2) (type-case Result (interp b1 env sto)
                  [v*s (v-b1 s-b1)
                       (interp b2 env s-b1)])]))


(define (eval [s : s-expression]) : Value
  (v*s-v (interp (desugar (parse s)) mt-env mt-store)))

(define (eval-exprs [s : ExprS]) : Value
  (v*s-v (interp (desugar s) mt-env mt-store)))

(define (eval-exprc [c : ExprC]) : Value
  (v*s-v (interp c mt-env mt-store)))

(test (eval '(+ 1 (+ 2 (+ 3 4)))) (numV 10))
(test (eval '(* 1 (* 2 (* 3 4)))) (numV 24))
(test (eval '(- 1 (- 2 (- 3 4)))) (numV -2))
(test (eval '(- 7)) (numV -7))

(test (eval-exprc (plusC (numC 10) (appC (lamC '_ (numC 5)) (numC 10))))
        (numV 15))

(test (eval-exprc (appC (lamC 'x (appC (lamC 'y (plusC (idC 'x) (idC 'y)))
                                          (numC 4)))
                        (numC 3)))
          (numV 7))

; 8

(test (eval-exprs (plusS (numS 10) (appS (lamS '_ (numS 5)) (numS 10))))
        (numV 15))

(test (eval-exprs  (unboxS (boxS (numS 3))))
       (numV 3))

(test (eval-exprs (letS 'b (boxS (numS 0))
                         (setboxS (idS 'b) (numS 2))))
     (numV 2))

(test (eval-exprs (letS 'b (boxS (numS 1)) (setboxS (idS 'b) (plusS (numS 4) (unboxS (idS 'b))))))
       (numV 5))

(test (eval-exprs (unboxS (letS 'b (boxS (numS 1)) (boxS (plusS (numS 1) (unboxS (idS 'b)))))))
        (numV 2))

(test/exn (eval-exprs (plusS (letS 'b (boxS (numS 0)) (numS 1)) (idS 'b)))
      "name not found") 

(test (eval-exprs (letS 'b (boxS (numS -2)) (seqS (setboxS (idS 'b) (plusS (numS 1) (unboxS (idS 'b))))
                                                              (setboxS (idS 'b) (plusS (numS 1) (unboxS (idS 'b))))))) 
        (numV 0))
        