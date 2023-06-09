#lang plai-typed

; Expression-Core data type ;
(define-type ExprC
   [numC  (n : number)]
   [notC  (e : ExprC)]
   [plusC (l : ExprC) (r : ExprC)]
   [multC (l : ExprC) (r : ExprC)]
   [eqC   (l : ExprC) (r : ExprC)]
   [ltC   (l : ExprC) (r : ExprC)]
   [ifC   (c : ExprC) (t : ExprC) (f : ExprC)]
   [idC   (s : symbol)]
   [appC  (fun : symbol) (arg : ExprC)])

(define-type FunDefC
  [fdC (name : symbol) (arg : symbol) (body : ExprC)])


(define given-functions (list
 (fdC 'inc    'x (plusC (idC 'x) (numC 1)))
 (fdC 'square 'x (multC (idC 'x) (idC 'x)))
 (fdC 'double 'x (multC (numC 2) (idC 'x)))))

(define (get-fundef [name : symbol] [fds : (listof FunDefC)]) : FunDefC
  (cond
    [(empty? fds) (error 'get-fundef "reference to undefined function")]
    [(cons? fds)  (cond
                    [(equal? name (fdC-name (first fds))) (first fds)]
                    [else (get-fundef name (rest fds))]
                    )]
    )
  )

(define (subst [what : ExprC] [for : symbol] [in : ExprC]) : ExprC ; lazy
    (type-case ExprC in
    [numC (n) in]
    [idC (s) (cond
               [(symbol=? s for) what]
               [else in])]
    [appC (f a)  (appC f (subst what for a))]
    [notC  (e)   (notC (subst what for e))]
    [plusC (l r) (plusC (subst what for l)
                        (subst what for r))]
    [multC (l r) (multC (subst what for l)
                        (subst what for r))]
    [eqC (l r) (eqC     (subst what for l)
                        (subst what for r))]
    [ltC (l r) (ltC     (subst what for l)
                        (subst what for r))]
    [ifC  (c t f) (ifC  (subst what for c)
                        (subst what for t)
                        (subst what for f))]))


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
   [ifS (c : ExprS) (t : ExprS) (f : ExprS)]
   [idS   (s : symbol)]
   [appS  (fun : symbol) (arg : ExprS)])

; Parser (s-expr -> ExprS) ;
(define (parse [s : s-expression]) : ExprS
    (cond
      [(s-exp-number?  s) (numS  (s-exp->number  s))]
      [(s-exp-boolean? s) (boolS (s-exp->boolean s))]
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
           [(not) (notS (parse (second sl)))]
           [(and) (andS (parse (second sl)) (parse (third sl)))]
           [(or)  (orS (parse (second sl)) (parse (third sl)))]
           [(=)   (eqS (parse (second sl)) (parse (third sl)))]
           [(<)   (ltS (parse (second sl)) (parse (third sl)))]
           [(<=)  (lteS (parse (second sl)) (parse (third sl)))]
           [(>)   (gtS  (parse (second sl)) (parse (third sl)))]
           [(>=)  (gteS (parse (second sl)) (parse (third sl)))]
           [(if)  (ifS  (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
           [else  (appS (s-exp->symbol (first sl)) (parse (second sl)))]))] ; sketchy
      [else (error 'parse "invalid input")]))

; Desugarer (ExprS -> ExprC) ;
(define (desugar [as : ExprS]) : ExprC
    (type-case ExprS as
      ;; core
      [numS  (n)     (numC n)]
      [notS  (e)     (notC (desugar e))]
      [plusS (l r)   (plusC (desugar l)
                            (desugar r))]
      [multS (l r)   (multC (desugar l)
                            (desugar r))]
      [eqS   (l r)   (eqC (desugar l)
                          (desugar r))]
      [ltS   (l r)   (ltC (desugar l)
                          (desugar r))]
      [ifS   (c t f) (ifC (desugar c) (desugar t) (desugar f))]
      [idS   (s)     (idC s)]
      [appS  (f a)   (appC f (desugar a))]
      
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
 (define (interp [a : ExprC] [fds : (listof FunDefC)]) : number
    (type-case ExprC a
      [numC (n) n]
      [idC (_) (error 'interp "shouldn't get here")]
      [notC (e) (if (= (interp e fds) 0) 1 0)]
      [plusC (l r) (+ (interp l fds) (interp r fds))]
      [multC (l r) (* (interp l fds) (interp r fds))]
      [eqC (l r) (if (= (interp l fds) (interp r fds)) 1 0)]
      [ltC (l r) (if (< (interp l fds) (interp r fds)) 1 0)]
      [ifC (c t f) (if (> (interp c fds) 0) (interp t fds) (interp f fds))]
      [appC (f a) (local ([define fd (get-fundef f fds)])
                    (interp (subst a ; lazy
                                   (fdC-arg fd)
                                   (fdC-body fd))
                            fds))]))

; Tests ;
(test (interp (desugar (parse '(+ 1 (+ 2 (+ 3 4))))) given-functions) 10)
(test (interp (desugar (parse '(* 1 (* 2 (* 3 4))))) given-functions) 24)
(test (interp (desugar (parse '(- 1 (- 2 (- 3 4))))) given-functions) -2)
(test (interp (desugar (parse '(- 7))) given-functions) -7)

(test (interp (desugar (parse '(if (< 3 2) (+ 1 2) (+ 3 4)))) given-functions) 7)
(test (interp (desugar (parse '(if (>= 3 2) (+ 1 2) (+ 3 4)))) given-functions) 3)


(test (interp (desugar (parse '(square (double (inc 4))))) given-functions) 100)
