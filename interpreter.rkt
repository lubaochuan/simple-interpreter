#lang eopl

; define lexical spec

(define scanner-spec-3-1
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)))

; define grammar spec
(define grammar-3-1
  '((program
     (expression)
     a-program)
    (expression
     (number)
     lit-exp)
    (expression
     (identifier)
     var-exp)   
    (expression
      (primitive "(" (separated-list expression ",") ")")
      primapp-exp)
    (expression
      ("if" expression "then" expression "else" expression)
      if-exp)
    (expression
      ("let" (arbno  identifier "=" expression) "in" expression)
      let-exp)
    (expression
      ("proc" "(" (separated-list identifier ",") ")" expression)
      proc-exp)
    (expression
      ("(" expression (arbno expression) ")")
      app-exp)
    (expression
      ("letrec"
        (arbno identifier "(" (separated-list identifier ",") ")"
          "=" expression)
        "in" expression)
      letrec-exp)
    (expression ("set" identifier "=" expression) varassign-exp)
    (expression
     ("begin" expression (arbno ";" expression) "end")
     begin-exp)
    (primitive ("+")     add-prim)
    (primitive ("-")     subtract-prim)
    (primitive ("*")     mult-prim)
    (primitive ("add1")  incr-prim)
    (primitive ("sub1")  decr-prim)
    (primitive ("zero?") zero-test-prim)))

; make parser

(define scan&parse
  (sllgen:make-string-parser
   scanner-spec-3-1
   grammar-3-1))

; create define-datatypes from grammar

(sllgen:make-define-datatypes scanner-spec-3-1 grammar-3-1)

; define evaluator

(define (run string)
  (eval-program
   (scan&parse string)))

(define (eval-program  pgm)
  (cases program pgm
    (a-program (body)
     (eval-expression body (init-env)))))

(define (eval-expression exp env)
  (cases expression exp
    (lit-exp (datum) datum)
    (var-exp (id) (apply-env env id))
    (primapp-exp (prim rands)
     (let ((args (eval-rands rands env)))
       (apply-primitive prim args)))
    (if-exp (test-exp true-exp false-exp)
     (if (true-value? (eval-expression test-exp env))
         (eval-expression true-exp env)
         (eval-expression false-exp env)))
    (let-exp (ids rands body)
     (let ((args (eval-rands rands env)))
       (eval-expression body (extend-env ids args env))))
    (proc-exp (ids body) (closure ids body env))
    (app-exp (rator rands)
     (let ((proc (eval-expression rator env))
           (args (eval-rands rands env)))
       (if (procval? proc)
           (apply-procval proc args)
           (eopl:error 'eval-expression
                       "Attempt to apply non-procedure ~s" proc))))
    (letrec-exp (proc-names idss bodies letrec-body)
     (eval-expression
      letrec-body
      (extend-env-recursively proc-names idss bodies env)))
    (varassign-exp (id rhs-exp)
     (begin
       (setref!
        (apply-env-ref env id)
        (eval-expression rhs-exp env))
       1))
    (begin-exp (exp exps)
               (if (null? exps)
                   (eval-expression exp env)
                   (eval-expression (begin-exp (car exps) (cdr exps)) env)))
    (else (eopl:error 'eval-expression "Not here:~s" exp))))

(define (true-value? x)
  (not (zero? x)))

(define (eval-rands rands env)
  (map (lambda (x)(eval-rand x env)) rands))

(define (eval-rand rand env)
  (eval-expression rand env))

(define (apply-primitive prim args)
  (cases primitive prim
    (add-prim () (+ (car args) (cadr args)))
    (subtract-prim () (- (car args) (cadr args)))
    (mult-prim () (* (car args) (cadr args)))
    (incr-prim () (+ (car args) 1))
    (decr-prim () (- (car args) 1))
    (zero-test-prim () (if (zero? (car args)) 1 0))))

(define (init-env)
  (extend-env
   '(i v x)
   '(1 5 10)
   (empty-env)))

; procedures

(define-datatype procval procval?
  (closure
    (ids (list-of symbol?))
    (body expression?)
    (env environment?)))

(define apply-procval
  (lambda (proc args)
    (cases procval proc
      (closure (ids body env)
        (eval-expression body (extend-env ids args env))))))

; references

(define-datatype reference reference?
  (a-ref
   (position integer?)
   (vec vector?)))

(define (primitive-deref ref)
  (cases reference ref
    (a-ref (pos vec) (vector-ref vec pos))))

(define (primitive-setref! ref val)
  (cases reference ref
    (a-ref (pos vec) (vector-set! vec pos val))))

(define (deref ref)
  (primitive-deref ref))

(define (setref! ref val)
  (primitive-setref! ref val))

; define the environment

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vec vector?)
   (env environment?))
  (recursively-extended-env-record
   (proc-names (list-of symbol?))
   (idss (list-of (list-of symbol?)))
   (bodies (list-of expression?))
   (env environment?)))

(define (empty-env)
  (empty-env-record))

(define (extend-env syms vals env)
  (extended-env-record syms (list->vector vals) env))

(define (extend-env-recursively proc-names idss bodies old-env)
  (recursively-extended-env-record
   proc-names idss bodies old-env))

(define (apply-env-ref env sym)
  (cases environment env
    (empty-env-record ()
     (eopl:error 'apply-env-ref "No binding for ~s" sym))
    (extended-env-record (syms vals env)
     (let ((position (rib-find-position sym syms)))
          (if (number? position)
              (a-ref position vals)
              (apply-env-ref env sym))))
    (recursively-extended-env-record (proc-names idss bodies old-env)
     (let ((pos (rib-find-position sym proc-names)))
       (if (number? pos)
           (closure
            (list-ref idss pos)
            (list-ref bodies pos)
            env)
           (apply-env-ref old-env sym))))))

(define (apply-env env sym)
  (deref (apply-env-ref env sym)))

(define (rib-find-position sym los)
  (list-find-position sym los))

(define (list-find-position sym los)
  (list-index (lambda (sym1) (eqv? sym1 sym)) los))

(define (list-index pred ls)
  (cond
    ((null? ls) #f)
    ((pred (car ls)) 0)
    (else (let ((list-index-r (list-index pred (cdr ls))))
            (if (number? list-index-r)
                (+ list-index-r 1)
                #f)))))

#|
tests
(run "3")
(run "x")
(run "+(3,x)")
(run "add1(+(3,x))")
(run "if 1 then 2 else 3")
(run "if i then x else 3")
(run "if -(3,+(1,2)) then 2 else 3")
(run "let x=5
          y=6
      in +(x,y)")
(run "let x=1
      in let x=+(x,2)
         in add1(x)")
(run "let f=proc (y,z) +(y,-(z,5))
      in (f 2 28)")
(run "let x=5
      in let f=proc (y,z) +(y,-(z,x))
         in let x=28
            in (f 2 x)")
(run "
let makemult = proc (maker, x)
                 if x
                 then +(4,(maker maker -(x,1)))
                 else 0
in let times4 = proc (x) (makemult makemult x)
   in (times4 4)
")

(run "
let factorial = proc (fact, x)
                if x then *(x,(fact fact -(x,1)))
                else 1
in (factorial factorial 5)
")

(run "
letrec fact(x) = if zero?(x) then 1 else *(x, (fact sub1(x)))
in (fact 6)
")

(run "
letrec even(x) = if zero?(x) then 1 else (odd sub1(x))
       odd(x)  = if zero?(x) then 0 else (even sub1(x))
in (odd 13)
")

(run "
let x = 0
in letrec
     even() = if zero?(x)
              then 1
              else let  d = set x = sub1(x)
                   in (odd)
     odd()  = if zero?(x)
              then 0
              else let d = set x = sub1(x)
                   in (even)
   in let d = set x = 13
      in (odd)
")

(run "
let count = 0
in let d = set count = 1
   in count
")

(run "
let g = let count = 0
        in proc ()
             let d = set count = add1(count)
             in count
in +((g),(g))
")

(run "
let x = 100
in let p = proc (x) let d = set x = add1(x)
                    in x
   in +((p x),(p x))
")

(run "
begin
  +(1, 2);
  -(2, 3);
  42
end
")
|#
