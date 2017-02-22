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
    (primitive ("+")     add-prim)
    (primitive ("-")     subtract-prim)
    (primitive ("*")     mult-prim)
    (primitive ("add1")  incr-prim)
    (primitive ("sub1")  decr-prim)))

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
       (eval-expression body (extend-env ids args env))))))

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
    (decr-prim () (- (car args) 1))))

(define (init-env)
  (extend-env
   '(i v x)
   '(1 5 10)
   (empty-env)))

; define the environment

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vec vector?)
   (env environment?)))

(define (empty-env)
  (empty-env-record))

(define (extend-env syms vals env)
  (extended-env-record syms (list->vector vals) env))

(define (apply-env env sym)
  (cases environment env
    (empty-env-record ()
     (eopl:error 'apply-env "No binding for ~s" sym))
    (extended-env-record (syms vals env)
     (let ((position (rib-find-position sym syms)))
          (if (number? position)
              (vector-ref vals position)
              (apply-env env sym))))))

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
|#
