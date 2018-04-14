#lang curly-fn hackett/private/kernel

(require hackett/private/util/require
         (only-in racket/base begin begin-for-syntax for-syntax)
         (postfix-in - (combine-in racket/base racket/splicing))

         (for-syntax racket/base
                     racket/match
                     racket/pretty
                     racket/syntax
                     syntax/parse/experimental/template

                     hackett/private/typecheck
                     hackett/private/util/stx)
         syntax/parse/define

         (only-in hackett/private/adt type-constructor-val data-constructor-val defn λ*)
         (only-in hackett/private/base ~type)
         (only-in hackett/private/class instance)
         hackett/private/prim
         hackett/private/provide)

(define-simple-macro (begin/type-namespace form ...)
  #:with [form* ...] (map type-namespace-introduce (attribute form))
  (begin form* ...))

(begin/type-namespace
  (require hackett/private/util/require
           (postfix-in - (combine-in racket/base racket/splicing))))

(begin-for-syntax
  ; Given the type of a data constructor, returns the types of its fields, where all type variables
  ; are instantiated using the provided list of replacement types. Order of instantiation is
  ; consistent with the order of type arguments to the type constructor, so when fetching the fields
  ; for (Tuple a b), the first element of inst-tys will be used for a, and the second will be used
  ; for b. If the number of supplied replacement types is inconsistent with the number of arguments to
  ; the type constructor, a contract violation is raised.
  ;
  ; Example:
  ; > (data-con-field-types (list x^ y^) (forall [b a] {a -> Integer -> (Maybe b) -> (Foo a b)}))
  ; (list x^ Integer (Maybe y^))
  ;
  ; While the data constructor type must be a fully-expanded type, the replacement types do not
  ; strictly need to be; they may be arbitrary syntax objects, in which case they will be left
  ; unexpanded in the result.
  ;
  ; (listof type?) type? -> (listof type?)
  (define (data-con-field-types inst-tys con-ty)
    (define/syntax-parse {~#%type:forall* [x ...] t_fn} con-ty)
    (define/syntax-parse
      {~->* t_arg ... {~#%type:app* ({~literal #%type:con} _)
                                    ({~literal #%type:bound-var} con-var) ...}}
      #'t_fn)
    (unless (equal? (length (attribute x)) (length (attribute con-var)))
      (raise-arguments-error 'data-con-field-types
                             "unexpected number of quantified variables in constructor"
                             "quantified" (length (attribute x))
                             "constructor" (length (attribute con-var))))
    (unless (equal? (length (attribute con-var)) (length inst-tys))
      (raise-arguments-error 'data-con-field-types
                             (format "too ~a variables given for instantiation"
                                     (if (> (length (attribute con-var)) (length inst-tys))
                                         "few" "many"))
                             "expected" (length (attribute con-var))
                             "given" (length inst-tys)))
    (define var-subst (map cons (attribute con-var) inst-tys))
    (map #{insts % var-subst} (attribute t_arg))))

(defn println : {String -> (IO Unit)}
  [[str] (do (print str)
             (print "\n"))])



(define-syntax-parser derive-instance/Show
  [(_ {~type ty-con:type-constructor-val})
   #:with [data-con:data-constructor-val ...] (attribute ty-con.data-constructors)
   #:with [ty-con-var-id ...] (build-list (attribute ty-con.arity) generate-temporary)
   #:with [[data-con-field-ty ...] ...] (map #{data-con-field-types (attribute ty-con-var-id) %}
                                             (attribute data-con.type))
   #:with [case-clause ...]
          (for/list ([con-id (in-list (attribute data-con))]
                     [fields (in-list (attribute data-con-field-ty))])
            (with-syntax ([[field-binding-id ...] (generate-temporaries fields)]
                          [con-str (datum->syntax #'here (symbol->string (syntax-e con-id)))])
              (quasitemplate
               [[(#,con-id field-binding-id ...)]
                {"(" ++ con-str {?@ ++ " " ++ (show field-binding-id)} ... ++ ")"}])))
   (syntax-property
    #'(instance (forall [ty-con-var-id ...] (Show data-con-field-ty) ... ...
                        => (Show (ty-con ty-con-var-id ...)))
        [show (λ* case-clause ...)])
    'disappeared-use
    (syntax-local-introduce #'ty-con))])



(data (Foo a) (Bar a) (Baz Integer))
(derive-instance/Show Foo)

(main (do (println (show (Bar "hello")))
          (println (show (: (Baz 42) (Foo String))))))


