;;; The Mighty BLOOP
(cl:defpackage #:bloop
               (:use #:cl #:alexandria #:anaphora)
               (:export #:bloop #:*tco* #:*break-on-huh*))
(cl:in-package #:bloop)
(declaim (optimize (speed 1) (safety 3) (debug 3)))
#|
line ::= ( lnum-expr [lbody] )
lbody ::= { end-clause | gosub-clause | goto-clause | if-clause | let-clause | print-clause | rem-clause | ret-clause }
end-clause ::= "END"
gosub-clause ::= "GOSUB" target-expr
goto-clause ::= "GOTO" target-expr
if-clause := "IF" logic-expr "THEN" target-expr
let-clause ::= "LET" identifier "=" val-expr
print-clause ::= "PRINT" { val-expr | "," | "_" }*
rem-clause = "REM" ignored*
ret-clause ::= "RETURN"
lnum-expr ::= { fixnum-expression }
identifier ::= { "A".."Z" } digit* ["$"]
target-expr ::= { fixnum-expression }
val-expr ::= { numeric-expression | string-expression }
logic-expr ::= { false-expr | true-expr }
false-expr ::= { zero-expr | empty-string-expr | nil-expr }
true-expr ::= { non-zero-expr | non-empty-expr | not-nil-expr }

Semantics:

lnum-expr's are evaluated at compile-time. They must be in the range 1..65535.

Other expressions are evaluated at run-time and may be dynamic.

A `val-expr' may be:

    - A symbol of form `identifier'. It is an error for it to be uninterned or
      unbound. It will be treated as a var and its symbol-value will be the
      expression value..

    - Some other bound symbol; it's symbol-value will be used.

    - Other unbound symbols: the expression value will be the symbol itself.

    - Other: it will be (EVAL'd) and the resulting value used.

Line forms can be in any order with respect to their line numbers. The lines
will be sorted as part of the compilation.

Multiple line forms may have the same line number; the first such form will be
used and later ones ignored. This allows modifying the program by pushing a new
version of the line onto the program body.

A line form may consist of just a line number; with the lbody nil. This allows
deleting lines by pushing a new empty definition of the line onto the program
body.

The line-number targets of GOTO and GOSUB do not need to actually exist in the
progam body. The jumped-to line will be the first with a line # >= the target.

PRINT separates immediately adjacent `val-expr' forms with a space. A
#\Newline is automatically written after the clause forms, unless the last form
was a control form (a symbol whose name is "%" or "_"). Control forms are not
directly printed. The "%" control causes the cursor to advance to the next
8-char tab stop. The "_" does nothing other than preventing automatic
whitespace; if it is between two `val-expr's then no space is printed between
them, and if it is the last form in the clause then it prevents the automatic
#\Newline.

The distinction between string and non-string variables (A$ vs A) isn't enforced.

Yes, I know it's actually more work to parse IDs this way than just allowing
arbitrary characters. Just trying to keep in historical context.

Parse errors:

?EQ -- No "="; LET form incorrect. Make sure there's whitespace between the
ID, "=" and value expression.

?ID -- Format of identifier string is incorrect.

?LN -- Invalid line number at beginning of line.

?TH -- No "THEN"; IF form incorrect.

??? -- Unrecognized syntax. Make sure there's white space between the syntax
elements, e.g., LET should have three separate ID, "=" and value forms.

Runtime errors:

!DP -- Return stack overflow; too many nested GOSUBs.

!EX -- Error while evaluating expression.

!GO -- Invalid IF/GOTO/GOSUB target line number.

!NG -- Return stack underflow; RETURN without prior GOSUB.

|#

(defvar *tco* nil "If true, do Tail-Call Optimization")
(defvar *break-on-huh* nil "If true, break into debugger on error.")

(defmacro bloop (&body outerbody)
  (let* ((scanned-lines nil)            ; Scanned lines
         (scanned-line-nums nil)        ; All defined line numbers
         (parsed-lines nil) ; Transpiled code for each line. (LIST {line#}{form}*)
         (p-lnum 0))        ; Line # of line currently being parsed
    (labels ((streq (a expect) (and (typep a '(or string symbol))
                                    (let ((av (string-upcase a))) (when (equal av expect) av))))
             (parsing-huh (test label &optional lbody)
               (or test (if *break-on-huh* (break) (error "?~A~@[@~D~]~@[ ~S~]" label (and p-lnum (plusp p-lnum) p-lnum) lbody))))
             (scan-lines (rawbody)
               (loop :for line :in rawbody
                     :for ln = (eval (first line))
                     :do (parsing-huh (typep ln '(integer 1 65535)) "LN" line) (setf p-lnum ln)
                     :unless (find ln lines :key #'car)
                       :collect (cons ln (rest line)) into lines
                     :finally
                        ;; Eliminate no-ops for the sake of tail-call-recursion detection.
                        (setf lines (delete-if (lambda (x) (or (null x) (streq (first (cdr x)) "REM"))) lines))
                        ;; Append implied END.
                        (push (cons 65536 '("END")) lines)
                        (return (sort lines #'< :key #'car))))
             (p-lbody (lbody &optional nbody)
               (destructuring-case (list* (make-keyword (string-upcase (first lbody))) (rest lbody))
                 ((:end) `((return-from bloop-prog t)))
                 ;; We fancy _optimizing_ compiler. We do tail-calls.
                 ((:gosub gexp) (if (and *tco* nbody (aand (first nbody) (or (streq it "RETURN") (streq it "END"))))
                                    `((rt-jump ,gexp) (go jump-table))
                                    `((rt-call ,gexp) (go jump-table))))
                 ((:goto gexp) `((rt-jump ,gexp) (go jump-table)))
                 ((:if exp thensym gexp) (parsing-huh (streq thensym "THEN") "TH")
                  `((when (rt-truep ',exp) (rt-jump ',gexp)  (go jump-table))))
                 ((:print &rest forms) `((rt-print ',forms)))
                 ((:return) `((rt-huh rstack "NG") (rt-jump (pop rstack)) (go jump-table)))
                 ((:let idexp eqsym exp)
                  (parsing-huh (streq eqsym "=") "EQ") `((let ((id (rt-id ',idexp))) (rt-set id (rt-eval ',exp)))))
                 ((t &rest rest) (declare (ignore rest)) (parsing-huh nil "??" lbody))))
             (parse-lines (sbody)
               (loop :for ((lnum . lbody) (nnum . nbody)) :on sbody ; Current, next lines
                     :append (when-let ((expansion (p-lbody lbody nbody))) `(,lnum ,@expansion)))))
      (setf scanned-lines (scan-lines outerbody)
            scanned-line-nums (map 'list #'first scanned-lines)
            parsed-lines (parse-lines scanned-lines))
      `(block bloop-prog
         (let* ((line-nums ',scanned-line-nums) ; Defined line numbers
                (rstack nil)                    ; Return stack
                (lnum 0))                       ; Current line number
           (labels (;; Run-time support
                    (rt-huh (test label &rest rest) (or test (if *break-on-huh* (break) (error "!~A@~D~{ ~A~}" label lnum rest))))
                    (rt-eval (x)
                      (acond
                        ((rt-id x nil) (symbol-value (or (find-symbol it) (rt-huh "ID" x))))
                        ((and (symbolp x) (boundp x)) (symbol-value x))
                        ((symbolp x) x)
                        (t (multiple-value-bind (v e) (ignore-errors (eval x)) (rt-huh (not e) "EX" e) v))))
                    (rt-call (lnexp) (rt-huh (< (length rstack) 10) "DP") (push (1+ lnum) rstack) (rt-jump lnexp))
                    (rt-jump (lnexp)
                      (let* ((ln (let ((r (rt-eval lnexp))) (rt-huh (typep r '(integer 1 65535)) "GO") r))
                             (targ (find ln line-nums :test #'<=)))
                        (setf lnum targ)))
                    (rt-truep (x) (let ((r (rt-eval x))) (typecase r (number (not (zerop r))) (string (not (emptyp r))) (t (when r t)))))
                    (rt-id (x &optional (err t)) (let* ((idstr (and (typep x '(or string symbol)) (string-upcase x)))
                                      (idlen (if idstr (length idstr) 0))
                                      (begOk (and (plusp idlen) (char<= #\A (aref idstr 0) #\Z)))
                                      (midOk (or (< idlen 3) (every (lambda (x) (char<= #\0 x #\9)) (subseq idstr 1 (1- idlen)))))
                                      (endOk (or (< idlen 2) (let ((c (aref idstr (1- idlen)))) (char= #\$ c) (char<= #\0 c #\9)))))
                                 (or (and begOk midOk endOk idstr) (and err (rt-huh nil "ID" x)))))
                    (rt-set (id val) (setf (symbol-value (ensure-symbol (string-upcase id))) val))
                    (rt-print (exprs)
                      (loop
                        :for prev-ctl = nil :then ctl
                        :for prev-val = nil :then (not ctl)
                        :for x in exprs
                        :for val = (rt-eval x)
                        :for ctl = (and (typep val 'symbol) (find (string x) '("%" "_") :test #'equal))
                        :unless (equal ctl "_")
                          :do (format t "~:[~; ~]~@[~{~A~}~]~:[~;~0,8T~]" (and prev-val (not ctl)) (unless ctl (list val)) (equal ctl "%"))
                        :finally (unless prev-ctl (terpri)))))
             (tagbody
                ,@parsed-lines
              jump-table
                (ecase lnum
                  ,@(map 'list (lambda (x) `(,x (go ,x))) scanned-line-nums)))))))))
