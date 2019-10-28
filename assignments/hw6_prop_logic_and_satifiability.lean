namespace prop_logic

/-
This assignment has five problems. The first
is to extend our propositional logic syntax
and semantics to support the three additional
connectives, exclusive or (⊕), implies (which 
we will write as ⇒), and if and only iff (↔).
We first give you the definitions developed
in class. You are to extend/modify them to
support expressions with the new connectives.
The remaining problems use this definition of
our language of expressions in propositional
logic.  
-/


/-
1. Extend our syntax and semantics
for propositional logic to support
the xor, implies, and iff and only
iff connectives/operators.

A. Add support for the exclusive or
connective/operator. Define the symbol, 
⊕, as an infix notation.

Here are specific steps to take for the
exclusive or connective, as an example.

1. Add new binary connective, xorOp
2. Add pXor as shorthand for binOpExp xorOp
3. Add ⊕ as an infix notation for pXor
4. Specify the interpretation of ⊕ to be bxor
5. Extend interpBinOp to handle the new case 

Then add support for the implies connective,
using the symbol, ⇒, as an infix operator.
We can't use → because it's reserved by Lean
and cannot be overloaded. Lean does not have 
a Boolean implies operator (analogous to bor),
so you will have to define one. Call it bimpl.

Finally add support for if and only iff. Use
the symbol ↔ as an infix notation. You will
have to define a Boolean function as Lean 
does not provide one for iff. Call it biff.

Here is the code as developed in class.
Now review the step-by-step instructions,
and proceed to read and midify this logic
as required. We've bracketed areas where
new material will have to be added. 
-/

/-    *** SYNTAX ***    -/

inductive var : Type 
| mkVar : ℕ → var

inductive unOp : Type
| notOp

inductive binOp : Type
| andOp
| orOp
| xorOp
| implOp
| iffOp


inductive pExp : Type
| litExp : bool → pExp
| varExp : var → pExp
| unOpExp : unOp → pExp → pExp
| binOpExp : binOp → pExp → pExp → pExp

open var
open pExp
open unOp
open binOp

-- Shorthand notations
def pTrue := litExp tt
def pFalse := litExp ff
def pNot := unOpExp notOp
def pAnd := binOpExp andOp
def pOr := binOpExp orOp
def pXor := binOpExp xorOp
def pImpl := binOpExp implOp
def pIff := binOpExp iffOp

-- conventional notation

notation e1 ∧ e2 :=  pAnd e1 e2
notation e1 ∨ e2 :=  pOr e1 e2
notation ¬ e := pNot e
notation e1 ⊕ e2 := pXor e1 e2
notation e1 ⇒ e2 := pImpl e1 e2
notation e1 ↔ e2 := pIff e1 e2

/-
    *****************
    *** SEMANTICS ***
    *****************
-/

def interpUnOp : unOp → (bool → bool) 
| notOp := bnot

def bimpl: bool → bool → bool
| tt tt:= tt
| tt ff:= ff
| ff tt:= tt
| ff ff:= tt

def  biff: bool → bool → bool
| tt tt:= tt
| tt ff:= ff
| ff tt:= ff
| ff ff:= tt

def interpBinOp : binOp → (bool → bool → bool) 
| andOp := band
| orOp := bor
| xorOp := bxor
| implOp := bimpl
| iffOp := biff

/-  *** SEMANTICS ***   -/


/-
Given a pExp and an interpretation
for the variables, compute and return
the Boolean value of the expression.
-/
def pEval : pExp → (var → bool) → bool 
| (litExp b) i := b
| (varExp v) i := i v
| (unOpExp op e) i := 
    (interpUnOp op) (pEval e i)
| (binOpExp op e1 e2) i := 
     (interpBinOp op)
        (pEval e1 i) 
        (pEval e2 i)


/-
Note: You are free to use pEval, if you
wish to, to check answers to some of the
questions below. It is not mandatory and
you will not be marked down for not doing
this.
-/

/-
#2. Define X, Y, and Z to be variable
expressions bound to a different variable
expression terms. Hint: Look at the
prop_logic_test.lean file to remind
yourself how we did this in class.
-/

def X : pExp := varExp (mkVar 0)
def Y : pExp := varExp (mkVar 1)
def Z : pExp := varExp (mkVar 2)


/-
#3. Here are some English language 
sentences that you are to re-express
in propositional logic. Here's one
example.
-/

/-
EXAMPLE:

Formalize the following proposition,
as a formula in propositional logic:
If it's raining then it's raining.
-/

-- Use R to represent "it's raining"
def R : pExp := varExp (mkVar 4)

-- Solution here
def p1 : pExp := pImpl R R


/-
Explanation: We first choose to represent
the smaller proposition, "it's raining", 
by the variable expression, R. We then
formalize the overall natural language
expression, if R then R, as the formula,
R ⇒ R.

Note: R ⇒ R can be pronounced as any of:
- if R is true then R is true 
- if R then R
- the truth of R implies the truth of R
- R implies R  

The second and fourth pronounciations
are the two that we prefer to use. 
-/

/-
For the remaining problems, use the 
variables expressions, X, Y, and Z, 
as already defined. Use parentheses
if needed to group sub-expressions.
-/

/-
A.

If it's raining and the streets are
wet then it's raining.
-/

def p2 : pExp := (X ∧ Y) ⇒ X

/-
B. If it's raining and the streets
are wet, then the streets are wet
and it's raining. 
-/

def p3 := (X ∧ Y) ⇒ (Y ∧ X)

/-
C. If it's raining then if the
streets are wet then it's raining
and the streets are wet.
-/
def p4 := X ⇒ (Y ⇒ (X ∧ Y))

/-
D. If it's raining then it's
raining or the moon is made of
green cheese.
-/
def p5 := X ⇒ (X ∨ Z)

/-
E. If it's raining, then if it's
raining implies that the streets 
are wet, then the streets are wet.
-/
def p6 := X ⇒ ((X ⇒ Y) ⇒ Y)


/-
#4. For each of the propositional
logic expressions below, write a truth
table and based on your result, state
whether the expression is unsatisfiable,
satisfiable but not valid, or valid. 

Here's an example solution for the
expression, (X ∧ Y) ⇒ Y.

X   Y   X ∧ Y   (X ∧ Y) ⇒ Y
-   -   -----   -----------
T   T   T       T
T   F   F       T
F   T   F       T
F   F   F       T
The proposition is valid.
-/

/-
A. After each "#check" give your 
answer for the specified proposition.
That is, write a truth table in a
comment and then say whether given the
proposition is valid, satisfiable but
not valid, or unsatisifiable. 

Note: This expression reqires that 
you  have properly specified ¬ and
⇒ as notations in our pExp language.
The errors indicated in many of the
following lines will go away once 
you have these notations properly
defined.
-/

#check (X ⇒ Y) ⇒ (¬ X ⇒ ¬ Y)

/-
X   Y   ¬X  ¬Y  X⇒Y  ¬X⇒¬Y  (X⇒Y)⇒(¬X⇒¬Y)
-   -   --  --  ---  -----  -------------
T   T   F   F   T    T      T
T   F   F   T   F    T      T
F   T   T   F   T    F      F
F   F   T   T   T    T      T
The proposition is satisfiable but not valid
-/


/-
B.
-/

#check ((X ⇒ Y) ∧ (Y ⇒ X)) ⇒ (X ⇒ Z)

/-
X  Y  Z  X⇒Y  Y⇒X  (X⇒Y)∧(Y⇒X)  (X⇒Z)  ((X⇒Y)∧(Y⇒X))⇒(X⇒Z)
-  -  -  ---  ---  -----------  -----  -------------------
T  T  T  T    T    T            T      T
T  T  F  T    T    T            F      F
T  F  T  F    T    F            T      T
T  F  F  F    T    F            F      T
F  T  T  T    F    F            T      T
F  T  F  T    F    F            T      T
F  F  T  T    T    T            T      T
F  F  F  T    T    T            T      T
The proposition is satisfiable but not valid
-/

/-
C.
-/

#check pFalse ⇒ (X ∧ ¬ X)

/-
pFalse  X  ¬X  X∧¬X  pFalse⇒(X∧¬X)
------  -  --  ----  -------------
F       T  F   F     T
F       F  T   F     T
The proposition is valid
-/


/-
D.
-/

#check pTrue ⇒ (X ∧ ¬ X)

/-
pTrue  X  ¬X  X∧¬X  pTrue⇒(X∧¬X)
------  -  --  ----  -------------
T       T  F   F     F
T       F  T   F     F
The proposition is unsatisifiable
-/


/-
E.
-/

#check (X ∨ Y) ∧ X ⇒ ¬ Y

/-
X  Y  ¬Y  X∨Y  (X∨Y)∧X  (X∨Y)∧X⇒¬Y
-  -  --  ---  -------  ----------
T  T  F   T    T        F
T  F  T   T    T        T
F  T  F   T    F        T
F  F  T   F    F        T
The proposition is satisfiable but not valid
-/


/-
#5. 

A. Find and present an interpretation
that causes the following proposition
to be satisfied (to evaluate to true).

(X ∨ Y) ∧ (¬ Y ∨ Z)


Answer:
 Let X be True, Y be True and Z be True. Then X ∨ Y is True and 
 ¬ Y ∨ Z is also True. It follows that (X ∨ Y) ∧ (¬ Y ∨ Z) is True. 


B. Count and state how many of the
possible interpretations satisfy the
formula.

Answer:
X  Y  Z  X∨Y  ¬Y  ¬Y∨Z  (X∨Y)∧(¬Y∨Z)
-  -  -  ---  --  ----  ------------
T  T  T  T    F   T     T
T  T  F  T    F   F     F
T  F  T  T    T   T     T
T  F  F  T    T   T     T
F  T  T  T    F   T     T
F  T  F  T    F   F     F
F  F  T  F    T   T     F
F  F  F  F    T   T     F
There are 4 interpretations satisfying the formula.
-/



end prop_logic

