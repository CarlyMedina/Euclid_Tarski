-- define band, bor, bnot, and verifying common identities 
namespace hidden

def band (b1 b2 : bool) : bool :=
bool.cases_on b1 ff b2

def bor (b1 b2 : bool) : bool := 
bool.cases_on b1 tt b2 

def bnot (b : bool) : bool :=
bool.cases_on b tt ff

end hidden

-- develop a notion of composition for α to β and β to γ, show it behaves as expected
namespace hidden


 def comp (α β γ : Type*) (f: α → option β) (g: β → option γ) (x : α) :
option γ := option.cases_on (f x) option.none g

 def comp' (α β γ : Type*) (f: α → option β) (g: β → option γ) (x : α) :
option γ := 
match (f x) with
| option.none     := option.none 
| (option.some b) := g b
end

end hidden 

-- define multiplication on the natural numbers 
namespace nat 

def add (m n : nat) : nat :=
nat.rec_on n m (λ n add_m_n, succ add_m_n)

def prod_nat ( m n : ℕ × ℕ) : ℕ := 
prod.cases_on m (λ m n, m * n)

#reduce prod_nat (4,6)


end nat 





-- Define an inductive data type consisting of terms built up from the following constructors:

-- const n, a constant denoting the natural number n
-- var n, a variable, numbered n
-- plus s t, denoting the sum of s and t
-- times s t, denoting the product of s and t

namespace hidden

inductive nat : Type
| zero : nat
| succ : nat → nat
-- BEGIN
namespace nat



end nat
-- END

end hidden

-- const n, a constant denoting the natural number n
-- var n, a variable, numbered n : asst n con
-- plus s t, denoting the sum of s and t
-- times s t, denoting the product of s and t


-- Recursively define a function that evaluates any such term with respect 
-- to an assignment of values to the variables.







-- Similarly, define the type of propositional 
-- formulas, as well as functions on the type 
-- of such formulas: an evaluation function, 
-- functions that measure the complexity of a 
-- formula, and a function that substitutes 
-- another formula for a given variable.

-- Simulate the mutual inductive definition 
-- of even and odd described in Section 7.9 
-- with an ordinary inductive type, using an 
-- index to encode the choice between them in 
-- the target type.


-- define boolean operators (band, bor, bnot) & verifying common identities 


-- namespace hidden

-- show that bool & nat are inhabited, the product of two
-- inhabited types is inhabited, and that the type of functions
-- to an inhabited type is inhabited 