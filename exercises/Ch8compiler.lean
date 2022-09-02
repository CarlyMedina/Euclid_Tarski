
import data.nat.basic
import data.nat.pow 
import data.bool.basic 
import init.logic


#check nat

namespace hidden

open function

#print surjective

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}



lemma surjective_comp {g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) :
surjective (g ∘ f) := 
begin
  assume x,
  have h, from hg x,
  cases h with b hb,
  have ha, from hf b,
  cases ha with a ha,
  rw [← ha] at hb,
  exact exists.intro a hb,

end

namespace hidden

inductive nat : Type
| zero : nat
| succ : nat → nat

open nat

def add : nat → nat → nat
| m zero     := m
| m (succ n) := succ (add m n) 

def add' (m : nat) : nat → nat
| zero     := m
| (succ n) := (succ n)

local infix ` + ` := add

def mul : nat → nat → nat
| n zero     := zero
| n (succ m) := mul n m + n


local infix ` × ` := mul

def pow (m: nat) : nat → nat → nat
|n zero := succ zero
|m (succ n):= n 

local infixr ` ^ `:= pow  

end hidden

namespace hidden2
def list_add : list nat → list nat → list nat
| []       _        := []
| _        []       := []
| (a :: l) (b :: m) := (a + b) :: list_add l m


def append {α : Type*} : list α → list α → list α 
| []     l := l
| (h::t) l := h :: append t l

#eval append [1, 2, 3] [4, 5, 6]

def reverse {α : Type*} : list α → list α 
| [] := [] 
| (a::l) := append (reverse l) [a]

#eval reverse [1]
#eval reverse (reverse [1, 2, 3])


reverse l++m by induction on m
[]++ m
proof by induction
-- def fib (n : nat) : nat → nat := 
-- begin 
-- | 0 ()  := 1 --???
-- | 1  ()   := 1
-- | (n+2) := fib (n+1) + fib n

-- end

end hidden2

def vector (α : Type u) (n : ℕ) := { l : list α // l.length = n }

def append'' {n m : nat} (v : vector α n) (w : vector α m) :
 --(append v w) =





--define well_founded.fix 
 

end vector 
end nat
end hidden

