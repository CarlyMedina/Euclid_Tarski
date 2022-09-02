import data.nat.basic



namespace hidden
-- use equation compiler 
--define addition on nat num


--define exponentiation on nat num





-- derive some of their basic properties 



end hidden 


open function

#print surjective

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

example : (nat × bool) := (1, true)
example : (nat × bool) → nat :=
begin
  intro p,


end

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
 

def reverse : list α → list α :=
λ l, reverse_core l []


-- -- define using eq compiler and prove theorems 
-- about lists by induction such 
-- as the fact that reverse(reverse 1)=1
-- --  for any list 1 

append ? 

cons ?
-- --  use equation compiler
--  to define reverse function
--   (like reverse function)

-- --  and prove theorems 
-- about lists by induction such 
-- as the fact that reverse(reverse 1)=1
-- --  for any list 1 




--define fxn that appends 2 vectors 