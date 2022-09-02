


variables (α : Type*) (p q : α → Prop)

 example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
begin
apply iff.intro,
  intro h,
  apply and.intro,
  intro α,
  have h3:= h α,
  exact and.left h3,
  intro α,
  have h2: p α ∧ q α := h α,
  exact and.right h2,
  intros h α,
  split,
  have h3:= and.left h,
  exact h3 α,
  have h4:= and.right h,
  exact h4 α,

  -- intro α,
  -- have h4:= h α,
  -- exact and.right h4,
  -- intro h,
  -- intro α,
  -- split,
  -- have h5:= q α,
  -- have h2,
end 

example (a b c d e : nat) (h1 :a =b ) (h2 :c =b ) (h3: d =c) : a = d :=
begin
  rw [h1, ← h2, h3],
end

--  iff.intro

  -- (assume h : ∀ x, p x ∧ q x,
  -- have h₂: ∀ x, p x, from 
  --   assume y, 
  --   have h₃: p y ∧ q y, from h y,
  --   show p y, from and.elim_left h₃,

  -- have h₃: ∀ x, q x, from 
  --   assume y,
  --   have h₄ : p y ∧ q y, from h y, 
  --   show q y, from and.elim_right h₄,
  -- show (∀ x, p x) ∧ (∀ x, q x), from and.intro h₂ h₃)
  -- (assume h: (∀ x, p x) ∧ (∀ x, q x),
  --   have h₂: (∀ x, p x), from and.elim_left h,
  --   have h₃: (∀ x, q x), from and.elim_right h, 
  --   assume y,
  --   have h₄: p y, from h₂ y, 
  --   have h₅: q y, from h₃ y,
  --   show p y ∧ q y, from and.intro h₄ h₅)


  

example (a b c d : nat) (h1 : a = b) (h₂ : c = d) : a + c = b + d :=
begin
  rw h1,
  rw h₂,
end
#check nat.add


example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
begin 
  intro h,
  cases h with hp hq, 
  { intro y,
    have h1, from hp y,
    exact or.inl h1 },
  intro y,
  have h2, from hq y,
  exact or.inr h2
end 

   
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
begin 
  intro h, 
  intro h2,
  intro y, 
  have h3 := h2 y,
  have h4:= h y, 
  apply h4 h3, 
end 


--variables (α : Type*) (p q : α → Prop)
variable r : Prop


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
  begin
    apply iff.intro,
      {intro h, 
      intro h2,
      intro h3,
      have h4:= h h3,
      have h5:= h4 h2,
      exact h5,},
      
      { intro h, 
        intro h2, 
        intro h3, 
        have h4:= h h3,
        have h5:= h4 h2,
        exact h5,
      }
  end 


variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : 
false := 
begin
  have h5 := h barber,
    cases h5 with h6 h7,
  have h1: ¬ shaves barber barber,
  { intro h3,
    
    apply h6 h3,
    exact h3, },
  have h2: shaves barber barber,
  { 
    apply h7 h1,  },
  apply h1,
  exact h2,
     
/-  have h2, from shaves barber, 
  have h1, from men,
  have h3, from barber, 
  have h4, from h h3,
  cases h4 with h5 h6, 
-/  
  
end 



