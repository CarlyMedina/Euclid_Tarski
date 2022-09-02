def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := λ x : α, λ y : β

def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ := 
 (λ x : α) (f α)  

def do_twice : (ℕ → ℕ) → ℕ → ℕ :=
  λ f x, f (f x)

def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) :=
