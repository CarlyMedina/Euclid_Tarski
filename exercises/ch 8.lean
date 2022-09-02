import data.nat.basic 
open function

#print surjective

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
open function

lemma surjective_comp {g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) :
surjective (g ∘ f) := 
begin
  assume y,
  simp,
  
  


end


variables p q : ℕ → Prop

example : (∃ x, p x) → (∃ y, q y) →
  ∃ x y, p x ∧ q y
| ⟨x1, hx1⟩ ⟨x2, hx2⟩ := ⟨x1, x2, hx1, hx2⟩

example : (∀ x, ∃ y, p x ∧ q y) → (∀ x, ∃y, q y ∧ p x) :=
assume h x, 
match h x with 
| ⟨y, px, qy⟩ := ⟨y, qy, px⟩ 
end 

example {g : β → γ} (h : surjective g) (y : γ) : true :=
match h y with
| ⟨x, hx⟩ := 