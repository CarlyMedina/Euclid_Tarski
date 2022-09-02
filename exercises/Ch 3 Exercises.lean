



variables p q r : Prop
#check nat
#check nat → (nat → nat)
#check nat → nat → nat
#check (nat → nat) → nat
#check bool → bool
def f : nat → nat → nat :=
  λ n m, n + m

def f' : (nat × nat) → nat :=
  λ ⟨n, m⟩ , n + m
#check f 1





-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=  
  iff.intro 
  (assume h : p ∧ q,
    have hp : p, from h.left,
    have hq : q, from h.right,
    show q ∧ p, from and.intro hq hp)
  (assume h: q ∧ p,
    have hq : q, from h.left,
    have hp : p, from h.right, 
    show p ∧ q, from (and.intro hp) hq )

example : p ∨ q ↔ q ∨ p := 
  iff.intro 
  (assume h : p ∨ q, 
  or.elim h
    (assume hp :p,\
      show q ∨ p, from or.inr hp)
    (assume hq:q, 
    show q ∨ p, from or.inl hq))
  (assume h : q ∨ p, 
  or.elim h
    (assume hq :q,
      show p ∨ q, from or.inr hq)
    (assume hp:p, 
    show p ∨ q, from or.inl hp))  

example : p ∨ q ↔ q ∨ p := 
⟨ λ h, or.elim h or.inr or.inl, λ h, or.elim h or.inr or.inl ⟩ 

/-   
   show p ∨ q, from or.inr    
    (assume hp : p,
    show p ∨ q, from or.inl 
    (assume h : q ∨ p,
    or.elim h 
    (assume hq : q,
    show q ∨ p, from or.inl
    (assume hp : p, 
    show q ∨ p, from or.inl)))))
    -/

  
  
-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
begin
-- apply iff.intro,
--   intro h, 
--   apply or.elim (and.right h),
--   intro hq,
--   apply or.inr, 
--   apply and.intro,
--   exact and.left (h),
--   have hp, from (and.left h),
--   have hqr, from (and.right h),
--   apply or.elim hqr,

end 

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
-- iff.intro 
--   (assume h : p → (q → r),
--     assume (hpq : p ∧ q), 
--     have hp:p, from and.left hpq,
--     have hq:q, from and.right hpq,
--     show r, from h hp hq )
--   (assume h : p ∧ q → r,
--     (assume hp,
--     assume hq,
--     have hpq: p ∧ q, from and.intro hp hq,
--     show r, from h hpq))
begin

example : (p → (q → r)) ↔ (p ∧ q → r) := 
iff.intro 
  (assume h : p → (q → r),
    assume (hpq : p ∧ q), 
    show r, from h (and.left hpq) (and.right hpq) )
  (assume h : p ∧ q → r,
    (assume hp,
    assume hq,
    have hpq: p ∧ q, from and.intro hp hq,
    show r, from h hpq))

example : (p → (q → r)) ↔ (p ∧ q → r) := 
iff.intro 
  (λ h hpq, h hpq.left hpq.right)
  (λ h hp hq, _)
--  (λ h hp hq,
--    have hpq: p ∧ q, from and.intro hp hq,
--    show r, from h hpq))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
begin
apply iff.intro, 
  intro h1,
  split,
  intro h2,
  have h3: p∨q, from or.inl h2,
  exact h1 h3,
  intro h2,
  have h3: p∨q, from (or.inr h2),
  exact h1 h3,
  intro h,
  have h2:= and.left h, 
  have h3:= and.right h,
  intro h4,
  apply or.elim h4,
  exact h2,
  exact h3,
end 


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := 
begin
intros h hp,
have h1, from hp.right,
have h2, from hp.left,
apply or.elim h,
by contradiction,
by contradiction,
end

example : ¬(p ∧ ¬p) := 
begin
  intro hnp, have hp, from hnp.left, have hnnp, from hnp.right,
  by contradiction,
end


example : p ∧ ¬q → ¬(p → q) := 
begin
intros hpnq hpq,
cases hpnq with h1 h2,
apply h2 (hpq h1),
apply hpq,
assumption,
have h1: p, from hpnq.left, 
have h2: ¬q, from hpnq.right, --other ways for have???? 
have hq: q, from hpq h1,
exact h2 hq,
end 


example : ¬p → (p → q) := 
begin
intros hnp hp,
by contradiction,
end

example (P : ℕ → Prop) (h1 : ∃ x, P x) : true :=
begin
  cases h1 with z hz,
end

example : p ∨ false ↔ p := 
begin
  apply iff.intro,
  { intro h,
    cases h with h1 h1,
    assumption, contradiction },
--    apply or.elim h,
--    intro h1,
--    exact h1,
--    intro h1,
--    by contradiction,
   intro h1,
    have h2:= p ∨ false, from or.inl h1
end 


example : (¬p ∨ q) → (p → q) := 
begin
intros h1 h2,
have h3: p ∨ q, from or.inl h2,
apply or.elim h1, 
intro h4,
by contradiction,
intro h4,
exact h4,
end 





example : p ∧ false ↔ false := 
begin 
split,
intro h,
show false, from h.right,
assume h,
constructor, 
by contradiction, 
exact h, 
end 

example : (p → q) → (¬q → ¬p) :=
begin 
intros hpq hnq prop,
have q, from hpq prop, 
exact hnq q, 
end 