-- -- begin 
-- -- introv h₁ h₂ h₃,
-- -- split,
-- -- have h₄ : ¬Col b a c := equalanglesNC Point B A C b a c h₃,
-- -- have h₅ : ∃ U V u v, Out A B U ∧ Out A C V ∧ Out a b u ∧ Out a c v ∧ Cong A U a u ∧ Cong A V a v ∧ Cong U V u v ∧ ¬ Col B A C := h₃,
-- -- cases h₅ with U h₅,
-- -- cases h₅ with V h₅,
-- -- cases h₅ with u h₅,
-- -- cases h₅ with v h₅,
-- -- cases h₅ with h₅ h₆,
-- -- cases h₆ with h₆ h₇,
-- -- cases h₇ with h₇ h₈,
-- -- cases h₈ with h₈ h₉,
-- -- cases h₉ with h₉ h10,
-- -- cases h10 with h10 h11,
-- -- cases h11 with h11 h12,
-- -- have h13 : a ≠ b := ray2 Point a b u h₇,
-- -- have h14 : b ≠ a := neq_symm Point a b h13,
-- --         have h15: ¬ Col A B C,
-- --         intro h16,
-- --         have h17: Col B A C ∧ Col B C A ∧ Col C A B ∧ 
-- --         Col A C B ∧ Col C B A := collinearorder Point A B C h16,
-- --         cases h17 with h17 h18,
-- --         contradiction,
-- --       have h16: A ≠ B, 
-- --       intro h17,
-- --       have h2: Col A B C := or.inl h17,
-- --       contradiction,
-- --     have h17: A ≠ C,
-- --     intro h,
-- --     have h2: (A = C) ∨ (B = C) ∨ (BetS B A C) ∨
-- --      (BetS A B C) ∨ (BetS A C B) := or.inl h, 
-- --     have h3: Col A B C := or.inr h2,
-- --     contradiction,
-- --   have h18: C ≠ A := neq_symm Point A C h17,
-- --     have h19 : a ≠ c,
-- --     intro h,
-- --     have h2: (a = c) ∨ (BetS a b c) ∨ (BetS b a c) 
-- --     ∨ (BetS b c a) := or.inl h, 
-- --     have h3: (b = c) ∨ (a = c) ∨ (BetS a b c) ∨ 
-- --     (BetS b a c) ∨ (BetS b c a) := or.inr h2, 
-- --     have h3: Col b a c := or.inr h3,
-- --     contradiction,
-- --   have h20: c ≠ a := neq_symm Point a c h19,
-- --     have h21: b ≠ c,
-- --     intro h,
-- --     have h1: (b = c) ∨ (a = c) ∨ (BetS a b c) ∨ 
-- --     (BetS b a c) ∨ (BetS b c a) := or.inl h,
-- --     have h2 : Col b a c := or.inr h1,
-- --     contradiction,
-- --   have h22: c ≠ b := neq_symm Point b c h21,
-- --   have h23: BetS A U B ∨ eq B U ∨ BetS A B U := ray1 Point A B U h₅,
-- --     have h24: Cong B V b v,
-- --     cases h23 with h23 h24,
-- --     have h24: Cong A U A U := cn_congruencereflexive A U,
-- --     have h25:= and.intro h23 h24,
-- --     -- have h26: ∃ U, BetS A U B ∧ Cong A U A U := Lt h25,

-- -- --     -- BetS A U B ∧ Cong A U A U,



lemma proposition_04 : ∀ (A B C a b c : Point), Cong A B a b → Cong A C a c → CongA B A C b a c →
Cong B C b c ∧ CongA A B C a b c ∧ CongA A C B a c b := sorry

-- begin 
  -- rintros _ _ _ _ _ _ h₁ h₂ h₃, refine ⟨_,_,_⟩,
  -- have h₄:= equalanglesNC h₃,
  -- rcases h₃ with ⟨U, V, u, v, h11,_,h5⟩,
  -- have h₄:= ray2 h5.1,
  -- have h₅: ¬ Col A B C,
  --   {intro h, 
  --   rcases collinearorder h, 
  --   tauto},
  -- have h₆: A ≠ B, 
  --   {intro h, 
  --   have : Col A B C := or.inl h, 
  --   tauto},
  -- have h₇: A ≠ C,
  -- {intro h, 
  --   have : Col A B C := or.inr(or.inl h), 
  --   tauto},
  -- have h₈ : a ≠ c,
  --   intro h, have : Col b a c := or.inr(or.inr(or.inl h)), 
  --   tauto,
  -- have h₉ : b ≠ c,
  --   intro h, have : Col b a c := (or.inr(or.inl h)), 
  --   tauto,
  -- have h10: B ≠ C,
  --   intro h, have : Col B A C := (or.inr(or.inl h)), 
  --   tauto,
  -- rcases ray1 h11,
  -- have h12: Cong B V b v ,
  --   have h2:= cn_congruencereflexive A U,
  --   have: Lt _ _ _ _:=  ⟨ _ , h, h2⟩ ,
  --   rcases lt_cong _ _ _ _ _ _ this h₁ with ⟨_,h3,h4⟩,
  --   have:= h4.trans h5.2.2.1,
  --   rcases bet.neq _ _ _ h3 with ⟨_,h40⟩,
  --   have h30:= ray4 (or.inl(h3)) h₄,
  --   rcases congr_flip' this.symm with ⟨ h32, _⟩, 
  --   rcases congr_flip' h32 with ⟨ ⟩,
  --   have h20:= layoffunique _ _ _ _  h5.1 h30 left_1,
  --   subst' h20,
  --   rcases ray4 (or.inl(h3)) h₄ with ⟨V, h30⟩,
  --   have h36: Cong U B u b := differenceofparts h4.symm h₁ h h3,
  --   have: Cong V B v b := axiom_5_line _ _ V B _ _ v b ,

-- end 
--
lemma proposition_11b (A B C P : Point): BetS A C B → ¬Col A B P → ∃ X, 
Per A C X ∧ OS X A B P := sorry 

-- begin 
--   introv h1 h2, 
-- cases notperp h1 h2 with M h3,
-- --A ≠ B bet.neq
-- rcases proposition_12 _ _ _ h3.1 with ⟨Q, ⟨E, h4⟩⟩, 
--   have h5: M ≠ Q,
--   {
--     intro h,
--     subst h, 
--   tauto
--   },
-- have h6:= T8_2  h4.2.2.2, 
-- have h7: Col A B C := or.inr(or.inr(or.inr(or.inr(or.inr h1)))),
-- rcases ⟨collinearorder h4.2.2.1, collinearorder h7⟩ with ⟨⟨_,h8⟩,_,⟨_,h10⟩⟩,  
-- rcases bet.neq _ _ _ h1 with ⟨_, h11⟩,
-- have h12: C ≠ Q,
--   intro h, subst h,
--   have : Col A E C := collinear4 left left_1 h11.2.symm,
--   rcases collinearorder this with ⟨_, h2⟩ ,
--   have:= collinearright h4.2.2.2 h2.1 h11.1, tauto,
-- have h13: Col C Q E := collinear5 h11.2 h12 h7 h4.2.1 h4.2.2.1,
-- rcases collinearorder h13 with ⟨_, h14⟩ ,
-- have h15: Per C Q M := collinearright h4.2.2.2 h14.2.2.2 h12, 
-- cases proposition_10 _ _ h12.symm with G h16,
-- have h17: M ≠ G, 
--   intro h, subst h,
--   have h₁: Col Q M C := or.inr(or.inr(or.inr(or.inr(or.inl h16.1)))),
--   have h₂: Col B Q C := collinear4 h4.2.1 h7 h11.2,
--   rcases ⟨collinearorder h₁, collinearorder h₂⟩ with ⟨ ⟨ _,h₃⟩ , ⟨ _,h₄⟩ ⟩ ,
--   have h₅: Col C M B := collinear4 h₃.2.2.1 h₄.1 h12.symm,
--   cases collinearorder h₅ with h6 h7,
--   have h₈: Col B M A := collinear4 h7.2.2.1 h10.2.2 left_2,
--   cases collinearorder h₈, tauto,
-- cases postulate_extension _ _ _ _ h17 h17 with H h18, 
-- have h19 : Midpoint M G H := ⟨h18.1 , h18.2.symm⟩,
-- rcases congr_flip' h16.2 with ⟨_,_,h20⟩ , 
-- have h21 : Midpoint Q G C:= ⟨h16.1, right_left_1⟩,
-- have h22: Col Q G C :=  or.inr(or.inr(or.inr(or.inr(or.inl h16.1)))),
-- rcases ⟨collinearorder h22, bet.neq _ _ _ h16.1⟩ with ⟨⟨_,h23⟩ , h24⟩,
-- have h25: Per G Q M:= collinearright h15 h23.2.1 h24.2.1.symm,
-- cases postulate_extension _ _ _ _ h5 h5 with J h26,
-- have h27:= T8_2 h25,
-- have h28:= rightreverse h27 h26.1 h26.2.symm,
-- have h29:= axiom_betweennesssymmetry _ _ _ h26.1, 
-- rcases congr_flip' h26.2 with ⟨_,h30⟩, 
-- have h31: Per J Q G := ⟨ M, h29, h30.1, h28.symm, h24.2.1 ⟩ ,
-- have h32: J ≠ G,
--   intro h,
--    have h₁: Col J Q G := or.inr(or.inl h),
--    have h₂: ¬Col J Q G := rightangleNC h31,
--    tauto,
-- cases postulate_extension _ _ _ _ h32 h32 with K h33,
-- have h34 : Midpoint J G K:= ⟨h33.1, h33.2.symm⟩,
-- have h35:= pointreflectionisometry h34 h21,
-- have h36:= pointreflectionisometry h19 h21, 
-- have h37:= pointreflectionisometry h21 h19,
-- have h38:= pointreflectionisometry h21 h34,
-- have h39:= pointreflectionisometry h19 h34,
-- have h40: BetS H C K:= bet_preserved _ _ _ H C K h36 h39 h38 h26.1,
-- rcases ⟨congr_flip' h18.2 , congr_flip' h28⟩ with ⟨h41,h42⟩,
-- have h43:= h41.1.trans h42.2.1,
-- have h44:= h43.trans (h33.2.symm), 
-- rcases congr_flip' h44 with ⟨_, h45⟩ ,
-- assert (Cong H G K G) by (forward_using lemma_congruenceflip).
-- assert (neq G C) by (forward_using lemma_betweennotequal).
-- assert (Cong H C M Q) by (conclude lemma_congruencesymmetric).
-- assert (Cong M Q Q J) by (conclude lemma_congruencesymmetric).
-- assert (Cong H C Q J) by (conclude lemma_congruencetransitive).
-- assert (Cong H C C K) by (conclude lemma_congruencetransitive).
-- assert (Cong H C K C) by (forward_using lemma_congruenceflip).
-- assert (neq G C) by (forward_using lemma_betweennotequal).
-- assert (neq C G) by (conclude lemma_inequalitysymmetric).
-- assert (Per H C G) by (conclude_def Per ).
-- assert (Per G C H) by (conclude lemma_8_2).
-- assert (Col Q G C) by (conclude_def Col ).
-- assert (eq A A) by (conclude cn_equalityreflexive).
-- assert (Col A B A) by (conclude_def Col ).
-- assert (Col Q C A) by (conclude lemma_collinear5).
-- assert (Col Q C G) by (forward_using lemma_collinearorder).
-- assert (Col C A G) by (conclude lemma_collinear4).
-- assert (Col G C A) by (forward_using lemma_collinearorder).
-- assert (neq A C) by (forward_using lemma_betweennotequal).
-- assert (Per A C H) by (conclude lemma_collinearright).
-- assert (BetS H G M) by (conclude axiom_betweennesssymmetry).
-- assert (Col C A B) by (forward_using lemma_collinearorder).
-- assert (neq C A) by (conclude lemma_inequalitysymmetric).
-- assert (Col A G B) by (conclude lemma_collinear4).
-- assert (Col A B G) by (forward_using lemma_collinearorder).
-- assert (¬ Col A B H).
--  {
--  intro.
--  assert (Col B G H) by (conclude lemma_collinear4).
--  assert (Col M G H) by (conclude_def Col ).
--  assert (Col G H M) by (forward_using lemma_collinearorder).
--  assert (Col G H B) by (forward_using lemma_collinearorder).
--  assert (neq G H) by (forward_using lemma_betweennotequal).
--  assert (Col H M B) by (conclude lemma_collinear4).
--  assert (Col H B A) by (forward_using lemma_collinearorder).
--  assert (Col H B M) by (forward_using lemma_collinearorder).
--  assert (Col A B M).
--  by cases on (eq H B ∨ neq H B).
--  {
--   assert (BetS M G B) by (conclude cn_equalitysub).
--   assert (Col M G B) by (conclude_def Col ).
--   assert (Col G B M) by (forward_using lemma_collinearorder).
--   assert (Col G B A) by (forward_using lemma_collinearorder).
--   assert (neq G B) by (conclude cn_equalitysub).
--   assert (Col B M A) by (conclude lemma_collinear4).
--   assert (Col A B M) by (forward_using lemma_collinearorder).
--   close.
--   }
--  {
--   assert (Col B A M) by (conclude lemma_collinear4).
--   assert (Col A B M) by (forward_using lemma_collinearorder).
--   close.
--   }

--  contradict.
--  }
-- assert (TS H A B M) by (conclude_def TS ).
-- assert (OS P M A B) by (forward_using lemma_samesidesymmetric).
-- assert (TS M A B H) by (conclude_def TS ).
-- assert (TS P A B H) by (conclude lemma_planeseparation).
-- assert (TS H A B P) by (conclude lemma_oppositesidesymmetric).


-- import data.nat.basic


-- class euclidean_preneutral (Point : Type) :=
--   (Circle : Type)
--   (Cong : Point → Point → Point → Point → Prop)
--   (BetS : Point → Point → Point → Prop)
--   (CI : Circle → Point → Point → Point → Prop)
--   (cn_congruencetransitive : ∀ B C D E P Q, Cong P Q B C → Cong P Q D E → Cong B C D E)
--   (cn_congruencereflexive : ∀ A B, Cong A B A B)
--   (cn_equalityreverse : ∀ A B, Cong A B B A)
--   (cn_sumofparts : ∀ A B C a b c, Cong A B a b → Cong B C b c → BetS A B C → BetS a b c → Cong A C a c)
--   (cn_equalitysub : ∀ A B C D, D = A → BetS A B C → BetS D B C)
--   (circle : ∀ A B C, A ≠ B → ∃ X, CI X C A B) 
--   (axiom_betweennessidentity : ∀ A B, ¬ BetS A B A)
--   (axiom_betweennesssymmetry : ∀ A B C, BetS A B C → BetS C B A)
--   (axiom_innertransitivity :∀ A B C D, BetS A B D → BetS B C D → BetS A B C)
--   (axiom_connectivity : ∀ A B C D, BetS A B D → BetS A C D → ¬ BetS A B C → ¬ BetS A C B → eq B C)
--   (axiom_nocollapse : ∀ A B C D, A ≠ B → Cong A B C D → C ≠ D)
--   (axiom_5_line : ∀ A B C D a b c d, Cong B C b c → Cong A D a d → Cong B D b d 
--   → BetS A B C → BetS a b c → Cong A B a b → Cong D C d c)
--   (postulate_extension : ∀ A B C D, A ≠ B → C ≠ D → ∃ X, BetS A B X ∧ Cong B X C D)
--   (postulate_Euclid2 : ∀ A B, A ≠ B → exists X, BetS A B X)
--   (postulate_Euclid3 : ∀ A B, A ≠ B → exists X, CI X A A B)

-- namespace euclidean_preneutral
-- variables {Point : Type}
-- variable [euclidean_preneutral Point]

-- end euclidean_preneutral

-- open euclidean_preneutral

-- class euclidean_neutral (Point : Type) extends euclidean_preneutral Point := 

-- (axiom_nullsegment1 : ∀ A B C, Cong A B C C → A = B)
-- (axiom_nullsegment2 : ∀ A B, Cong A A B B) 

-- section 
import data.nat.basic 

-- class euclidean_preneutral (Point : Type) :=
--   (Circle : Type)
--   (Cong : Point → Point → Point → Point → Prop)
--   (BetS : Point → Point → Point → Prop)
--   (CI : Circle → Point → Point → Point → Prop)
--   (cn_congruencetransitive : ∀ B C D E P Q, Cong P Q B C → Cong P Q D E → Cong B C D E)
--   (cn_congruencereflexive : ∀ A B, Cong A B A B)
--   (cn_equalityreverse : ∀ A B, Cong A B B A)
--   (cn_sumofparts : ∀ A B C a b c, Cong A B a b → Cong B C b c → BetS A B C → BetS a b c → Cong A C a c)
--   (cn_equalitysub : ∀ A B C D, D = A → BetS A B C → BetS D B C)
--   (circle : ∀ A B C, A ≠ B → ∃ X, CI X C A B) 

-- namespace euclidean_preneutral
-- variables {Point : Type} 
-- variable [euclidean_preneutral Point]

-- end euclidean_preneutral

-- open euclidean_preneutral

class euclidean_neutral (Point : Type) := 
  (Circle : Type)
  (Cong : Point → Point → Point → Point → Prop)
  (BetS : Point → Point → Point → Prop)
  (axiom_betweennessidentity : ∀ A B, ¬ BetS A B A)
  (axiom_betweennesssymmetry : ∀ A B C, BetS A B C → BetS C B A)
  (axiom_innertransitivity :∀ A B C D, BetS A B D → BetS B C D → BetS A B C)
 
namespace euclidean_neutral
section 

variables {Point : Type} 
variable [euclidean_neutral Point]

variables x y z : Point 
variables C D E : euclidean_neutral.Circle Point 

lemma T3_6a : ∀ (A B C D : Point), BetS A B C → BetS A C D → BetS B C D := 

  begin
  introv h₁ h₂,
  rcases ⟨axiom_betweennesssymmetry _ _ _ h₁, axiom_betweennesssymmetry _ _ _ h₂⟩,
  use ⟨ axiom_innertransitivity _ _ _ _ ⟩,
  have h₃:= axiom_betweennesssymmetry A B C h₁, 
  have h₄:= axiom_betweennesssymmetry A C D h₂,
  have h₅:= axiom_innertransitivity D C B A h₄ h₃,
  use [axiom_betweennesssymmetry _ _ _ h₅],
  end



-- BEGIN 
-- section Basic Lemmas

-- variables p q : Prop

-- lemma andFalseElimRight : ¬(p ∧ q) → (p → ¬q) :=
--     assume (LHS : ¬(p ∧ q)) (Hp: p),
--     (λ (Hq: q), LHS (and.intro Hp Hq))


-- lemma andFalseElimLeft : ¬(p ∧ q) → (q → ¬p) :=
--     assume (LHS : ¬(p ∧ q)) (Hq: q),
--     (λ (Hp: p), LHS (and.intro Hp Hq))


-- lemma andFalseIntroLeft : ¬p → ¬(p ∧ q) :=
--     assume (LHS : ¬p),
--     (λ Hnpq: (p ∧ q), LHS (and.elim_left Hnpq))


-- lemma andFalseIntroRight : ¬p → ¬(q ∧ p) :=
--     assume (LHS : ¬p),
--     (λ Hnpq: (q ∧ p), LHS (and.elim_right Hnpq))

-- open classical

-- lemma deMorganAndLeft : ¬(p ∧ q) → (¬p ∨ ¬q) :=
--   assume LHS : ¬(p ∧ q),
--   or.elim (classical.em p) --why won't it run with just em? is there a conflict in the library?
--     (λ Hp: p, or.intro_right (¬p) (andFalseElimRight p q LHS Hp))
--     (λ Hp: (¬p), or.intro_left (¬q) Hp)


-- lemma deMorganAndRight : (¬p ∨ ¬q) → ¬(p ∧ q) :=
--   assume LHS : (¬p ∨ ¬q),
--   or.elim LHS (andFalseIntroLeft p q) (andFalseIntroRight q p)


-- theorem deMorganAnd (p : Prop) (q: Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := sorry 

-- lemma deMorganRight : (¬p ∨ ¬q) → ¬(p ∧ q) :=
--   assume LHS : (¬p ∨ ¬q),
--   or.elim LHS (andFalseIntroLeft p q) (andFalseIntroRight q p)




--- draft tarski to euclid 


     
      have HPU: Bet U P P := between_trivial U P,
      have:= between_inner_transitivity _ _ _ _ (between_symmetry _ _ _ HRPV),
      have:= outer_transitivity_between _ _ _ _ HRPV,
      --exact outer_transitivity_between _ _ _ _  HRPV HPVX HNE6.2.1,
      use HRSQ,--contradiction,
      cases bet.neq _ _ _ HBet, exact ne.symm HNE4.1,
      apply col_permutation_5, apply bet_col, assumption, cleanup,
      apply col_permutation_5, apply bet_col, apply between_symmetry, assumption, 
       unfold Col at HNC, simp [Col], cleanup_hyps, cleanup, constructor, 
        
       apply between_identity,
      apply col_transitivity_2,
      have : Bet P U I,
        have : Col P U I,
        cases bet.neq _ _ _ HBet,
        simp [Col], cleanup,
        exfalso,
        have HFalse: OS Q S P U,
        apply one_side_transitivity _ _ _ R _,
      -- split, split, split, tauto!, split,
      -- tauto!,
          rw l9_19 _ _ _ _ Q, cleanup,
          apply bet_out, cleanup,  apply right.1,
     
        
      -- have HFalse: TS Q S P U,
      --       {refine ⟨by assumption,_⟩, split, 
      --       intro heq,
      --       have HQU: Q = U, 
      --       {apply l6_21 S Q R Q, 
      --       apply par_strict_not_col_1 _ _ _ P,
      --        exact par_strict_comm _ _ _ _ HPar, 
      --        any_goals { try {cleanup,},
      --        }, apply col_permutation_2,
      --         apply bet_col,
      --         exact between_symmetry _ _ _ HQUR,
      --       }, tauto!, use I, refine ⟨by assumption,by assumption⟩ ,},
      --       replace HFalse:= l9_9 _ _ _ _ HFalse, 
      --       apply HFalse,
      --       apply one_side_transitivity _ _ _ R,
      --       {exact l12_6 _ _ _ _ HPar},
      --       rw l9_19 Q, refine ⟨⟨ne.symm HNE10.2.2,ne.symm HNE10.2.1,_⟩,_⟩ , right, 
      --       assumption,


   
      -- apply out_sym,
      -- rw← l6_2,
      -- exact HPUY, tauto!,
      -- apply out_trivial,
      -- split,
      -- apply bet_out, exact HNE6.2.1, exact between_symmetry _ _ _ HRPV,
      -- cleanup, cleanup,
      -- apply par_strict_not_col_1 _ _ _ P,
      -- have : OS P R I U,
      --   apply one_side_transitivity _ _ _ Q,
      --   apply l12_6,
      --   apply par_strict_right_comm,
      --   apply par_strict_col_par_strict _ _ _ S, 
      --   intro,  subst_vars, cleanup_hyps, 
      --   apply HNC, cleanup,
      -- split,
      -- suffices : Bet I Q S,
      -- exact between_symmetry _ _ _ this,
      -- have HTS: TS Q R S I,
      -- apply l9_8_2 _ _ P _ _, 
      --   split, cleanup,
      --   split,
      --   apply par_not_col_strict P,
      -- apply par_strict_not_col_2 S, apply par_strict_left_comm, assumption,
      -- split, apply not_col_permutation_2,apply par_strict_not_col_2 S,
      -- apply par_strict_col_par_strict _ _ _ P _,
      -- intro heq, subst I,
      -- have:=  not_col_permutation_2 _ _ _ (par_strict_not_col_4 _ _ _ _ HPar), contradiction,
      -- apply par_strict_comm _ _ _ _ HPar,
      -- by_contradiction,
      -- have: R = P, apply l6_21, use h,
      -- have:= NCdistinct h, cleanup, cleanup, use this.2.2.1, cleanup, cleanup, cleanup,
      -- apply col_permutation_2, 
    
      




      -- have HPUI : Bet P U I,
      -- have HNC1: ¬ Col X Q S, 
      -- { apply par_strict_not_col_2 _,
      -- apply par_strict_symmetry,
      -- apply par_strict_col_par_strict _ _ _ R _, exact HNE6.2.2,
      -- tauto!, apply col_permutation_4, apply bet_col,
      -- exact outer_transitivity_between _ _ _ _  HRPV HPVX HNE6.2.1,},
      -- have : Q = U, 
      --   {apply l6_21 S Q R Q, 
      --     apply par_strict_not_col_1 S, 
      --     exact par_strict_comm _ _ _ _ HPar, 
      --     tauto!, 
      --     cleanup, cleanup,
          
      --     -- tauto!, tauto!,}, 
         
      --   },
      -- have: Q = Y, {apply l6_21 Q S X Q,
      -- cleanup, 
      -- cleanup, cleanup, cleanup, cleanup, 
      -- exact bet_col _ _ _ HXQY,},
      -- have : R = U,
      --     {
      --      apply l6_21 P R Q U,
      --     apply par_strict_not_col_1 S, },
      -- have : Q = U, 
      --   {apply l6_21 S Q R Q, 
      --     apply par_strict_not_col_2 S, 
      --     exact par_strict_left_comm _ _ _ _ HPar, 
      --     tauto!, 
      --     cleanup, cleanup,
      --     -- tauto!,
      --     -- tauto!, tauto!,}, 
         
      --   },
        
        
        
        
        
      -- have HTS: TS Q R S I,
      -- apply l9_8_2 _ _ P _ _, 
      -- repeat {split,},
      -- have:= par_strict_not_col_1 _ _ _ _ 
      -- (par_strict_symmetry _ _ _ _ HPar), cleanup, cleanup,
      -- tauto!,
      --        exact par_strict_comm _ _ _ _ HPar, 
      -- have HFalse := HTS,
      -- by_cases Bet P U I, cleanup, 
      -- apply between_symmetry,
      -- by_cases Bet I Q S, cleanup, exfalso,
      --  have HPUI: Col P U I,
        -- { exfalso,
        -- have HNPUI: ¬ Bet P I U,
        --   { intro heq,
        --   have HFalse: TS Q S P U,
        --     {refine ⟨by assumption,_⟩, split, 
        --     intro heq,
        --     have HQU: Q = U, 
        --     {apply l6_21 S Q R Q, 
        --     apply par_strict_not_col_1 _ _ _ P,
        --      exact par_strict_comm _ _ _ _ HPar, 
        --      any_goals { try {cleanup,},
        --      }, apply col_permutation_2,
        --       apply bet_col,
        --       exact between_symmetry _ _ _ HQUR,
        --     }, tauto!, use I, refine ⟨by cleanup,by assumption⟩ ,} ,
            -- have HFalse2:= l9_9 _ _ _ _ HFalse,
            -- apply HFalse2,
            -- apply one_side_transitivity _ _ _ R _ ,
            -- {apply l12_6, assumption,}, 
            -- repeat {split,}, 
            -- apply not_col_permutation_3, 
            -- apply par_strict_not_col_1 _ _ _ P,
            --  exact par_strict_comm _ _ _ _ HPar,
            --  apply not_col_permutation_3, 
            -- apply par_strict_not_col_1 _ _ _ P,
            --  exact par_strict_comm _ _ _ _ HPar, apply col_trivial_1,
            --  have HFalse: TS P R I U,
            --  split,  apply not_col_permutation_4, apply par_strict_not_col_1 _ _ _ S,
            --   {split, 
            -- intro heq,
            -- have HRU: R = U, 
            --  {apply l6_21 P R Q U, 
            -- apply par_strict_not_col_1 _ _ _ S,
            --  exact par_strict_comm _ _ _ _ HPar, 
            --  any_goals { try {cleanup,},
            --  }, apply col_permutation_2,
            --   apply bet_col,
            --   exact between_symmetry _ _ _ HQUR,
            -- }},
               
              
            --    {apply l6_21 P R Q U, 
            -- apply par_strict_not_col_1 _ _ _ S,
            --  exact par_strict_comm _ _ _ _ HPar, 
             
            
            
            
            
         
      -- by_cases Bet S Q I, tauto!,
      -- split, 
      -- have HFalse: TS Q S P U,
      --       refine ⟨by assumption,_⟩, split, 
      --         have HQU: Q = U, 
      --         apply l6_21 S Q R Q, 
      --         apply par_strict_not_col_1 _ _ _ P,
      --         exact par_strict_comm _ _ _ _ HPar, 
      --   -- --       tauto!, cleanup,
      --         any_goals {try {cleanup,},},
              -- apply col_transitivity_1,
        --       apply  HNE4.2.1, cleanup, cleanup,
        --       apply col_permutation_2,
        --       apply bet_col,
        --       exact between_symmetry _ _ _ HQUR,
        --       tauto!, use I, use ( HCol), 



      -- by_contradiction,
      -- clear Hc1, clear Hc2, 
      -- have:= par_strict_not_col_2 _ _ _ _
      --  (((par_strict_comm _ _ _ _ HPar))),

      --   have HQU: Q = U, 
      --       {apply l6_21 Q R P Q, tauto, tauto, cleanup,
      --       -- apply par_strict_not_col_1 _ _ _ P,
      --       --  exact par_strict_comm _ _ _ _ HPar, 
      --       --  any_goals { try {cleanup,},
      --         apply col_permutation_2,
      --         apply bet_col,
      --         exact between_symmetry _ _ _ HQUR, cleanup,
      --         have:= outer_transitivity_between,--here 
      --         apply col_transitivity_1,
      --         have HNE12:= bet.neq _ _ _ HPTQ,
      --         use (ne.symm HNE12.2.1),
      --         apply col_permutation_1,
      --         apply bet_col , 
      --         exact between_symmetry _ _ _ HPTQ,
      --       },-- tauto!, use I, refine ⟨by assumption,by assumption⟩ ,},
      -- have HFalse : TS P R I U,
      -- split, apply par_strict_not_col_2, apply par_strict_symmetry,
      --  apply par_strict_col_par_strict _ _ _ _ _, intro,
 
      
      -- rcases HCol, subst Q, use I,cleanup, 
      -- have : Q = Y,
      -- {apply l6_21 Q P R Q,
      -- cleanup, 
      
      -- cleanup, cleanup, cleanup, simp [Col], cleanup, constructor,
      -- apply l6_21, apply HNC,
      -- exact bet_col _ _ _ HXQY,},
      -- have:= par_strict_not_col_2 _ _ _ _
      --  ((par_strict_symmetry _ _ _ _ HPar)),
      -- -- par_strict_not_col_2 _ _ _ _ HPar, -- split,
      -- apply between_trivial,
      -- have: Bet P U I,
      --   have : Col P U I, exfalso,
      --     have HFalse: TS I S P U,
      --       refine ⟨by assumption,_⟩, split, 
      --       intro heq,
      --       have HQU: I = U, 
      --       {apply l6_21 S I R U, 
      --       apply par_strict_not_col_1 _ _ _ P,
      --        exact par_strict_comm _ _ _ _ HPar, 
      --        any_goals { try {cleanup,},
      --        }, 
      --         apply bet_col,exact between_symmetry _ _ _ HQUR,},
      --         tauto!,  use I, cleanup, 
      --         have : U = Y,
      --           apply l6_21,
      --           apply par_strict_not_col_2 S, 
      --           exact par_strict_right_comm _ _ _ _ HPar,
                
              --exact between_symmetry _ _ _ HQUR,
            -- }, tauto!, use I, use HCol, 
            






        -- have HPUI: Col P U I,
        -- apply col_transitivity_1, use HNE7.2.2, 
        -- have HPUY:= bet_col _ _ _ HPUY, cleanup,
        -- have HBet:= bet_col _ _ _ HBet, cleanup, 
        -- exfalso,
        --  have HFalse: TS Q S P U,
        -- --     refine ⟨by assumption,_⟩, split, 
        --       have HQU: Q = U, 
        --       apply l6_21 S Q R Q, 
        --       apply par_strict_not_col_1 _ _ _ P,
        --       exact par_strict_comm _ _ _ _ HPar, 
        -- --       tauto!, cleanup,
        --       any_goals {try {cleanup,},},
        --       apply col_transitivity_1,
        --       apply  HNE4.2.1, cleanup, cleanup,
        --       apply col_permutation_2,
        --       apply bet_col,
        --       exact between_symmetry _ _ _ HQUR,
        --       tauto!, use I, use ( HCol), 

        -- by_contradiction,
      --   exfalso,
          -- exfalso,
          -- have HFalse: TS Q S P U,
          -- refine ⟨by assumption,_⟩, split,
          -- intro heq,
           

      --       exfalso,
      --        have HFalse: TS Q S P U,
      --       refine ⟨by assumption,_⟩, split, 
      --       intro heq,
      --       have HQU: Q = U, 
      --       apply l6_21 S Q R Q, 
      --       apply par_strict_not_col_1 _ _ _ P,
      --        exact par_strict_comm _ _ _ _ HPar, 
      --        any_goals {try {cleanup,},}
      --        , apply col_permutation_2,
      --         apply bet_col,
              -- exact between_symmetry _ _ _ HQUR,
            -- have: Col P U I,  refine ⟨by assumption,by assumption⟩ ,},
            -- replace HFalse:= l9_9 _ _ _ _ HFalse, 
            -- apply HFalse,
            -- apply one_side_transitivity _ _ _ R,
            -- {exact l12_6 _ _ _ _ HPar},
            -- rw l9_19 Q, refine ⟨⟨ne.symm HNE10.2.2,ne.symm HNE10.2.1,_⟩,_⟩ , right, 
            -- assumption, 
            -- apply par_strict_not_col_1 _ _ _ P,
            -- exact par_strict_right_comm _ _ _ _ HPar, 
            -- tauto!, cleanup,
            -- apply bet_col,
            -- exact between_symmetry _ _ _ HQUR, }, 
            
            -- have HFalse : TS P R I U,

            -- { unfold TS,
            -- split,
            --   -- apply l6_21, 
            --   apply par_strict_not_col_1 _ _ _ _ ,  
            --    apply par_strict_symmetry, assumption, tauto!,
            --    cleanup, simp [Col], right,left, 
            --    apply l6_21 , 
            --     apply par_strict_not_col_2 S, 
            --   exact par_strict_left_comm _ _ _ _ HPar, 
            --     tauto!, cleanup,

               
            --    replace h:= col_permutation_2 _ _ _ h,
            --    have:= col_permutation_5 _ _ _ (bet_col _ _ _ HRPV),
            --   apply bet_col, 
            --   apply outer_transitivity_between, 
            --   use between_symmetry _ _ _ HQUR,
            --     -- exact outer_transitivity_between _ _ _ _  HRPV HPVX HNE6.2.1,

--  have HPUI: Bet P U I,
--       {
--         have HPUI: Col P U I,
--         { exfalso,
--         have HNPUI: ¬ Bet P I U,
--           { intro heq,
--           have HFalse: TS Q S P U,
--             {refine ⟨by assumption,_⟩, split, 
--             intro heq,
--             have HQU: Q = U, 
--             {apply l6_21 S Q R Q, 
--             apply par_strict_not_col_1 _ _ _ P,
--              exact par_strict_comm _ _ _ _ HPar, 
--              any_goals { try {cleanup,},
--              }, apply col_permutation_2,
--               apply bet_col,
--               exact between_symmetry _ _ _ HQUR,
--             }, tauto!, use I, refine ⟨by assumption,by assumption⟩ ,},
--             replace HFalse:= l9_9 _ _ _ _ HFalse, 
--             apply HFalse,
--             apply one_side_transitivity _ _ _ R,
--             {exact l12_6 _ _ _ _ HPar},
--             rw l9_19 Q, refine ⟨⟨ne.symm HNE10.2.2,ne.symm HNE10.2.1,_⟩,_⟩ , right, 
--             assumption, 
--             apply par_strict_not_col_1 _ _ _ P,
--             exact par_strict_right_comm _ _ _ _ HPar, 
--             tauto!, cleanup,
--             apply bet_col,
--             exact between_symmetry _ _ _ HQUR, }, 
--             have HFalse : TS P R I U,

            -- }

            -- use (ne.symm HNE10.2.2 ), tauto!,
            -- -- exact (between_symmetry H)
         

         
  --           -- have HPI: P = I,
  --           -- { apply l6_21 S Q R Q, 
  --           -- apply par_strict_not_col_1 _ _ _ P,
  --           --  exact par_strict_comm _ _ _ _ HPar, 
  --           --  any_goals { try {cleanup,},
  --           --  },tauto!,},
           
  --           have:= col_permutation_2 _ _ _ (bet_col _ _ _ heq),
  --           exfalso, have:= outer_transitivity_between _ _ _ _ heq,  
  --           -- have:= 
            
            
  --             apply between_equality_2, -- _ _ _ (between_symmetry _ _ _ heq),
  --           exact between_equality _ _ _  heq,
  --           apply between_symmetry,
  --           apply between_exchange3 , exact heq, 
  --           apply between_exchange2,
  --           have:= between_inner_transitivity _ _ _ _ heq,
  --           have := between_exchange4 _ _ _ _ HBet,
  --           -- apply between_symmetry,
  --           cleanup,

  --           -- apply outer_transitivity_between2,
            
            
          
        
      
    -- have HNE9 := bet.neq _ _ _ HBet,
    -- have HSQI: Bet S Q I,
  
    -- constructor,
    
    -- induction HCol, subst Q, apply between_trivial,
    -- by_contradiction,
    -- induction HCol, subst S, intro heq,
    
    -- suffices: Col S Q I, 
    -- clear Hc1, clear Hc2, use I, 
    -- by_cases Bet S Q I,
    -- split, assumption,


    -- split,
    -- have HTS : TS Q R S I,
    -- apply l9_8_2 _ _ P _,
    -- unfold TS,
    -- split, 
    -- apply not_col_permutation_4,
    -- apply par_strict_not_col_2 S, apply par_strict_left_comm, assumption,
    -- split, apply not_col_permutation_2,apply par_strict_not_col_2 S,
    -- apply par_strict_col_par_strict _ _ _ P _,
    -- intro heq, subst I,
    -- have:=  not_col_permutation_2 _ _ _ (par_strict_not_col_4 _ _ _ _ HPar), contradiction,
    -- apply par_strict_comm _ _ _ _ HPar,
    -- by_contradiction,
    -- have: R = P, apply l6_21, use h,
    -- have:= NCdistinct h, cleanup, cleanup, use this.2.2.1, cleanup, cleanup, cleanup,
    -- apply col_permutation_2, 
   
    -- intro heq, subst_vars, exact HNE6.2.2,
    
    
    -- apply par_strict_not_col_4 ,
    -- replace HPar:= par_strict_not_col_4 _ _ _ _ HPar,
    -- apply between_symmetry, 
    -- unfold Col at HCol,
    --   apply l9_8_2 _ _ P _, split,
    --    apply par_strict_not_col_2, apply par_strict_left_comm,-- tauto!,
    
    
    
    --  apply between_symmetry, unfold Col at HCol,
    -- cases_type* or, cleanup, cleanup,
    -- unfold Col at HCol,


    -- have HQU: Q = U, apply l6_21 Q P R Q, 
    -- apply par_strict_not_col_2 S, apply par_strict_left_comm, tauto!,
    -- replace HPar:= par_strict_distinct _ _ _ _ HPar, tauto!, cleanup, cleanup,
    -- cleanup, cleanup, apply col_permutation_2, exact bet_col _ _ _  HQUR, tauto!,
    -- use Q, cleanup,  apply l12_6, apply par_strict_right_comm,
    -- apply par_strict_col_par_strict _ _ _ R, tauto!, tauto!,
    -- apply col_permutation_4, 
    -- apply bet_col, 
    -- exact outer_transitivity_between _ _ _ _  HRPV HPVX HNE6.2.1,
    -- have : Q = U,
    -- apply l6_21 S Q R Q, 
    -- split, 
    -- unfold Col at HCol,--tauto!,
    -- cleanup,
    -- have HTS : TS Q R S I,
    -- apply l9_8_2 _ _ P _ _,
    -- split, 

    
    
      
      
    
    -- have := outer_transitivity_between _ _ _ _  HBet,
    -- apply between_exchange4 _ _ _ _  HPUY, 
      
    -- suffices: ¬  tauto!, apply between_equality, 
    -- exact between_symmetry _ HXQY,
    -- apply l4_19,
    -- apply cong_identity,
    -- apply outer_transitivity_between, apply between_inner_transitivity refine ⟨ by tauto!, by tauto!, _,_⟩ ,
    -- apply col__coplanar,
    -- --assumption, unfold Col, simp*,
    -- left,
    -- replace HPar:= par_strict_distinct _ _ _ _ HPar,
    -- by_contradiction,
    -- suffices : P = R, tauto!,
    -- unfold Par_strict at *, 
    -- have NCPerm:= NCol_perm _ _ _ HNC, 
    -- exfalso,
    -- have:= coplanar_perm_3 _ _ _ _ (coplanar_trivial Q S P),
    -- cases this with x,
    -- unfold Coplanar at *, apply HPar.2.2.2, use P, constructor, 
    -- unfold Col at *, simp*,
    
    -- exact Col_perm _ _ _ this_h.1,
    -- apply NCPerm.2.2.2.1,

    
    --  simp [Col], 
    -- left, exfalso,
    -- cleanup,
    -- rcases HPar with ⟨HP1, HP2, HP3, HP4⟩ , 
    --  apply HP4, use P, constructor, unfold Coplanar at HP3,
    --  have NCPerm:= NCol_perm _ _ _ HNC, 
    --  simp [Col] at *, simp*, repeat { rw not_or_distrib at NCPerm ,}, cleanup, 
    -- suffices HCol: ¬ Coplanar Q S P R, 
    -- have NCPerm:= NCol_perm _ _ _ HNC, tauto!, 
    -- apply  col__coplanar,
    -- intro heq,
    -- apply bet_col, --apply HNC, simp [Col] at *,
    -- unfold Coplanar,

  
--- signed area


-- (** This is Euclid Book I, Prop 35 *)
-- Lemma parallelograms_same_base :
--  forall A B C D E F,
--  Plg A B C D ->
--  Plg E B C F ->
--  Col A E F ->
--  Col D E F ->
--  signed_area4 A B C D =F= signed_area4 E B C F.
-- Proof.
-- intros.
-- unfold signed_area4.
-- convert_to_algebra.
-- decompose_coordinates; intros; spliter.
-- *)


-- (*
-- (** This is Euclid Book I, Prop 36 *)
-- Lemma parallelograms_equal_bases :
--  forall A B C D E F G H,
--  A<>B ->
--  B<>C ->
--  E<>F ->
--  F<>G ->
--  Parallelogram A B C D ->
--  Parallelogram E F G H ->
--  Cong B C F G ->
--  Col A E H ->
--  Col D E H ->
--  signed_area4 A B C D =F= signed_area4 E F G H.
-- Proof.
-- intros.
-- apply plg_par in H4;[idtac|auto|auto].
-- apply plg_par in H5;[idtac|auto|auto].
-- spliter.
-- revert H4 H10 H5 H9 H6 H7 H9.
-- setoid_rewrite characterization_of_parallelism_F.
-- setoid_rewrite characterization_of_collinearity_F.
-- setoid_rewrite characterization_of_congruence_F.
-- unfold signed_area4, signed_area, cross_product.
-- decompose_coordinates;simpl.
-- intros;spliter.
-- put_negs_in_goal;
-- express_disj_as_a_single_poly.
-- right.
-- right.
-- right.
-- right.
-- nsatz.
-- setoid_rewrite characterization_of_parallelism_F.
-- *)

-- (** This is Euclid Book I, Prop 37 *)

-- Lemma triangles_same_base :
--  forall A B C D,
--  Par A D B C ->
--  signed_area A B C =F= signed_area D B C.
-- Proof.
-- intros A B C D.
-- unfold signed_area.
-- setoid_rewrite characterization_of_parallelism_F.
-- decompose_coordinates;simpl.
-- unfold cross_product;simpl.
-- intros.
-- spliter.
-- nsatz.
-- Qed.

-- (*
-- (** This is Euclid Book I, Prop 38 *)
-- Lemma triangles_equal_bases :
--  forall A B C D E F,
--  Par A D B C ->
--  Col B C E ->
--  Col B C F ->
--  Cong B C E F ->
--  signed_area A B C =F= signed_area D E F.
-- Proof.
-- intros A B C D E F.
-- unfold signed_area.
-- setoid_rewrite characterization_of_parallelism_F.
-- setoid_rewrite characterization_of_collinearity_F.
-- setoid_rewrite characterization_of_congruence_F.
-- decompose_coordinates;simpl.
-- unfold cross_product;simpl.
-- intros;spliter.
-- put_negs_in_goal;
-- express_disj_as_a_single_poly.
-- *)

-- (*
-- (** This is Euclid Book I, Prop 39 *)
-- Lemma triangle_equal_parallel:
--  forall A B C D,
--  signed_area A B C =F= signed_area D B C ->
--  OS B C A D ->
--  Par A D B C.
-- Proof.
-- *)



end 
end euclidean_neutral 