import data.nat.basic
import tactic.interactive
import tactic.basic
import init.default
import data.dlist 
import tactic.core
import init.data.subtype.basic init.funext
import init.logic

-- attribute ne @[reducible]

-- variables {a b c d : Prop}
  class euclidean_preneutral (Point : Type) :=
  (Circle : Type)
  (Cong : Point → Point → Point → Point → Prop)
  (BetS : Point → Point → Point → Prop)
  (CI : Circle → Point → Point → Point → Prop)
  (cn_congruencetransitive : ∀ B C D E P Q, Cong P Q B C → Cong P Q D E → Cong B C D E)
  (cn_congruencereflexive : ∀ A B, Cong A B A B)
  (cn_equalityreverse : ∀ A B, Cong A B B A)
  (cn_sumofparts : ∀ A B C a b c, Cong A B a b → Cong B C b c → BetS A B C → BetS a b c → Cong A C a c)
  (cn_equalitysub : ∀ A B C D, D = A → BetS A B C → BetS D B C)
  (circle : ∀ A B C, A ≠ B → ∃ X, CI X C A B) 
  (axiom_betweennessidentity : ∀ A B, ¬ BetS A B A)
  (axiom_betweennesssymmetry : ∀ A B C, BetS A B C → BetS C B A)
  (axiom_innertransitivity :∀ A B C D, BetS A B D → BetS B C D → BetS A B C)
  (axiom_connectivity : ∀ A B C D, BetS A B D → BetS A C D → ¬ BetS A B C → ¬ BetS A C B → eq B C)
  (axiom_nocollapse : ∀ A B C D, A ≠ B → Cong A B C D → C ≠ D)
  (axiom_5_line : ∀ A B C D a b c d, Cong B C b c → Cong A D a d → Cong B D b d 
  → BetS A B C → BetS a b c → Cong A B a b → Cong D C d c) --variant of Hilbert's SAS criterion for triangle congruence
  (postulate_extension : ∀ A B C D, A ≠ B → C ≠ D → ∃ X, BetS A B X ∧ Cong B X C D)
  (postulate_Euclid2 : ∀ A B, A ≠ B → exists X, BetS A B X)
  (postulate_Euclid3 : ∀ A B, A ≠ B → exists X, CI X A A B)

namespace euclidean_preneutral
variables {Point : Type}
variable [euclidean_preneutral Point]

def Col (A B C : Point) := ((A = B) ∨ (A = C) ∨ (B = C) ∨ (BetS B A C) ∨ (BetS A B C) ∨ (BetS A C B))
 
def OnCirc (B : Point) (J : Circle Point) := ∃ X Y U, CI J U X Y ∧ Cong U B X Y

def InCirc (P : Point) (J : Circle Point) := ∃ X Y U V W, CI J U V W ∧ (eq P U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U P U Y)) 

def OutCirc (P : Point) (J : Circle Point) := ∃ X U V W, CI J U V W ∧ BetS U X P ∧ Cong U X V W

def Equilateral (A B C : Point) := (Cong A B B C) ∧ (Cong B C C A)

def Triangle (A B C : Point) := ¬ Col A B C
/-- Point C lies on Ray AB -/
def Out (A B C : Point) := ∃ X, BetS X A C ∧ BetS X A B 
/-- Segment AB is less than CD  -/
def Lt (A B C D : Point) := ∃ X, BetS C X D ∧ Cong C X A B 
/-- B is the midpoint of AC -/
def Midpoint (A B C : Point) := BetS A B C ∧ Cong A B B C 
/--  Angle ABC is equal to angle abc -/
def CongA (A B C a b c : Point) := ∃ U V u v, Out B A U ∧ Out B C V ∧ Out b a u 
∧ Out b c v ∧ Cong B U b u ∧ Cong B V b v ∧ Cong U V u v ∧ ¬ Col A B C   
/-- DBF is a supplement of ABC  -/
def Supp (A B C D F : Point) := Out B C D ∧ BetS A B F 
/-- ABC is a right angle -/
def Per (A B C : Point) := ∃ X, BetS A B X ∧ Cong A B X B ∧ Cong A C X C ∧ B ≠ C 
/-- PQ is perpendicular to AB at C and ¬ColABP -/
def Perp_at (P Q A B C : Point) := ∃ X, Col P Q C ∧ Col A B C ∧ Col A B X ∧ Per X C P 
/-- PQ is perpendicular to AB -/
def Perp (P Q A B : Point) := ∃ X, Perp_at P Q A B X 
/-- P is in the interior of angle ABC -/
def InAngle (A B C P : Point) := ∃ X Y, Out B A X ∧ Out B C Y ∧ BetS X P Y 
/-- TS in GH (P and Q are on opposite sides of AB) -/
def OS (P A B Q : Point) := ∃ X, BetS P X Q ∧ Col A B X ∧ ¬ Col A B P 
/-- P and Q are on the same side of AB -/
def SS (P Q A B : Point) := ∃ X U V, Col A B U ∧ Col A B V ∧ BetS P U X ∧ BetS Q V X ∧ ¬ Col A B P ∧ ¬ Col A B Q
/-- ABC is isosceles with base BC  -/
def isosceles (A B C : Point) := Triangle A B C ∧ Cong A B A C 
/-- AB cuts CD in E -/
def Cut (A B C D E : Point) := BetS A E B ∧ BetS C E D ∧ ¬ Col A B C ∧ ¬ Col A B D 
/-- Triangle ABC is congruent to Triangle abc -/
def Cong_3 (A B C a b c : Point) := Cong A B a b ∧ Cong A C a c ∧ Cong B C b c 
/-- Angle ABC is less than angle DEF -/
def LtA (A B C D E F : Point) := ∃ U X V, BetS U X V ∧ Out E D U ∧ Out E F V ∧ CongA A B C D E X 
/-- AB and CD are together greater than EF -/
def TG (A B C D E F : Point) := ∃ X, BetS A B X ∧ Cong B X C D ∧ Lt E F A X 
/-- AB, CD are together greater than EF, GH  -/
def TT (A B C D E F G H : Point) := ∃ X, BetS E F X ∧ Cong F X G H ∧ TG A B C D E X 
/-- ABC and DEF together make two right angles -/
def RT (A B C D E F : Point) := ∃ X Y Z U V, Supp X Y U V Z ∧ CongA A B C X Y U ∧ CongA D E F V Y Z 
/-- AB meets CD  -/
def Meet (A B C D : Point) := ∃ X, A ≠ B ∧ C ≠ D ∧ Col A B X ∧ Col C D X 
/-- A B crossed C D -/
def CR (A B C D : Point) := ∃ X, BetS A X B ∧ BetS C X D 
/-- AB and CD are Tarski parallel -/
def TP (A B C D : Point) := A ≠ B ∧ C ≠ D ∧ ¬ Meet A B C D ∧ SS C D A B 
/-- AB and CD are parallel -/
def Par (A B C D : Point) := ∃ U V u v X, A ≠ B ∧ C ≠ D ∧ Col A B U ∧ 
  Col A B V ∧ U ≠ V ∧ Col C D u ∧ Col C D v ∧ u ≠ v ∧
 ¬ Meet A B C D ∧ BetS U X v ∧ BetS u X V 
/-- ABC and DEF are together equal to PQR -/
def SumA (A B C D E F P Q R : Point) := ∃ X, CongA A B C P Q X ∧ CongA D E F X Q R ∧ BetS P X R 
/-- ABCD is a parallelogram -/
def PG (A B C D : Point) := Par A B C D ∧ Par A D B C 
/-- ABCD is a square -/
def SQ (A B C D : Point) := Cong A B C D ∧ Cong A B B C ∧ Cong A B D A ∧ Per D A B ∧ Per A B C ∧ Per B C D ∧ Per C D A 
/--  ABCD is a rectangle -/
def RE (A B C D : Point) := Per D A B ∧ Per A B C ∧ Per B C D ∧ Per C D A ∧ CR A C B D 
/-- ABCD and abcd are congruent rectangles -/
def RC (A B C D a b c d : Point):= RE A B C D ∧ RE a b c d ∧ Cong A B a b ∧ Cong B C b c 
/-- ABCD and abcd are equal rectangles -/
def ER (A B C D a b c d : Point) := ∃ X Y Z U x z u w W, RC A B C D X Y Z U ∧ RC a b c d x Y z u ∧ BetS x Y Z ∧ BetS X Y z ∧ BetS W U w 


end euclidean_preneutral

open euclidean_preneutral

 
class euclidean_neutral (Point : Type) extends euclidean_preneutral Point := 

(axiom_nullsegment1 : ∀ A B C, Cong A B C C → A = B)
(axiom_nullsegment2 : ∀ A B, Cong A A B B) 

(postulate_Pasch_inner : ∀ A B C P Q, BetS A P C → BetS B Q C → ¬ Col A C B → ∃ X, BetS A X Q ∧ BetS B X P)

(postulate_Pasch_outer : ∀ A B C P Q, BetS A P C → BetS B C Q → ¬ Col B Q A → ∃ X, BetS A X Q ∧ BetS B P X)

open euclidean_neutral 

section 

variables {Point : Type} 
variable [euclidean_neutral Point]

variables x y z : Point 
variables C D E : euclidean_preneutral.Circle Point 

--namespace euclidean_preneutral
--namespace Cong

lemma euclidean_preneutral.Cong.symm {A B C D : Point} : Cong B C A D → Cong A D B C := 
begin 
  rintros h₁,
  use [cn_congruencetransitive _ _ _ _ _ _ h₁ (cn_congruencereflexive B C)],
end 

lemma euclidean_preneutral.Cong.trans {A B C D E F : Point}:
Cong A B C D → Cong C D E F → Cong A B E F := 
  begin
  rintros h₁ h₂,
  use [cn_congruencetransitive _ _ _ _ _ _ h₁.symm h₂],
  end 

lemma euclidean_preneutral.Cong.flipL {A B C D : Point} : Cong A B C D → Cong B A C D  := 
  
  begin
    rintros h1,
    use (h1.symm.trans (cn_equalityreverse A B)).symm,
  end 

lemma euclidean_preneutral.Cong.flipR {A B C D : Point} : Cong A B C D → Cong A B D C  := 
  begin 
  rintros h1,
    use (h1.trans (cn_equalityreverse C D)),
  end 

lemma euclidean_preneutral.Cong.flipLR {A B C D : Point} : Cong A B C D → Cong B A D C :=
  begin
  rintros h1,
  use (cn_equalityreverse B A).trans (h1.trans (cn_equalityreverse C D)),
  end 

lemma euclidean_preneutral.Cong.reverse {A B C D : Point} : Cong A B C D → Cong D C B A := sorry


-- end Cong
-- end euclidean_preneutral

section
variables U V W X : Point
variable h : Cong U V W X
variable h' : Cong W X U X

end


/--Triangle ABC is congruent to Triangle ABC -/
lemma Tcongr_refl {A B C : Point} : Triangle A B C → Cong_3 A B C A B C := 
begin
  rintros h₁,
  use ⟨cn_congruencereflexive _ _, cn_congruencereflexive _ _, cn_congruencereflexive _ _⟩,
end 

lemma lt_cong2 {A B C D E F : Point}: Lt A B C D → Cong A B E F → Lt E F C D := 
begin
  rintros ⟨G, h₃⟩ h₂, 
  use [G, h₃.1, h₃.2.trans h₂],
end 

lemma bet.neq {A B C : Point}: BetS A B C → B ≠ C ∧ A ≠ B ∧ A ≠ C := 
  begin
    rintros h₁,
    refine ⟨ _ , _, _⟩ ,
    repeat {
      intro hEq,
      subst hEq, 
      },
    have := axiom_innertransitivity _ _ _ _ (axiom_betweennesssymmetry _ _ _ h₁)(axiom_betweennesssymmetry _ _ _ h₁),
    have := axiom_betweennessidentity _ _, 
    contradiction, 
    have := axiom_innertransitivity _ _ _ _ h₁ h₁,
    have := axiom_betweennessidentity _ _,
    contradiction,
    have := axiom_betweennessidentity _ _,
    contradiction,
end 

--namespace euclidean_preneutral
--namespace TG


  lemma euclidean_preneutral.TG.symm {A B C a b c : Point} :
   TG A a B b C c → TG B b A a C c := sorry 
   

  lemma euclidean_preneutral.TG.flip {A B C a b c : Point} : TG A a B b C c →
   TG a A B b C c ∧ TG A a B b c C := sorry 
-- 



-- end TG
-- end euclidean_preneutral

section

variables R S T r s t : Point
variable h : TG r R T t S s
variable h' : TG R r S s t T

end

lemma TTorder { A B C D E F G H : Point}:
   TT A B C D E F G H → TT C D A B E F G H :=sorry
  
lemma TTtransitive {A B C D E F G H P Q R S : Point}:
   TT A B C D E F G H → TT E F G H P Q R S → TT A B C D P Q R S := sorry 

lemma TTflip {A B C D E F G H : Point}: TT A B C D E F G H →
   TT B A D C E F G H := sorry 

lemma TTflip2 {A B C D E F G H : Point}:
   TT A B C D E F G H → TT A B C D H G F E := sorry 

lemma extensionunique {A B E F : Point}:
BetS A B E → BetS A B F → Cong B E B F → E = F := 
  begin
  rintros h1 h2 h3, 
  use [axiom_nullsegment1 _ _ _ ((axiom_5_line _ _ _ _ _ _ _ _ h3 (cn_congruencereflexive A E) (cn_congruencereflexive B E) h1 h2 (cn_congruencereflexive A B)).symm)],
  end 

lemma T3_6a {A B C D : Point}: BetS A B C → BetS A C D → BetS B C D := 
  begin
  rintros h₁ h₂,
  rcases ⟨axiom_betweennesssymmetry _ _ _ h₂, axiom_betweennesssymmetry _ _ _ h₁⟩ with ⟨h₃,h₄⟩,
  simp [axiom_betweennesssymmetry _ _ _ (axiom_innertransitivity _ _ _ _ h₃ (h₄))],
  end


lemma T3_7a { A B C D : Point } : BetS A B C → BetS B C D → BetS A C D := 

begin
  rintros h₁ h₂,
  rcases ⟨bet.neq h₁, bet.neq h₂, postulate_extension _ _ _ _ h₃.2.2 h₄.1⟩ with ⟨h₃, h₄, E, h₅⟩,
  have h6:= extensionunique h₂ (T3_6a h₁ h₅.1) h₅.2.symm, 
  subst (h6), tauto,
end 

lemma T3_7b {A B C D : Point} : BetS A B C → BetS B C D → BetS A B D := 

  begin 
  rintros h₁ h₂,
  rcases ⟨axiom_betweennesssymmetry _ _ _ h₁, axiom_betweennesssymmetry _ _ _ h₂⟩ with ⟨h₄,h₅⟩ ,
  use (axiom_betweennesssymmetry _ _ _ (T3_7a h₅ h₄)),
  end 

lemma T3_5b {A B C D : Point}: BetS A B D →  BetS B C D →
   BetS A C D := 
  begin
  rintros h₁ h₂,
  use [T3_7a (axiom_innertransitivity _ _ _ _ h₁ (h₂)) h₂],
  end 


lemma T3_6b {A B C D : Point}: BetS A B C → BetS A C D → BetS A B D := 
begin
  rintros h₁ h₂,
  use [axiom_betweennesssymmetry _ _ _ (T3_5b (axiom_betweennesssymmetry _ _ _ h₂) (axiom_betweennesssymmetry _ _ _ h₁))] ,

end 

lemma null3 {A B C D : Point}: A ≠ B → Cong A B C D → C ≠ D := 

begin
  rintros h h₁,
  use [axiom_nocollapse _ _ _ _ h h₁],
end 


lemma raystrict {A B C : Point }: Out A B C → A ≠ C := 

begin 
  rintros ⟨J , h⟩ h2,
  cases bet.neq h.1 with h3, 
  contradiction,
end 

lemma bet_preserved {A B C a b c : Point}: Cong A B a b → Cong A C a c → Cong B C b c →
BetS A B C → BetS a b c := 

begin 
  rintros h h2 h3 h4,
  cases bet.neq h4 with h5 h6, 
  rcases postulate_extension _ _ _ _ (null3 h6.1 h) h5 with ⟨d, h7L, h7R⟩, 
  simp [axiom_betweennesssymmetry _ _ _ (cn_equalitysub _ _ _ _ (axiom_nullsegment1 _ _ _ (axiom_5_line _ _ _ _ _ _ _ _ (h7R.symm) h2 h3 h4 h7L h).symm)
  (axiom_betweennesssymmetry _ _ _ h7L ))],
end 

lemma layoff {A B C D : Point}:
A ≠ B → C ≠ D → ∃ X, Out A B X ∧ Cong A X C D := 

begin 
  rintros h h1,
  cases postulate_extension _ _ _ _ h.symm h1 with E h2,
  rcases bet.neq (axiom_betweennesssymmetry _ _ _ h2.1 ) with ⟨ _ , h4⟩,
  rcases postulate_extension _ _ _ _ h4.1 h1 with ⟨P, h5⟩,
  use ⟨_, ⟨_, h5.1, (axiom_betweennesssymmetry _ _ _ h2.1 )⟩, h5.2⟩,
end 


lemma doublereverse {A B C D : Point}:
Cong A B C D → Cong D C B A ∧ Cong B A D C :=
begin 
  introv h, 
  have h₁:= (cn_equalityreverse B A).trans (h.trans (cn_equalityreverse C D)), 
  use ⟨(h₁).symm , h₁⟩ ,
end 

lemma lt_cong {A B C D E F : Point}: Lt A B C D → Cong C D E F → Lt A B E F:=
begin
rintros ⟨G, h1⟩ h2,
cases postulate_extension _ _ _ _ (null3 ((bet.neq h1.1).2.2) h2).symm (null3 ((bet.neq h1.1).2.2) h2).symm with P h5,
rcases bet.neq (axiom_betweennesssymmetry _ _ _ h5.1) with ⟨ _ , h7, _ ⟩ ,
cases postulate_extension _ _ _ _ h7 (null3 (((bet.neq h1.1).2.1)) h1.2) with H h9,
cases postulate_extension _ _ _ _ (((bet.neq h1.1).2.2)).symm h7.symm with Q h10,
cases doublereverse (axiom_5_line _ _ _ _ _ _ _ _ ((h1.2.trans (h9.2.symm))) 
(cn_sumofparts _ _ _ _ _ _ (((cn_equalityreverse Q C).trans h10.2).trans 
(cn_equalityreverse E P))h2 (axiom_betweennesssymmetry _ _ _ h10.1) (axiom_betweennesssymmetry _ _ _ h5.1)) h2 
(axiom_innertransitivity _ _ _ _ (axiom_betweennesssymmetry _ _ _ h10.1) h1.1)h9.1 
(((cn_equalityreverse Q C).trans h10.2).trans (cn_equalityreverse E P))),
use ⟨H, (bet_preserved (h1.2.trans (h9.2.symm)) h2 right h1.1), h9.2⟩, 

end 

lemma lt_neq {A B C D : Point} : Lt A B C D → A ≠ B ∧  C ≠ D :=
begin 
  rintro ⟨E, h⟩,
  simp [bet.neq h.1, null3 (bet.neq h.1).2.1 h.2],
end 


lemma crossbar {A B C E U V : Point}:
   Triangle A B C → BetS A E C → Out B A U → Out B C V →
   ∃ X, Out B E X ∧ BetS U X V :=sorry 

lemma angleordertransitive {A B C D E F P Q R : Point}:
   LtA A B C D E F → LtA D E F P Q R →
   LtA A B C P Q R := sorry 

lemma together {A B C D F G P Q a b c : Point} : TG A a B b C c → Cong D F A a → Cong F G B b → BetS D F G → 
Cong P Q C c → Lt P Q D G ∧ A ≠ a ∧ B ≠ b ∧ C ≠ c := 

begin 
rintros⟨R, h₁⟩ h₂ h₃ h₄ h₅, 
have h6 := (cn_sumofparts _ _ _ _ _ _ h₂ (h₃.trans h₁.2.1.symm) h₄ h₁.1).symm,
have h7:= lt_cong (lt_cong2 h₁.2.2 h₅.symm) h6,
rcases bet.neq h₁.1 with ⟨ _ , h8 , h9⟩ ,
rcases ⟨null3  left h₁.2.1, h₁.2.2 ⟩ with    ⟨ _ , S, h10⟩ ,
rcases bet.neq h10.1 with ⟨ h19 , h20, h21⟩,
have h22:= null3 h20 h10.2,
tauto,

end 

lemma not_eq_of_triangle {A B C : Point} : Triangle A B C → (A ≠ B ∧ B ≠ C ∧ A ≠ C)  :=
begin
  intro h,
  refine ⟨_, _, _⟩,
  all_goals { 
    intro hEq,
    have : Col A B C,
      unfold Col,
      tauto,
    contradiction,    
  }
end

lemma neq_partwhole {A B C : Point} : BetS A B C → ¬ Cong A B A C :=
  begin
  introv h1,
  cases bet.neq h1 with h2 h3,
  cases postulate_extension _ _ _ _  h3.1.symm h3.1.symm with D h4,
  have h5:= axiom_betweennesssymmetry _ _ _ h4.1,
  have h6:= T3_7b h5 h1,
  cases bet.neq h6 with _ h7,
  have h8 : ¬Cong A B A C,
    intro hEq,
    have := extensionunique h5 h6 hEq,
    repeat {tauto},
  end 

lemma trichotomy2 {A B C D : Point} : Lt A B C D → ¬ Lt C D A B:= 
  begin
  rintros ⟨E, h1⟩ hEq,
  rcases lt_cong hEq (h1.2.symm) with ⟨F,h3⟩,
  have := neq_partwhole (T3_6b h3.1 h1.1),
  tauto,
  end 

lemma differenceofparts : ∀ {A B C a b c : Point},
Cong A B a b → Cong A C a c → BetS A B C → BetS a b c →
Cong B C b c := 


begin
  rintros _ _ _ _ _ _ h₁ h₂ h₃ h₄,
    rcases ⟨bet.neq h₃, bet.neq h₄⟩ with ⟨h₅, h₆⟩,
    cases postulate_extension _ _ _ _ (h₅.2.2).symm (h₅.2.2) with E h₇,
    cases postulate_extension _ _ _ _ (h₆.2.2).symm (h₆.2.2) with e h₈,
    have h₉:= h₇.2.trans h₂,
    have h10:= h₉.symm,
    have h11:= h₈.2.symm,
    have h12:= h₉.trans h11,
    have h13:= axiom_nullsegment2 C c,
    have h14:= cn_equalityreverse E A,
    have h15:= h14.trans h₇.2,
    have h16:= h15.trans h₂,
    have h17:= ((cn_equalityreverse e a).trans h₈.2).symm,
    have h18:= h16.trans h17,
    rcases ⟨axiom_betweennesssymmetry _ _ _ h₇.1, axiom_betweennesssymmetry _ _ _ h₈.1⟩ with ⟨h19, h20⟩ ,
    have h21:= cn_sumofparts _ _ _ _ _ _ h18 h₂ h19 h20,
    have h22:= doublereverse h₁,
    have h23:= cn_equalityreverse a e,
    have h24:= h12.trans h23,
    have h25:= axiom_innertransitivity _ _ _ _ h19 h₃,
    have h26:= axiom_innertransitivity _ _ _ _ h20 h₄,
    rcases ⟨bet.neq h25, bet.neq h26⟩ with ⟨h27, h28⟩,
    have h29:= axiom_5_line _ _ _ _ _ _ _ _ h₁ h21 h₂ h25 h26 h18,
    have h30:= doublereverse h29,
    tauto,
  
end 

lemma droppedperpendicularunique { A J M P : Point} :
   Per A M P → Per A J P → Col A M J → M = J := sorry 



lemma outerconnectivity {A B C D : Point} :
   BetS A B C → BetS A B D → ¬ BetS B C D → ¬ BetS B D C → C = D :=sorry 

lemma congr_flip' {A B C D : Point} : Cong A B C D → (Cong B A D C ∧ Cong B A C D ∧ Cong A B D C) := 
begin
  rintros h1,
  use [(cn_equalityreverse B A).trans (h1.trans (cn_equalityreverse C D)),
      (cn_equalityreverse B A).trans h1, (h1.trans (cn_equalityreverse C D))],
end 

lemma rightreverse {A B C D : Point} : 
Per A B C → BetS A B D → Cong A B B D → Cong A C D C := 
  begin
  rintros ⟨E , h⟩ h1 h2, 
  cases bet.neq h1 with h3 h4,
  have h5:= ((h2.symm).trans h.2.1),
  cases congr_flip' h5 with h6 h7,
  have h8:= extensionunique h1 h.1 h7.2,
  subst h8, 
  tauto,
  end 
lemma interior5 :
   ∀ {A B C D a b c d : Point}, BetS A B C → BetS a b c → 
   Cong A B a b → Cong B C b c → Cong A D a d → Cong C D c d →
   Cong B D b d :=

   begin
   introv h h1 h2 h3 h4 h5,
   rcases ⟨bet.neq h, bet.neq h1⟩ with ⟨h6, h7⟩,
   cases postulate_extension _ _ _ _ h6.2.2.symm h6.1 with M h8,
   have h9:= axiom_betweennesssymmetry _ _ _ h8.1,
   have h10:= cn_equalityreverse M A,
   have h11:= h10.trans h8.2,
   cases postulate_extension _ _ _ _ h7.2.2.symm h7.1 with m h12,
   have h13:= axiom_betweennesssymmetry _ _ _ h12.1,
   have h14:= cn_equalityreverse m a,
   have h15:= (h14.trans h12.2).symm,
   have h16:= h3.trans h15,
   have h17:= h11.trans h16,
   have h18:= cn_sumofparts _ _ _ _ _ _ h2 h3 h h1,
   have h19:= doublereverse h18,
   rcases ⟨(T3_6a (axiom_betweennesssymmetry _ _ _ h) h8.1), T3_6a (axiom_betweennesssymmetry _ _ _ h1) h12.1⟩ with ⟨h20, h21⟩,
   rcases ⟨doublereverse h17, doublereverse h2⟩ with ⟨h22,h23⟩ ,
   have h24:= congr_flip' (axiom_5_line _ _ _ _ _ _ _ _ h22.2 h5 h4 h8.1 h12.1 h19.2),
   rcases ⟨(axiom_betweennesssymmetry _ _ _ h20), axiom_betweennesssymmetry _ _ _ h21⟩ with ⟨h25, h26⟩,
   have h27:= congr_flip' (axiom_5_line _ _ _ _ _ _ _ _ h2 h24.1 h4 h25 h26 h17),
   tauto,

   end 

lemma T8_3 :
   ∀ { A B C D : Point}, Per A B C → Out B C D → Per A B D :=sorry 


lemma SS_refl {A B P : Point}: A ≠ B → ¬ Col A B P → SS P P A B := 
begin
  rintros h₁ h₂,
  have h₃: P ≠ A,
    intro hEq,
    have : Col A B P := (or.inr (or.inl (hEq.symm))),
    tauto,
  cases postulate_extension _ _ _ _ h₃ h₃.symm with C, 
  use [C , A , A, ((or.inr (or.inl ⟨A⟩))) , ((or.inr (or.inl ⟨A⟩))), h.1, h.1, h₂, h₂], 

end 

lemma NCdistinct {A B C : Point} : ¬Col A B C → A ≠ B ∧ B ≠ C ∧
A ≠ C ∧ B ≠ A ∧ C ≠ B ∧ C ≠ A :=
begin 
  rintros h1 ,
  refine ⟨ _, _, _, _, _, _⟩,
  all_goals { 
    intro hEq,
    subst hEq,
  },
  have : Col _ _ C :=  or.inl ⟨A⟩,
   tauto,
  have : Col A _ _:= or.inr(or.inr(or.inl ⟨B⟩)), 
  tauto,
  have: Col _ B _ := (or.inr(or.inl ⟨A⟩)),
  tauto,
  have : Col _ _ C :=  or.inl ⟨B⟩,
   tauto,
  have : Col A _ _:= or.inr(or.inr(or.inl ⟨C⟩)), 
  tauto,
  have: Col _ B _ := (or.inr(or.inl ⟨C⟩)),
  tauto,
end 

lemma ray2 {A B C : Point}: Out A B C → A ≠ B := 

begin 
  rintros ⟨E,⟨h3,h4⟩⟩ h2, 
  rcases bet.neq h4 with ⟨h5, _ ⟩, contradiction,
end

lemma ray : ∀ {A B P : Point}, Out A B P → P ≠ B → ¬ BetS A P B →
BetS A B P := 

begin
  rintros _ _ _ ⟨E, h⟩ h1 h2,
  have h3:= (ray2 ⟨E, h⟩),
  have h4:= bet.neq h.1,
  cases postulate_extension _ _ _ _ h3 h4.1 with D h5,
  have h6:= ((cn_equalityreverse D B).trans h5.2).symm,
  have h7:= axiom_betweennesssymmetry _ _ _ h5.1,
  have h8: Lt A P D A := ⟨ B, h7, ((cn_equalityreverse D B).trans h5.2)⟩,
  have h9:= lt_cong h8 (cn_equalityreverse D A),
  have h10:= bet.neq h7,
  cases h9 with F h11,
  have h12:= T3_7b h.2 h5.1,
  have h13:= axiom_innertransitivity _ _ _ _ h12 h11.1,
  have h14:= (extensionunique h13 h.1 h11.2).symm,
  subst h14,
  have h14: ¬¬BetS A B P,
    intro hEq,
    have h:= axiom_connectivity _ _ _ _ h5.1 h11.1 hEq h2,
    tauto,
  use of_not_not h14,
end

lemma ray1 : ∀ {A B P : Point}, Out A B P → (BetS A P B ∨ B = P ∨ BetS A B P):= sorry

lemma ray3 : ∀ {B C D V : Point},
   Out B C D → Out B C V → Out B D V := 

   begin
   rintros _ _ _ _ ⟨E, h1⟩ ⟨H, h2⟩,
   have h3: ¬¬ BetS E B V,
    intro h,
    have h4: ¬ BetS B E H, 
      intro h,
      have h5:= axiom_betweennesssymmetry _ _ _ h,
      have h6:= T3_6a h5 h2.1,
    tauto,
    have h7: ¬ BetS B H E,
      intro h,
      have h₁:= axiom_betweennesssymmetry _ _ _ h,
      have h₂:= T3_7a h₁ h2.1,
    tauto,
      have h8:= (outerconnectivity (axiom_betweennesssymmetry _ _ _ h2.2) (axiom_betweennesssymmetry _ _ _ h1.2) h7 h4).symm, 
      subst h8,
    tauto,
    have h9:= of_not_not h3,
    use E, tauto,
   end 

lemma ray4  {A B E : Point} : (BetS A E B ∨ E = B ∨ BetS A B E) → A ≠ B →
  Out A B E := 

  begin
  introv h1 h2,
  cases postulate_extension _ _ _ _ h2.symm h2 with J h3,
  have h4:= axiom_betweennesssymmetry _ _ _ h3.1,
  cases_type* or,
  have h5 := axiom_innertransitivity _ _ _ _ h4 h1,
  use [J], tauto,
  subst h1,
  use J, tauto,
  have h4:= T3_7b h4 h1,
  use J, tauto,
  end 

lemma ray5 : ∀ {A B C : Point}, Out A B C → Out A C B := 

begin

  rintros _ _ _ h₁,
  cases (ray1 h₁) with h₂,
  all_goals {cases_type* or},
  have h₃:= raystrict h₁,
  use (ray4 (or.inr(or.inr (h₂))) h₃), 
  have h₃:= raystrict h₁,
  use (ray4 (or.inr(or.inl (h))) h₃), 
  have h₃:= raystrict h₁,
   use (ray4 ((or.inl (h))) h₃), 
end 


lemma collinear1 : ∀ {A B C : Point}, Col A B C → Col B A C :=

  begin
  rintros _ _ _ ⟨⟨h⟩⟩,
  use or.inl ⟨A⟩,
  cases_type* or,
  use or.inr(or.inr(or.inl ᾰ)), 
  use (or.inr(or.inl ᾰ)),
  use or.inr(or.inr(or.inr(or.inr(or.inl ᾰ)))), 
  use (or.inr(or.inr(or.inr(or.inl ᾰ)))), 
  use (or.inr(or.inr(or.inr(or.inr(or.inr(axiom_betweennesssymmetry _ _ _ ᾰ)))))),
  end 


lemma collinear2: ∀ {A B C : Point}, Col A B C → Col B C A := sorry

--rename 
lemma collinearreverse: ∀ {A B C: Point}, Col A B C → Col C B A := sorry 


lemma collinearorder {A B C : Point}: Col A B C →
Col B A C ∧ Col B C A ∧ Col C A B ∧ Col A C B ∧ Col C B A := 
begin
rintros h,
simp [collinear2 h, collinear1 h, collinear2 (collinear2 h), 
    collinear2 (collinear1 h), collinear1 ( collinear2 h)], 
end 



lemma collinear_lemma (A B C : Point) (H : Col A B C ∨ Col A C B ∨ Col B A C ∨ Col B C A ∨ Col C B A ∨ Col C A B) :
  Col A B C := 
  begin
  cases_type* or,
  tauto,
  repeat {simp [collinearorder H]}, 
  end 

lemma collinear_lemma' (A B C : Point) (H : BetS A B C ∨ BetS A C B ∨ BetS B A C ∨ BetS B C A ∨ BetS C B A ∨ BetS C A B) :
  Col A B C :=
sorry

meta def collinear_tac : tactic unit :=  `[ subst_vars ] >> (`[ apply collinear_lemma, simp *] <|> 
`[ apply collinear_lemma', simp *])

example (A B C : Point) (H : Col A B C) : Col C B A :=
by collinear_tac

example (A B C D : Point) (H : Col A B C) (H' : C = D) : Col A B D := 
by collinear_tac


lemma collinear_identity_lemma ( A B : Point) (H : A = A ) (H' : B = B): 
  Col B B A := sorry

lemma collinear_identity_lemma' ( A B : Point) (H : A = A) (H' : B = B): 
  Col A B A := sorry 

lemma collinear_identity_lemma'' ( A B : Point) (H : A = A ) (H' : B = B): 
  Col A B B := sorry 

meta def collinear_identity : tactic unit := `[ subst_vars ] >> (`[ apply collinear_identity_lemma, simp *] <|> 
`[ apply collinear_identity_lemma', simp *] <|> (`[ apply collinear_identity_lemma'', simp *]))

  
-- lemma ray_identity_lemma (A B E : Point) ( H : ( E = B ∨ B = E)) :
--   Out A B E := sorry 

-- lemma ray_identity_lemma' (A B E : Point) ( H : ( E = B ∨ B = E) ∧ A ≠ B ∨ B ≠ A ) :
--   Out A E B := sorry 

-- lemma ray_identity_lemma'' (A B : Point) (H : B = B) (H' : A ≠ B) : Out A B B := 
--   begin
--   simp [(ray4 (or.inr(or.inl H)) H')], 
--   end 

-- meta def ray_identity : tactic unit :=   `[ subst_vars ] >> (`[ apply ray_identity_lemma'', simp *] >> `[ try {assumption, simp [bet.neq] at *])

-- meta def cleanup : tactic unit := `[ try { simp only [col1, col2, col3, col4, col5, ne, nesymm, 
-- cong1, cong2, cong3, cong4, cong5, cong6, cong7, congA1, congA2, par1, par2, par3, par4, par5, par6, par7] }; try { assumption } ]
-- meta def ray_identity : tactic unit := (`[ apply ray_identity_lemma'', simp * at *]) <|> `[assumption']


-- meta def cleanup_hyps : tactic unit := `[ try { simp only [col1, col2, col3, col4, col5, ne, nesymm, 
-- cong1, cong2, cong3, cong4, cong5, cong6, cong7, congA1, congA2, par1, par2, par3, par4, par5, par6, par7] at *} ]

-- meta def ray_identity : tactic unit := `[ subst_vars ] >> (`[ apply ray_identity_lemma, simp *])


lemma congr_symm {A B C D : Point}: Cong B C A D → Cong A D B C := 
begin 
  rintros h₁,
  use [cn_congruencetransitive A D B C B C h₁ (cn_congruencereflexive B C)],
end 




--namespace euclidean_preneutral
--namespace Par


lemma euclidean_preneutral.Par.symm {A B C D : Point}: Par A B C D → Par C D A B :=sorry 

lemma euclidean_preneutral.Par.NC {A B C D : Point}: Par A B C D →
   ¬Col A B C ∧ ¬Col A C D ∧ ¬Col B C D ∧ ¬Col A B D := sorry 

lemma euclidean_preneutral.Par.flip {A B C D : Point}:
   Par A B C D → Par B A C D ∧ Par A B D C ∧ Par B A D C := sorry 


-- end Par
-- end euclidean_preneutral


section
variables U V W X : Point
variable h :  Par U V W X
variable h' : Par W X U X

end




lemma NCorder {A B C : Point}:
   ¬Col A B C → ¬Col B A C ∧ ¬Col B C A ∧ ¬Col C A B ∧ ¬Col A C B ∧ ¬Col C B A := sorry 

lemma samesidesymmetric {A B P Q : Point}: 
   SS P Q A B → SS Q P A B ∧ SS P Q B A ∧ SS Q P B A:= sorry 

lemma collinear4 : ∀ (A : Point) {B C D : Point}, Col A B C → Col A B D → A ≠ B → Col B C D := sorry

lemma collinear5 : ∀ {A B C D E : Point}, A ≠ B → C ≠ D → Col A B C → Col A B D → Col A B E → Col C D E := sorry 

lemma oppositesidesymmetric { A B P Q : Point}: OS P A B Q → OS Q A B P := sorry 

lemma collinearparallel {A B C c d : Point}:
   Par A B c d → Col c d C → C ≠ d → Par A B C d := sorry 

lemma crisscross {A B C D : Point}: 
   Par A C B D → ¬ CR A B C D → CR A D B C := sorry 

lemma NChelper {A B C P Q : Point}:
   ¬Col A B C → Col A B P → Col A B Q → P ≠ Q → ¬Col P Q C :=sorry 

lemma twolines {A B C D E F : Point}:
   Cut A B C D E → Cut A B C D F → ¬Col B C D →
   E = F :=sorry 



lemma rightangleNC : ∀ {A B C : Point}, Per A B C → ¬Col A B C := sorry 

lemma rayimpliescollinear {A B C : Point}: Out A B C → Col A B C :=

begin
  rintros ⟨ J , h1 ⟩, 
  cases bet.neq h1.1 with h2 h3, 
  have h4: (Col J A B), by collinear_tac,
  have h5: (Col J A C), by collinear_tac,
  simp [collinear4 J h4 h5 h3.1 ],
end 

--namespace euclidean_preneutral
--namespace CongA


lemma euclidean_preneutral.CongA.symm {A B C a b c : Point}:
CongA A B C a b c → CongA a b c A B C := sorry

lemma euclidean_preneutral.CongA.trans {A B C D E F P Q R : Point}:
CongA A B C D E F → CongA D E F P Q R → CongA A B C P Q R := sorry

lemma euclidean_preneutral.CongA.flip :  ∀ {A B C D E F : Point}, 
CongA A B C D E F → CongA C B A F E D := sorry 

lemma euclidean_preneutral.CongA.NC :
 ∀ {A B C a b c : Point}, CongA A B C a b c → ¬ Col a b c := sorry 


-- end CongA
-- end euclidean_preneutral

section
variables Q R U V W X : Point
variable h :  CongA Q R U V W X
variable h' : CongA V W X X W V 

end

lemma angledistinct {A B C a b c : Point}:
CongA A B C a b c → A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c := 

begin 
  rintros h1,
  have h2:= h1.symm,
  rcases h1 ,
  refine ⟨ _,_,_,_,_,_⟩,
  repeat{
    intro hEq, 
    have : Col A B C, by collinear_identity, 
    tauto,},
    intro h, 
    repeat {rcases h2},
    have h2: Col a b c := (or.inl h),
    tauto,
     repeat{
    intro hEq, 
    have : Col a b c, by collinear_identity, 
    tauto,},
end 

lemma equalangleshelper: ∀ {A B C a b c p q : Point},
CongA A B C a b c → Out b a p → Out b c q → CongA A B C p b q :=
  begin
  rintros _ _ _ _ _ _ _ _ ⟨U, V, u, v, h1⟩ h2 h3,
  have h4:= ray3 h2 h1.2.2.1,
  have h5:= ray3 h3 h1.2.2.2.1,
  use [ U, V, u, v], 
  tauto,
  end

lemma angleorderrespectscongruence2 {A B C D E F a b c : Point}:
   LtA A B C D E F → CongA a b c A B C → LtA a b c D E F := sorry


lemma layoffunique : ∀ (A B C D : Point), Out A B C → Out A B D → Cong A C A D → eq C D := sorry

lemma ABCequalsCBA: ∀ {A B C : Point}, ¬ Col A B C → CongA A B C C B A := sorry 

lemma eq_anglesrefl {A B C : Point}: ¬ Col A B C → CongA A B C A B C := 
  begin 
  rintros h1,
  simp [(ABCequalsCBA h1).trans(ABCequalsCBA ( (ABCequalsCBA h1).NC))],
  end 

lemma supplements {A B C D F a b c d f : Point}:
CongA A B C a b c → Supp A B C D F → Supp a b c d f →
CongA D B F d b f := sorry

lemma T8_2 : ∀ {A B C : Point}, Per A B C → Per C B A := sorry 

lemma collinearright : ∀ {A B C D : Point}, 
Per A B D → Col A B C → C ≠ B → Per C B D := sorry 

section 

lemma col1 (A B C : Point) : Col A B C = Col A C B := sorry
lemma col2 (A B C : Point) : Col A B C = Col B A C := sorry
lemma col3 (A B C : Point) : Col A B C = Col B C A := sorry
lemma col4 (A B C : Point) : Col A B C = Col C A B := sorry
lemma col5 (A B C : Point) : Col A B C = Col C B A := sorry
lemma nesymm (A B : Point) : ¬ (A = B) ↔ ¬ (B = A) := sorry

--local attribute [simp] col1 col2 col3 col4 col5 ne nesymm 

lemma cong1 (A B C D : Point) : Cong A B C D = Cong A B D C := sorry
lemma cong2 (A B C D : Point) : Cong A B C D = Cong B A C D := sorry
lemma cong3 (A B C D : Point) : Cong A B C D = Cong B A D C := sorry
lemma cong4 (A B C D : Point) : Cong A B C D = Cong C D A B := sorry 
lemma cong5 (A B C D : Point) : Cong A B C D = Cong C D B A := sorry 
lemma cong6 (A B C D : Point) : Cong A B C D = Cong D C A B := sorry 
lemma cong7 (A B C D : Point) : Cong A B C D = Cong D C B A := sorry 
lemma congA1 (A B C a b c : Point) : CongA A B C a b c = CongA a b c A B C := sorry
lemma congA2 (A B C a b c: Point) : CongA A B C a b c =  CongA C B A c b a := sorry 

-- local attribute [simp] cong1 cong2 cong3 cong4 cong5 cong6 cong7 congA1 congA2

lemma par1 (A B C D : Point): Par A B C D = Par A B D C  :=sorry 
lemma par2 (A B C D : Point): Par A B C D = Par B A C D :=sorry
lemma par3 (A B C D : Point): Par A B C D = Par B A D C :=sorry
lemma par4 (A B C D : Point): Par A B C D = Par C D A B :=sorry
lemma par5 (A B C D : Point): Par A B C D = Par C D B A :=sorry
lemma par6 (A B C D : Point): Par A B C D = Par D C A B :=sorry
lemma par7 (A B C D : Point): Par A B C D = Par D C B A :=sorry

-- local attribute [simp] par1 par2 par3 par4 par5 par6 par7

meta def cleanup : tactic unit := `[ try { simp only [col1, col2, col3, col4, col5, ne, nesymm, 
cong1, cong2, cong3, cong4, cong5, cong6, cong7, congA1, congA2, par1, par2, par3, par4, par5, par6, par7] }; try { assumption } ]

meta def cleanup_hyps : tactic unit := `[ try { simp only [col1, col2, col3, col4, col5, ne, nesymm, 
cong1, cong2, cong3, cong4, cong5, cong6, cong7, congA1, congA2, par1, par2, par3, par4, par5, par6, par7] at *} ]

example (A B C E Q : Point) (h1 : Col C B A) (h2 : Col Q A C) (h3 : Col E A Q) (h4 : A ≠ Q) : Col B A C :=
begin
  cleanup_hyps,
  have : Col A E C,
  { apply @collinear4 _ _ Q; cleanup,
   }, tauto,
  -- have : ¬ Col C C A, cleanup,
end

  example (A B C D : Point) (h1 : Cong A B C D): Cong D C B A :=
begin
  cleanup_hyps,
  { cleanup,
   },

end

lemma ray_identity_lemma (A B : Point) (H : B = B) (H' : A ≠ B) : Out A B B := 
  begin
  simp [(ray4 (or.inr(or.inl H)) H')], 
  end 

-- lemma ray_identity_lemma' (A B : Point) (H : B = B → A ≠ B ): Out A B B :=sorry

lemma ray_identity_lemma'( A B : Point) (H': A ≠ B): Out A B B := sorry 

lemma ray_identity_lemma'' (A B : Point) (H : A = A) (H' : A ≠ B) : Out B A A := 
  begin
  simp [(ray4 (or.inr(or.inl H)) H'.symm)], 
  end 

-- lemma ray_identity4 (A B : Point) A ≠ B → exists X, BetS A B X)


meta def ray_identity : tactic unit := `[ subst_vars ] >> ( `[ apply ray_identity_lemma, simp * at *]  <|>
`[apply ray_identity_lemma', simp * ] ) >> `[tauto {closer := ray_identity}] <|> (`[ cleanup, simp *] <|> `[ cleanup, tauto])

-- meta def ray_identity : tactic unit := `[ subst_vars ] >> (`[ apply ray_identity_lemma, simp *] ) <|>
--  `[ apply ray_identity_lemma', simp *] <|> (`[ apply ray_identity_lemma'', simp *] ) >> `[cleanup, tauto] --{closer := ray_identity}] 
-- --  `[ subst_vars ] >> (`[ apply ray_identity_lemma, simp *] <|> 
 
--  `[ apply ray_identity_lemma', simp *] <|> (`[ apply ray_identity_lemma'', simp *]))

--  (`[ cleanup_hyps, apply ray_identity_lemma', simp *])) >> `[tauto {closer := ray_identity}] 
-- --<|>  (`[ cleanup, simp *])


-- meta def collinear_identity : tactic unit := `[ subst_vars ] >> (`[ apply collinear_identity_lemma, simp *] <|> 
-- `[ apply collinear_identity_lemma', simp *] <|> (`[ apply collinear_identity_lemma'', simp *]))

  


end 

end 

class euclidean_neutral_ruler_compass (Point : Type) extends euclidean_neutral Point :=

(axiom_circle_center_radius : ∀ A B C J P, CI J A B C → OnCirc P J → Cong A P B C)

(postulate_line_circle : ∀ A B C K P Q, CI K C P Q -> InCirc B K -> A ≠ B ->
  exists X Y, Col A B X ∧ BetS A B Y ∧ OnCirc X K ∧ OnCirc Y K ∧ BetS X B Y) 

( postulate_circle_circle : 
  ∀ C D F G J K P Q R S, CI J C R S → 
  InCirc P J → OutCirc Q J → CI K D F G → OnCirc P K → OnCirc Q K 
  → ∃ X, OnCirc X J ∧ OnCirc X K)


open euclidean_neutral_ruler_compass 


section 

  variables {Point : Type}
  variable [euclidean_neutral_ruler_compass Point]

  variables x y z : Point
  variables C D E : euclidean_preneutral.Circle Point


lemma localextension {A B Q : Point}: A ≠ B → B ≠ Q → ∃ X, BetS A B X ∧ Cong B X B Q := sorry 

lemma angletrichotomy {A B C D E F : Point}: LtA A B C D E F → ¬ LtA D E F A B C := sorry

lemma angletrichotomy2 {A B C D E F : Point}: 
¬Col A B C → ¬Col D E F → ¬ CongA A B C D E F → ¬ LtA D E F A B C → LtA A B C D E F := sorry

lemma trichotomy1 {A B C D : Point}: ¬ Lt A B C D → ¬ Lt C D A B → A ≠ B → C ≠ D → Cong A B C D := sorry

/-- To construct an equilateral triangle on a given finite straight line. -/
lemma proposition_01 : ∀ (A B: Point), A ≠ B → ∃ X, Equilateral A B X ∧ Triangle A B X := 
begin 
  introv h1,
  rcases ⟨postulate_Euclid3 A B h1, postulate_Euclid3 B A h1.symm, localextension h1.symm h1⟩ with ⟨⟨J ,h2⟩, ⟨K , h4⟩⟩,
  cases localextension h1.symm h1 with D h5,
  have h16: OnCirc D J:=⟨_, _, _ , h2, h5.2⟩,
  rcases postulate_circle_circle _ _ _ _ _ _ _ _ _ _ h4 ⟨A, B, _, _, _, h4, or.inl ⟨B⟩⟩ 
   ⟨ _, _, _, _, h4, h5.1, cn_congruencereflexive B A⟩ h2 ⟨ _ , _, _, h2, (cn_congruencereflexive A B)⟩ h16 with ⟨C , h22⟩ ,
  have h25: Cong A C A B := axiom_circle_center_radius _ _ _ _ _ h2 h22.2,
  have h27:= h25.symm,
  have h28:= axiom_circle_center_radius _ _ _ _ _ h4 h22.1,
  rcases congr_flip' h28 with ⟨ _ , _ , h32 ⟩,
  have h38:= axiom_nocollapse _ _ _ _ h1 h32.symm,
  have h39:= axiom_nocollapse _ _ _ _ h38 (((h32.trans h25.symm)).trans (cn_equalityreverse A C)), 
  have h40: ¬ BetS A C B ∧ ¬ BetS A B C, 
    refine ⟨_,_⟩,
    repeat{
    intro hEq,
    have h₁:= neq_partwhole hEq,
      contradiction},
  have h42: ¬ BetS B A C,
    intro h,
    have h₁: ¬Cong B A B C := neq_partwhole h,
    have h₂: Cong B A B C := (cn_equalityreverse B A).trans h32.symm, 
    tauto,
  have h43: ¬ Col A B C, 
    intro h,
    have h₂: A = B ∨ A = C ∨ B = C ∨ BetS B A C ∨ BetS A B C ∨ BetS A C B := h,
    tauto,
  use ⟨ C , ⟨h32.symm ,((h32.trans (h25.symm)).trans (cn_equalityreverse A C))⟩, h43⟩,
 end 

/-- To place a straight line equal to a given straight line with one end at a given point. -/

lemma proposition_02 : ∀ (A B C : Point), A ≠ B -> B ≠ C -> exists X, Cong A X B C := 


begin 
  introv h1 h2, 
  cases proposition_01 _ _ h1 with D h3,
  rcases ⟨congr_flip' h3.1.1.symm, postulate_Euclid3 B C h2, NCdistinct h3.2⟩ with ⟨ ⟨_ , h8⟩ , ⟨J , h9⟩, ⟨_, _ , _, _ , h12, _ ⟩⟩,
  rcases postulate_line_circle _ _ _ _ _ _ h9 (⟨ D, B, _ , _, _, h9 , or.inl ⟨B⟩⟩) h12 with ⟨ P , G , h13⟩, 
  rcases h13 with ⟨ _, h15, _, _ ⟩,
  rcases bet.neq h15,
  rcases postulate_Euclid3 D G right.right with ⟨R, h16⟩,
  have h17:= axiom_circle_center_radius _ _ _ _ _ h9 h13_right_right_right.1,
  rcases congr_flip' (h3.1.2.symm) with ⟨ _ , _ , _ ⟩, 
  have h24: InCirc A R := ⟨ _, _, _, _, _, h16, (or.inr ⟨h15 ,(cn_congruencereflexive D G), right_1_right⟩)⟩,
  rcases NCdistinct h3.2 with ⟨ _ , _ , _ , h26, _ ,h25 ⟩,
  have h27:= postulate_line_circle _ _ _ _ _ _ h16 h24 h25,
  rcases h27 with ⟨ Q , L , ⟨h28 , h29, h30, h31, h32⟩ ⟩,
  have h33:= axiom_circle_center_radius _ _ _ _ _ h16 h31, 
  use ⟨L, cn_congruencetransitive _ _ _ _ _ _ (differenceofparts right_1_right.symm h33.symm h15 h29) h17⟩, 
end 

/--Given two unequal straight lines, to cut off from the greater a straight line equal to the less.-/
lemma proposition_03: ∀(A B C D E F : Point), A ≠ B → C ≠ D → Lt C D A B → Cong E F A B → 
∃ X, BetS E X F ∧ Cong E X C D := 

begin 
  introv h1 h2 h3 h4, 
  use [lt_cong h3 h4.symm],
end 

end

open euclidean_neutral 

section 

variables {Point : Type} 
variable [euclidean_neutral Point]

variables x y z : Point 
variables C D E : euclidean_preneutral.Circle Point 

  lemma angleorderrespectscongruence {A B C D E F P Q R : Point}: LtA A B C D E F → CongA P Q R D E F →
   LtA A B C P Q R :=sorry 

end 

open euclidean_neutral_ruler_compass


section 

  variables {Point : Type}
  variable [euclidean_neutral_ruler_compass Point]

  variables x y z : Point
  variables C D E : euclidean_preneutral.Circle Point


/--If two triangles have the two sides equal to two sides respectively, 
and have the angles contained by the equal straight lines equal, 
they will also have the base equal to the base, the triangle will be equal
to the triangle, and the remaining angles will be equal to the remaining angles
 respectively, namely those which the equal sides subtend. -/



lemma proposition_04 : ∀ (A B C a b c : Point), Cong A B a b → Cong A C a c → CongA B A C b a c →
Cong B C b c ∧ CongA A B C a b c ∧ CongA A C B a c b := sorry

-- begin 
--   rintros _ _ _ _ _ _ h₁ h₂ h₃,
--   have h₄a : ¬Col b a c := h₃.NC,
--   rcases h₃ with ⟨U, V, u, v, h11,_,h5⟩,
--   have h₄:= ray2 h5.1,
--   have h₅: ¬ Col A B C,
--     {intro h, 
--     rcases collinearorder h, 
--     tauto},
--   -- have h5a := NCdistinct h₅,
--   -- have h6a:= NCdistinct h₄a,
--   have h₆: A ≠ B, 
--     {intro h, 
--     have : Col A B C := or.inl h, 
--     tauto},
--   have h₇: A ≠ C,
--   {intro h, 
--     have : Col A B C := or.inr(or.inl h), 
--     tauto},
--   have h₈ : a ≠ c,
--     {intro h,
--     have h9: Col b a c := or.inr(or.inr(or.inl h)), 
--     tauto},
--   have h₉ : b ≠ c,
--     {intro h, 
--     have : Col b a c := (or.inr(or.inl h)), 
--     tauto},
--   have h10: B ≠ C,
--     {intro h, 
--     have : Col B A C := (or.inr(or.inl h)), 
--     tauto},
--   have h12:= ray1 h11,
--   have h13: Cong B V b v,
--   cases_type* or, 
--       have h2: Cong A U A U := cn_congruencereflexive A U,
--       have h3: Lt A U A B:=  ⟨ U , h12, cn_congruencereflexive A U⟩,
--       rcases lt_cong h3 h₁ with ⟨w, h4, h₅⟩,
--       rcases bet.neq h4 with ⟨_,h6⟩,
--       have h30:= ray4 (or.inl(h4)) h6.2,
--       have h20:= layoffunique _ _ _ _ h5.1 h30 (h₅.trans h5.2.2.1).symm,
--       subst h20,
--       have h22: Cong U B u b := differenceofparts h5.2.2.1 h₁ h12 h4,
--       have h23: Cong V B v b := axiom_5_line _ _ B V _ _ b v h22 h5.2.2.2.1 h5.2.2.2.2.1 h12 h4 h5.2.2.1,
--       rcases congr_flip' h23 with ⟨ h24, h25⟩, 
--       tauto,
--     subst h12,
--       have h6:= ray1 h5.1,
--     have h7:= ((h₁.symm).trans ((cn_congruencereflexive A B).trans h5.2.2.1)).symm,
--     cases_type* or,
--       have h7: b = u, 
--         have h2:= neq_partwhole h6,
--       tauto,
--         subst h7,
--       tauto,
--         subst h6,
--       tauto,
--     have h7: b = u, 
--       have h2:= neq_partwhole h6,
--       have h6:= (h₁.symm.trans ((cn_congruencereflexive A B).trans h5.2.2.1)),
--       tauto,
--       subst h7,
--       tauto,
--     have h3: Lt A B A U:= ⟨B, h12 , (cn_congruencereflexive A B)⟩,
--     rcases lt_cong h3 h5.2.2.1 with ⟨f, h4, h13 ⟩,
--     rcases bet.neq h4 with ⟨_,h₅⟩,
--     have h20:= (layoffunique _ _ _ _  (ray4 (or.inl(h4)) h₅.2) (ray5 h5.1) (h13.trans h₁)).symm,
--     subst' h20,
--     have h36:= differenceofparts (h₁) h5.2.2.1 h12 h4,
--     have h37:= interior5 h12 h4 h₁ h36 h5.2.2.2.1 h5.2.2.2.2.1,
--     tauto,
--     have h15:= ray1 h₃_h_h_h_h_right_left,
--     have h16: Cong B C b c, 
--     cases ray1 h₃_h_h_h_h_right_left with h16 h17,
--       have h3: Lt A V A C:=  ⟨ V , h16, (cn_congruencereflexive A V)⟩,
--         rcases lt_cong h3 h₂ with ⟨g, h12, h17⟩,
--         rcases bet.neq h12 with ⟨_,h18⟩,
--         have h19:= ray4 (or.inl(h12)) h18.2,
--         have h22:= (layoffunique _ _ _ _ (ray4 (or.inl(h12)) h18.2) h5.2.1 (h17.trans h5.2.2.2.1)).symm,
--         subst' h22,
--         have h22:= differenceofparts h5.2.2.2.1 h₂ h16 h12,
--         rcases congr_flip' h13 with ⟨ h23, h24⟩, 
--         have h23:= axiom_5_line _ _ _ _ _ _ _ _ h22 h₁ h23 h16 h12 h5.2.2.2.1,
--       tauto,
--       cases h17 with h16 h17,
--       subst h16,
--       have h20: Out a _ _ := ray4(or.inr(or.inl ⟨c⟩)) (ray2 h5.2.1),
--       have h21:= layoffunique _ _ _ _ h20 h5.2.1 (h₂.symm.trans h5.2.2.2.1),
--       subst h21,
--       tauto,
--       have h19: Lt A C A V:=  ⟨ C , h17, (cn_congruencereflexive A C)⟩,
--       rcases lt_cong h19 h5.2.2.2.1 with ⟨g, h19, h20⟩,
--       rcases bet.neq h19 with ⟨_,h21⟩,
--       have h26:= (layoffunique _ _ _ _ (ray4 (or.inl (h19)) h21.2) (ray5 h5.2.1) (h20.trans h₂)).symm,
--       subst h26,
--       have h27: Cong C V c v:= differenceofparts h₂ h5.2.2.2.1 h17 h19,
--       rcases congr_flip' h13 with ⟨ h28, h29⟩, 
--       have h30:= interior5 h17 h19 h₂ h27 h₁ h28,
--       cases congr_flip' h30 with h31 h32,
--       repeat {tauto,},
--       refine ⟨_,_,_⟩,
--       tauto,
--       have h17:= ray5 h11,
--         have h40: Out B A A := ray4(or.inr(or.inl ⟨A⟩)) h₆.symm,
--       have h6: Out B C C := ray4(or.inr(or.inl ⟨C⟩)) h10,
--       have h41: Out b a a := ray4(or.inr(or.inl ⟨a⟩)) (ray2 h5.1).symm,
--       have h42: Out b c c := ray4(or.inr(or.inl ⟨c⟩)) h₉,
--       rcases congr_flip' h₁ with ⟨h43,h11,_⟩,
--       use [A, C, a, c , h40, h6, h41, h42, h43, h16, h₂, h₅ ], 
--       have h40: Out C A A , by ray_identity,
--       have h6: Out C B B , by ray_identity,
--       rcases congr_flip' h₂ with ⟨h43, h11, _⟩ ,
--       rcases congr_flip' h16 with ⟨h44, h45⟩ ,
--       -- have h46a:= NCorder h₅,
--       have h46: ¬ Col A C B, 
--       intro hEq,
--       rcases collinearorder hEq with ⟨h1, h2⟩ ,
--         tauto, 
--       use ⟨A , B, a, b, h40, h6, (ray4(or.inr(or.inl ⟨a⟩)) h₈.symm), (ray4(or.inr(or.inl ⟨b⟩)) h₉.symm), h43, h44, h₁, h46⟩, 

-- end 
    
/-- In isosceles triangles, the angles at the base are equal to one another -/    
lemma proposition_05 : ∀ (A B C : Point), isosceles A B C → CongA A B C A C B := 

begin
  rintros _ _ _ ⟨h2 , h3⟩,
  have h4: ¬ Col C A B,
    intro h,
    rcases collinearorder h with ⟨ h₁, ⟨h₂,_⟩⟩, 
    contradiction,
  rcases (proposition_04 A C B A B C) h3.symm h3 (ABCequalsCBA  h4), 
  tauto,

end 

/-- ...if the equal straight lines be produced further, the angles under the base will be equal 
to one another.-/
lemma proposition_5b : ∀ (A B C  F G : Point), isosceles A B C → 
BetS A B F → BetS A C G → CongA C B F B C G := 

begin 
  introv h1 h2 h3,
  have h4:=  (proposition_05 A B C h1).NC,
  have h5: B ≠ C,
    intro h, 
    have : Col A C B := or.inr (or.inr (or.inl h.symm)),
    tauto,
  use supplements (proposition_05 A B C h1) ⟨(ray4 (or.inr (or.inl ⟨C⟩)) h5), h2⟩ (⟨(ray4 (or.inr (or.inl ⟨B⟩)) h5.symm), h3⟩),
end 


lemma proposition_6a : ∀ (A B C : Point), Triangle A B C → 
CongA A B C A C B → ¬ Lt A C A B := sorry
-- begin 
-- introv h₁ h₂ h₃,
-- rcases angledistinct h₂ with ⟨ h₃ , h₄, h₅, h₆⟩,
--   have : ¬ Lt A C A B, 
--   intro h,
--     rcases proposition_03 _ _ _ _ _ _ h₃ h₅ h (cn_equalityreverse B A) with ⟨D, h2⟩, 
--     rcases congr_flip' h2.2 with  ⟨ h3 , h4 , h5 ⟩,
--     have h12:= equalangleshelper (eq_anglesrefl h₁) (ray4 (or.inl h2.1) h₃.symm) (ray4 (or.inr(or.inl ⟨C⟩)) h₄),
--     have h14:= ( (h12).symm).trans h₂, 
--       have h15: ¬ Col A C B,
--       intro h,
--       rcases collinearorder h with ⟨ _, _, _, _, _ ⟩ ,
--       contradiction,
--     have h17: ¬ Col D B C,
--       intro h,
--       have h18: Col B D A := or.inr(or.inr(or.inr(or.inr(or.inl h2.1)))),
--       rcases ⟨collinearorder h18, bet.neq h2.1⟩  with ⟨ h20, _ , _, h26⟩,
--       rcases collinearorder (collinear4 (h20.1) h (right_left.symm)) with ⟨h30, _ ⟩,
--       contradiction,
--     have h20:= proposition_04  _ _ _ _ _ _ h5 (cn_equalityreverse B C) h14,
--     have h21: ¬ Col C B A, 
--       intro h,
--       rcases collinearorder h with ⟨ _, _, _, _, h22⟩ ,
--       contradiction,
--     have h23:= (h20.2.2).trans (ABCequalsCBA h21),
--     have h25: ¬ Col A C B, 
--       intro h,
--       rcases collinearorder h with ⟨ _ , _ , _, _, h1⟩ ,
--       contradiction, 
--     have h27:= (h23.trans h₂).trans (ABCequalsCBA h25),
--     have h28:=  (h27.symm).symm,
--     have h31:= ray4 (or.inr (or.inl ⟨B⟩)) h₄.symm,
--     have h32:= ray4 (or.inr (or.inl ⟨A⟩)) h₅.symm,
--     have h33: ¬ Col B C D,
--       intro h34,
--       rcases collinearorder h34 with ⟨ _, _, _, _⟩,
--       contradiction,
--     have h37:= angleorderrespectscongruence2 ( ⟨ _ , _ , _, h2.1 , h31 , h32 , (eq_anglesrefl h33)⟩) ( h27.symm),
--     have h38:= angletrichotomy (h37), 
--   contradiction, 
--   contradiction,
-- end 

lemma proposition_06 : ∀ (A B C : Point),
   Triangle A B C → CongA A B C A C B → Cong A B A C := sorry
-- begin 
-- introv h₁ h₂, 
-- have h₃: ¬ Col A C B,
--   intro h, 
--   rcases collinearorder  h with ⟨ _ , _ , _ , _ , _⟩, 
--   contradiction,
-- rcases angledistinct ( h₂.symm) with ⟨ _ , _, h₅, _⟩, 
-- simp [trichotomy1 (proposition_6a  _ _ _ h₃ ( h₂.symm)) (proposition_6a  _ _ _ h₁ h₂) h₅ left],
-- end


--attempted redo of ten, come back to it 
lemma proposition_10 : ∀ (A B : Point), A ≠ B → ∃ X, BetS A X B ∧ Cong X A X B := sorry

  -- begin
  -- rintros _ _ h1,
  -- cases proposition_01 _ _ h1 with C h2,
  -- have h3: ¬ Col _ _ _ := h2.2,
  -- have h4: Cong _ _ _ _ ∧ Cong _ _ _ _ := h2.1,
  -- have h5:= not_eq_of_triangle h2.2,
  -- rcases ⟨postulate_extension _ _ _ _ h5.2.1.symm h1, postulate_extension _ _ _ _ h5.2.2.symm h1⟩ with ⟨⟨D, h6⟩, E, h7⟩ ,
  -- rcases ⟨axiom_betweennesssymmetry _ _ _ h6.1 , axiom_betweennesssymmetry _ _ _ h7.1⟩ with ⟨h8,h9⟩ ,
  -- have h10: ¬ Col D C E,
  --   intro h,
  --   rcases collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h6.1))))) with ⟨_,_,h₁,_⟩ ,
  --   rcases collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h7.1))))) with ⟨_,_,h₂,_⟩ ,
  --   rcases collinearorder h with ⟨_,_,_,_,h₃⟩ ,
  --   rcases ⟨bet.neq h9, bet.neq h8⟩ with ⟨⟨h₄, h₅⟩, _, h₇⟩ ,
  --   have h₈:= collinear4 h₃ h₂ h₅.2,
  --   rcases collinearorder h₈ with ⟨h₉,_⟩ ,
  --   have h10:= collinear4 h₁ h₉ h₇.2,
  --   have h11:= collinearorder h10,
  -- tauto,
  -- cases postulate_Pasch_inner _ _ _ _ _ h8 h9 h10 with F h11,
  -- have h12: ¬ Col C E B,
  --   intro h,
  --   rcases collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h7.1))))) with ⟨_,_,_,h₁⟩,
  --   have h₂:= bet.neq h9,
  --   have h₃:= collinear4 h h₁.1 h₂.2.2.symm,
  --   have h₄:=collinearorder h₃,
  --   have h₅:= collinear4 h₄.2.2.2.1 h₁.2 h₂.2.1,
  -- tauto,
  -- rcases ⟨axiom_betweennesssymmetry _ _ _ h11.1 , axiom_betweennesssymmetry _ _ _ h11.2⟩ with ⟨h13,h14⟩ ,
  -- have h15:= bet.neq h6.1,
  -- have h16: ¬ Col A D C,
  --   intro h,
  --   have h₁: Col C B D := or.inr(or.inr(or.inr(or.inr(or.inl h6.1)))),
  --   rcases ⟨collinearorder h, collinearorder h₁⟩ with ⟨ ⟨h₂⟩, h₃⟩ ,
  --   have h₄:= collinear4 h₃.2.2.1 right.1 h15.2.2.symm,
  --   have := collinearorder h₄, 
  -- tauto,
  -- cases postulate_Pasch_inner _ _ _ _ _ h13 h6.1 h16 with M h17,
  -- have h18: Lt B F B E := ⟨F, h14 , cn_congruencereflexive B F⟩,
  -- have h19:= bet.neq h14,
  -- have h20:= (congr_flip' h4.2.symm),
  -- have h21: Cong B D A E:= h6.2.trans h7.2.symm,
  -- have h22:= axiom_5_line _ _ _ _ _ _ _ _ (h6.2.trans h7.2.symm).symm h20.2.2.symm (cn_equalityreverse A B) h7.1 h6.1 h20.2.2,
  -- cases proposition_03 _ _ _ _ A D h19.2.2 h19.2.1 h18 h22.symm with G h23,
  -- have h24: Cong G D F E:= differenceofparts h23.2 h22.symm h23.1 h14,
  -- have h25:= doublereverse h24,
  -- have h26:= doublereverse h23.2,
  -- have h27:= doublereverse h21,
  -- -- have h28:= cn_equalityreverse B A,
  -- have h29:= axiom_betweennesssymmetry _ _ _ h23.1, 
  -- have h30 := interior5 h11.2 (axiom_betweennesssymmetry _ _ _ h23.1) h25.1 h26.1 h27.1 (cn_equalityreverse B A),
  -- have h31:= congr_flip' h26.1,
  -- have h32:= doublereverse h30,
  -- have h33:= congr_flip' h25.1,
  -- have h34:= interior5 h14 h23.1 h31.1 h33.1 h21 (cn_equalityreverse E D),
  -- have h35:= (doublereverse h22),
  -- have h36:= doublereverse h35.1,
  -- have h37:= bet_preserved h32.2 h36.2 h34 h13,
  -- have h38:= null3 h1 h6.2.symm,
  -- have h39:= axiom_betweennesssymmetry _ _ _ h37,
  -- have h40: ¬ Col A D E, 
  --   intro h,
  --     have h₁:= collinearorder h,
  --     have h₂ := collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h9))))),
  --     have h₃:= bet.neq h9,
  --     have h₄:= collinearorder (collinear4 h₂.1 h₁.2.2.2.1 h₃.2.1.symm),
  --     have h₅ := collinearorder ( collinear4 h₂.2.2.2.1 (collinear4 h₂.1 h₁.2.2.2.1 h₃.2.1.symm) h₃.2.2),
  --   tauto,
  -- have h41: ¬ Col A D B, 
  --   intro h,
  --   have h₁:= collinearorder h,
  --   have h₂:= collinearorder (collinear4 (or.inr(or.inr(or.inr(or.inr(or.inl (axiom_betweennesssymmetry _ _ _ h6.1)))))) h₁.2.1 h15.1.symm),
  -- tauto,
  -- have h42: Cut A D E B G := ⟨h23.1, h39, h40, h41⟩ ,
  -- have h43: Cut A D E B F := ⟨h13, h11.2, h40, h41⟩ ,
  -- have h44: ¬ Col D E B,
  --   intro h, 
  --   have h₁:= collinearorder h,
  --   have h₂:= collinearorder (collinear4 (or.inr(or.inr(or.inr(or.inr(or.inl (axiom_betweennesssymmetry _ _ _ h6.1)))))) h₁.2.2.2.1 h15.1.symm),
  -- tauto,
  -- have h45:= (twolines h42 h43 h44).symm,
  -- subst h45,
  -- have h46:= interior5 h17.2 h17.2 (cn_congruencereflexive C M) (cn_congruencereflexive M F) h20.2.2 h26.2,
  -- tauto,
  -- end


-- lemma proposition_10 : ∀ (A B : Point), A ≠ B → ∃ X, BetS A X B ∧ Cong X A X B := 

--   begin
--   rintros _ _ h1,
--   cases proposition_01 _ _ h1 with C h2,
--   have h3: ¬ Col _ _ _ := h2.2,
--   have h4: Cong _ _ _ _ ∧ Cong _ _ _ _ := h2.1,
--   have h5:= not_eq_of_triangle h2.2,
--   rcases ⟨postulate_extension _ _ _ _ h5.2.1.symm h1, postulate_extension _ _ _ _ h5.2.2.symm h1⟩ with ⟨⟨D, h6⟩, E, h7⟩ ,
--   rcases ⟨axiom_betweennesssymmetry _ _ _ h6.1 , axiom_betweennesssymmetry _ _ _ h7.1⟩ with ⟨h8,h9⟩ ,
--   have h10: ¬ Col D C E,
--     intro h,
--     rcases collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h6.1))))) with ⟨_,_,h₁,_⟩ ,
--     rcases collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h7.1))))) with ⟨_,_,h₂,_⟩ ,
--     rcases collinearorder h with ⟨_,_,_,_,h₃⟩ ,
--     rcases ⟨bet.neq h9, bet.neq h8⟩ with ⟨⟨h₄, h₅⟩, _, h₇⟩ ,
--     have h₈:= collinear4 h₃ h₂ h₅.2,
--     rcases collinearorder h₈ with ⟨h₉,_⟩ ,
--     have h10:= collinear4 h₁ h₉ h₇.2,
--     have h11:= collinearorder h10,
--   tauto,
--   cases postulate_Pasch_inner _ _ _ _ _ h8 h9 h10 with F h11,
--   have h12: ¬ Col C E B,
--     intro h,
--     rcases collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h7.1))))) with ⟨_,_,_,h₁⟩,
--     have h₂:= bet.neq h9,
--     have h₃:= collinear4 h h₁.1 h₂.2.2.symm,
--     have h₄:=collinearorder h₃,
--     have h₅:= collinear4 h₄.2.2.2.1 h₁.2 h₂.2.1,
--   tauto,
--   rcases ⟨axiom_betweennesssymmetry _ _ _ h11.1 , axiom_betweennesssymmetry _ _ _ h11.2⟩ with ⟨h13,h14⟩ ,
--   have h15:= bet.neq h6.1,
--   have h16: ¬ Col A D C,
--     intro h,
--     have h₁: Col C B D := or.inr(or.inr(or.inr(or.inr(or.inl h6.1)))),
--     rcases ⟨collinearorder h, collinearorder h₁⟩ with ⟨ ⟨h₂⟩, h₃⟩ ,
--     have h₄:= collinear4 h₃.2.2.1 right.1 h15.2.2.symm,
--     have := collinearorder h₄, 
--   tauto,
--   cases postulate_Pasch_inner _ _ _ _ _ h13 h6.1 h16 with M h17,
--   have h18: Lt B F B E := ⟨F, h14 , cn_congruencereflexive B F⟩,
--   have h19:= bet.neq h14,
--   have h20:= (congr_flip' h4.2.symm),
--   have h21: Cong B D A E:= h6.2.trans h7.2.symm,
--   have h22:= axiom_5_line _ _ _ _ _ _ _ _ (h6.2.trans h7.2.symm).symm h20.2.2.symm (cn_equalityreverse A B) h7.1 h6.1 h20.2.2,
--   cases proposition_03 _ _ _ _ A D h19.2.2 h19.2.1 h18 h22.symm with G h23,
--   have h24: Cong G D F E:= differenceofparts h23.2 h22.symm h23.1 h14,
--   have h25:= doublereverse h24,
--   have h26:= doublereverse h23.2,
--   have h27:= doublereverse h21,
--   -- have h28:= cn_equalityreverse B A,
--   have h29:= axiom_betweennesssymmetry _ _ _ h23.1, 
--   have h30 := interior5 h11.2 (axiom_betweennesssymmetry _ _ _ h23.1) h25.1 h26.1 h27.1 (cn_equalityreverse B A),
--   have h31:= congr_flip' h26.1,
--   have h32:= doublereverse h30,
--   have h33:= congr_flip' h25.1,
--   have h34:= interior5 h14 h23.1 h31.1 h33.1 h21 (cn_equalityreverse E D),
--   have h35:= (doublereverse h22),
--   have h36:= doublereverse h35.1,
--   have h37:= bet_preserved h32.2 h36.2 h34 h13,
--   have h38:= null3 h1 h6.2.symm,
--   have h39:= axiom_betweennesssymmetry _ _ _ h37,
--   have h40: ¬ Col A D E, 
--     intro h,
--       have h₁:= collinearorder h,
--       have h₂ := collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h9))))),
--       have h₃:= bet.neq h9,
--       have h₄:= collinearorder (collinear4 h₂.1 h₁.2.2.2.1 h₃.2.1.symm),
--       have h₅ := collinearorder ( collinear4 h₂.2.2.2.1 (collinear4 h₂.1 h₁.2.2.2.1 h₃.2.1.symm) h₃.2.2),
--     tauto,
--   have h41: ¬ Col A D B, 
--     intro h,
--     have h₁:= collinearorder h,
--     have h₂:= collinearorder (collinear4 (or.inr(or.inr(or.inr(or.inr(or.inl (axiom_betweennesssymmetry _ _ _ h6.1)))))) h₁.2.1 h15.1.symm),
--   tauto,
--   have h42: Cut A D E B G := ⟨h23.1, h39, h40, h41⟩ ,
--   have h43: Cut A D E B F := ⟨h13, h11.2, h40, h41⟩ ,
--   have h44: ¬ Col D E B,
--     intro h, 
--     have h₁:= collinearorder h,
--     have h₂:= collinearorder (collinear4 (or.inr(or.inr(or.inr(or.inr(or.inl (axiom_betweennesssymmetry _ _ _ h6.1)))))) h₁.2.2.2.1 h15.1.symm),
--   tauto,
--   have h45:= (twolines h42 h43 h44).symm,
--   subst h45,
--   have h46:= interior5 h17.2 h17.2 (cn_congruencereflexive C M) (cn_congruencereflexive M F) h20.2.2 h26.2,
--   tauto,
--   end



lemma planeseparation {A B C D E : Point} :
   SS C D A B → OS D A B E → OS C A B E := sorry 

lemma diagonalsmeet {A B C D : Point} :
   PG A B C D → ∃ X, BetS A X C ∧ BetS B X D :=sorry 


-- @[simp]lemma samenotopposite {A B C D : Point} : SS A B C D → ¬ OS A C D B :=sorry 

lemma samenotopposite {A B C D : Point} : SS A B C D → ¬ OS A C D B :=sorry 

lemma proposition_12 : ∀ (A B C : Point), ¬ Col A B C → ∃ X, Perp_at C X A B X := 
begin
  rintros _ _ _ h1,
  have h2: A ≠ B ∧ B ≠ C,
    refine ⟨ _,_⟩,
      {intro h, 
      have:= (or.inl h), 
      tauto
      },
      {intro h,
      have := or.inr(or.inr(or.inl h)), 
      tauto,
      },
  cases postulate_extension _ _ _ _ h2.2.symm h2.2.symm with E h3,  
  rcases bet.neq h3.1 with ⟨ h4, h5⟩, 
  cases postulate_Euclid3 _ _ h5.2 with K h10,
  have h11: InCirc B K := ⟨_ ,_, _ ,_, E, h10, (or.inr(⟨h3.1, (cn_congruencereflexive C E), (cn_congruencereflexive C B)⟩))⟩,
  rcases postulate_line_circle _ _ _ K _ _ h10 h11 h2.1 with ⟨P, Q , h12⟩,
  have h13:= (axiom_circle_center_radius _ _ _ K _ h10 h12.2.2.1).trans,
  have h14:= (axiom_circle_center_radius _ _ _ K _ h10 h12.2.2.2.1).symm,
  rcases ⟨congr_flip' (h13 h14), bet.neq (h12.2.2.2.2)⟩ with ⟨⟨ h16, _⟩, ⟨_,h17⟩⟩,
  cases proposition_10 _ _ h17.2 with M h18,
  cases congr_flip' h18.2 with h19,
  have h20: Col P M Q := (or.inr(or.inr(or.inr(or.inr(or.inl h18.1))))),
  have h21: Col P B Q := (or.inr(or.inr(or.inr(or.inr(or.inl  h12.2.2.2.2))))),
  rcases ⟨collinearorder h20, collinearorder h21⟩ with ⟨⟨h22, h23⟩, h24, h25⟩,
  rcases collinearorder ((or.inr(or.inr(or.inr(or.inr(or.inl h12.2.1)))))) with ⟨h27⟩ ,
  have h28:= collinear4 Q (collinear4 P h25.2.2.1 h23.2.2.1 h17.2) right_2.2.2.2 left.symm,
  rcases collinearorder h28 with ⟨ _, h29 ⟩,
  have h30: M ≠ C,
    intro h, 
    have h2:= h.symm,
    subst h2, 
    tauto,
  use [M , P, (or.inr(or.inr(or.inl ⟨M⟩))), h29.2.1 ,h12.1, (⟨ _, h18.1, h19, h16, h30⟩)], 

end 


lemma notperp : ∀ {A B C P : Point},
BetS A C B → ¬Col A B P → ∃ X, ¬Col A B X ∧ SS X P A B ∧ ¬ Per A C X := sorry 


lemma proposition_07 : ∀ (A B C D : Point), 
A ≠ B → Cong C A D A → Cong C B D B → SS C D A B → C = D := sorry

  -- begin
  -- rintros _ _ _ _ h1 h2 h3 ⟨U, V, u, h4⟩,
  -- have h5: ¬Col A B C := h4.2.2.2.2.1,
  -- rcases proposition_12 _ _ _ h5 with ⟨F , H, h6⟩, 
  -- have h7: C ≠ F,
  --   intro h,
  --   subst h,
  --   tauto,
  -- cases postulate_extension _ _ _ _ h7 h7.symm with E h8,
  -- have h9: Cong A C A E,
  -- by_cases (A = F),
  --   {subst h,
  --   use h8.2.symm,},
  --   have h9: Col H F A := collinearreverse (collinear4 (collinear1 h6.2.1) (collinear1 h6.2.2.1) h1.symm),
  --   have h10: Per A F C := collinearright h6.2.2.2 h9 h,
  --   cases T8_2 h10 with P h11,
  --   have h12: E = P := extensionunique h8.1 h11.1 ((h8.2.flipR).trans (h11.2.1.flipR)),
  --   subst h12,
  --   use h11.2.2.1.flipLR,
  -- have h10: Cong B C B E,
  -- by_cases (B = F),
  -- {subst h,
  --   use h8.2.symm,},
  -- {have h9: Col H F B := collinearreverse (collinear4 (h6.2.1) (h6.2.2.1) h1),
  --   have h10:= collinearright h6.2.2.2 h9 h,
  --   cases T8_2 h10 with P h11,
  --   have h12: E = P := extensionunique h8.1 h11.1 ((h8.2.flipR).trans ( h11.2.1.flipR)),
  --   subst h12,
  --   use h11.2.2.1.flipLR,},
  --   have h10a:= (samesidesymmetric ⟨U, V, u, h4⟩).1,
  --   have h11: OS C A B E, unfold OS, use F, tauto,
  --   have h12: OS D A B E := planeseparation h10a h11, 
  --   cases h12 with G h12,
  --   have h13: Cong D A A E := ((h2.flipL).symm.trans h9),
  --   have h14: Cong A D A E := h13.flipL,
  --   have h15:= (h3.symm.flipLR).trans h10,
  --   have h16:  Cong G D G E, 
  --   cases h12.2.1, 
  --   tauto,
  --     cases_type* or,
  --     repeat {subst' h, 
  --   tauto},
  --   have h₁ : Cong D G E G := axiom_5_line _ _ _ _ _ _ _ _ (cn_congruencereflexive A G) h15 h14 h h (cn_congruencereflexive B A),
  --   use h₁.flipLR,
  --   have h₁ : Cong D G E G := axiom_5_line _ _ _ _ _ _ _ _ (cn_congruencereflexive B G) h14 h15 h h (cn_congruencereflexive A B),
  --   use h₁.flipLR,
  --   use interior5 h h (cn_congruencereflexive A G) (cn_congruencereflexive G B) h14 h15,  
  --   have h17: F = G, 
  --     by_cases (A = G),
  --       have h₁ := axiom_betweennesssymmetry _ _ _ h12.1,
  --       have h₂: G ≠ B,
  --         intro hEq,
  --         subst h,
  --         tauto,
  --       have h₃: Per E G B := ⟨D, h₁, ((h16).symm.flipLR), ( (h15)).symm.flipLR, h₂⟩,
  --       have h₁: F ≠ B,
  --       { intro hEq,
  --         have h1a:= hEq.symm,
  --         subst h,
  --         have h₄: Per B A E := T8_2 h₃,
  --         subst h1a,
  --         have h₅: Per E B A := ⟨C, (axiom_betweennesssymmetry _ _ _ h8.1), ( h8.2.flipLR), ( (h9).flipLR).symm, h₂.symm⟩,
  --         have h₆: Per A B E := T8_2 h₅,
  --         cases postulate_extension _ _ _ _ h₂.symm h₂ with J h₇,
  --         have h₈: Per E B J := T8_3 h₅ (ray4 (or.inr(or.inr h₇.1)) h₂.symm),
  --         have h₉:= T8_2 h₈,
  --         have h10b: Col B A J, by collinear_tac,
  --         have h10c: Col J A B, by collinear_tac,
  --         have h11: Per J A E := collinearright h₄ h10b ((bet.neq h₇.1).1.symm),
  --         have := droppedperpendicularunique h11 h₉ h10c,
  --         tauto,
  --       },
  --       {
  --         have h17: Per E F B := ⟨C, (axiom_betweennesssymmetry _ _ _ h8.1), ( h8.2.flipLR), ( (h10).flipLR).symm, h₁⟩,
  --       have h18:= T8_2 h17,
  --       have h19:= T8_2 h₃,
  --       have h20: Col B G F, by collinear_tac,
  --       have h21: G = F := droppedperpendicularunique h19 h18 h20,
  --     tauto!,
  --     },
  --       have : F ≠ G,
  --       by_cases h1a : (A = F),  
  --       subst h1a,
  --         have h21: B ≠ G, 
  --           intro h,
  --           subst h,
  --           have h₁ := axiom_betweennesssymmetry _ _ _ h12.1,
  --           have h₃: Per E B A:= ⟨D, h₁, ( (h16).symm.flipLR), ( (h14)).symm.flipLR, h1.symm⟩,
  --         -- have h₁: F ≠ B,
  --         -- intro hEq,
  --       -- have h1a:= hEq.symm,
  --       -- subst h,
  --           have h₄: Per A B E := T8_2 h₃,
  --           have h₅: Per E A B, unfold Per, use C, simp*, use [(axiom_betweennesssymmetry _ _ _ h8.1), (h8.2.flipLR), (h10.reverse)],
  --       -- subst h1a,
  --     have h₆: Per E B A := ⟨D, (axiom_betweennesssymmetry _ _ _ h12.1), (h16.reverse), (h14.reverse), h1.symm⟩,
  --     -- have h₆: Per A B E := T8_2 h₅,
  --         cases postulate_extension _ _ _ _ (h) h with K h₇,
  --         -- have h₈: Per B A E := T8_3 h₅ (ray4 (or.inr(or.inr h₇.1)) h),
  --         have h9a: Per E A B, unfold Per, use C, simp*, use [(axiom_betweennesssymmetry _ _ _ h8.1), (h8.2.flipLR), (h10.reverse)],
  --         have h8a: Out A B K := (ray4 (or.inr(or.inr h₇.1)) h),
  --         have h8b: Per E A K := T8_3 h9a h8a,
  --         have h9b:= T8_2 h8b,
  --         have h12a:=  T8_2 h9a,
  --         have h10b: Col A B K, by collinear_tac,
  --         have h10c: Col K B A, by collinear_tac,
  --         have h11: Per K B E := collinearright h₄ h10b ((bet.neq h₇.1).1.symm),
  --         have h12: B = A := droppedperpendicularunique h11 h9b h10c,
  --       tauto,
  --       assumption,
  --       have h₁: Col B A F, by collinear_tac,
  --       have h₂: Col B A G, by collinear_tac,
  --       have h₃: Col A F G := collinear4 h₁ h₂ h1.symm,
  --       have h₄: Per E F A, unfold Per, use C, use [(axiom_betweennesssymmetry _ _ _ h8.1), (h8.2.flipLR) , h9.reverse, (ne.symm h1a)],
  --       have h₅:= T8_2 h₄,
  --       have h₆: Per E G A, unfold Per, use [D, (axiom_betweennesssymmetry _ _ _ h12.1), (h16.reverse), (h14.reverse), (ne.symm h)],
  --       have h₇:= T8_2 h₆,
  --       have h₈: F = G := droppedperpendicularunique h₅ h₇ h₃,
  --       subst_vars,
  --       simp*,
  -- end 



lemma eq_implies_out {A B : Point} : (B = B) ∧ (A ≠ B) → (Out A B B) := 
  begin
  rintros ⟨h,h1⟩, use (ray4 (or.inr(or.inl h)) h1),
  end 

lemma proposition_08 : ∀ (A B C D E F : Point),
Triangle A B C → Triangle D E F → Cong A B D E → Cong A C D F → Cong B C E F →
CongA B A C E D F ∧ CongA C B A F E D ∧ CongA A C B D F E := 
begin
  introv h1 h2 h3 h4 h5,
  rcases ⟨not_eq_of_triangle h1, not_eq_of_triangle h2⟩ with ⟨⟨h6, h7, h9⟩,⟨h8, h11, h10⟩⟩,
  have h12: ¬Col B A C ∧ ¬ Col C B A ∧ ¬ Col A C B, 
  refine ⟨ _ , _ , _ ⟩ ,
    {intro h, rcases collinearorder h, contradiction,},
    repeat {intro h, rcases collinearorder h, tauto}, 
  rcases ⟨congr_flip' h3, congr_flip' h4, congr_flip' h5⟩ with ⟨⟨ ⟩, ⟨h14,h15⟩, h16⟩,
use [⟨_, _, _, _, eq_implies_out ⟨⟨B⟩ ,h6⟩, eq_implies_out ⟨⟨C⟩ , h9⟩, 
eq_implies_out ⟨⟨E⟩ ,h8⟩, eq_implies_out ⟨⟨F⟩ ,h10⟩, h3, h4, h5, h12.1⟩,
 ⟨_ , _, _, _, eq_implies_out ⟨⟨C⟩, h7⟩, eq_implies_out ⟨⟨A⟩,h6.symm⟩,
 eq_implies_out⟨⟨F⟩, h11⟩, eq_implies_out ⟨⟨D⟩, h8.symm⟩, h5, left, h14, h12.2.1⟩,
 ⟨_ , _, _, _, eq_implies_out ⟨⟨A⟩, h9.symm⟩, eq_implies_out⟨⟨B⟩ , h7.symm⟩,
 eq_implies_out ⟨⟨D⟩, h10.symm⟩, eq_implies_out ⟨ ⟨E⟩, h11.symm⟩, h14, h16.1, h3, h12.2.2⟩],

end 

 

lemma proposition_09 : ∀ (A B C : Point),
¬ Col B A C → ∃ X, CongA B A X X A C ∧ InAngle B A C X := 

begin 
  introv h,
  have h2: A ≠ B, intro h, have h: Col B A C := or.inl h.symm, contradiction,
  have h3: A ≠ C, intro h, have h: Col B A C := or.inr(or.inr(or.inl h)), contradiction,
  cases layoff h3 h2 with E,
  have h4: B ≠ E, 
    intro h₁, 
    have h: Col A B E := or.inr(or.inr(or.inl h₁)),
    have h2:= rayimpliescollinear h_1.1, 
    rcases collinearorder h with ⟨_, _, h3,_⟩ , rcases collinearorder h2 with ⟨_, _, h4,_⟩,
    have h6:= collinear4 E h3 h4 (raystrict  h_1.1).symm, 
    rcases collinearorder h6 with ⟨_⟩ , 
    contradiction,
  cases proposition_10 _ _ h4 with F h5,
  rcases doublereverse  h5.2.symm,
  have h7: ¬Col B A F, 
    intro h, 
    have h2: Col B F E := or.inr(or.inr(or.inr(or.inr(or.inl h5.1)))),
    rcases collinearorder h2 with ⟨ _⟩ , rcases collinearorder h with ⟨ _ , _ ,_, _⟩ ,
    rcases bet.neq h5.1 with ⟨ _,_⟩,
    have h8:= collinear4 F left_1 right_2_right_left right_2.1.symm,
    have h9:= rayimpliescollinear  h_1.1,
    rcases collinearorder h8 with ⟨_⟩ , rcases collinearorder h9 with ⟨ _ ⟩ ,
    have h11:= collinear4 E right_3.1 right_4.2.1 (raystrict  h_1.1).symm, 
    rcases collinearorder h11, 
    contradiction,
  have h12:= ray4 (or.inr (or.inl ⟨B⟩)) h2,
  have h13: A ≠ F, 
    intro h, 
    have h2: Col B A F := or.inr(or.inr(or.inl h)), 
    contradiction,
  have h14:= ray4 (or.inr (or.inl ⟨F⟩)) h13,
  have h15: CongA _ _ _ _ _ _:= ⟨ _, _, _, _, h12, h14, h_1.1, h14, h_1.2.symm, (cn_congruencereflexive A F), left, h7⟩ ,
    rcases ( h15.symm) with ⟨v, u, V ,U ,h17,h18,h19,h20,h21⟩,
    have h19:= h15.trans (ABCequalsCBA h21.2.2.2),
    have h20: InAngle B A C F := ⟨ _, _, h12, h_1.1,h5.1⟩, 
    tauto,

end 

lemma proposition_11 : ∀ (A B C : Point), BetS A C B → ∃ X, Per A C X := 

begin 
introv h, 
rcases bet.neq h,
cases postulate_extension _ _ _ _ right.1 right.1 with E h2,
rcases bet.neq h2.1 with ⟨_, h4⟩, 
rcases proposition_01 _ _ h4.2 with ⟨F, ⟨⟨_, h5⟩⟩⟩,
have h9: C ≠ F, 
  intro h12, 
  have:= or.inr(or.inr(or.inr(or.inr(or.inl h2.1)))),
  rcases collinearorder this with ⟨_,_,_, h13, h14⟩, subst' h12, tauto,
  rcases ⟨congr_flip' h2.right.symm , congr_flip' h5.symm⟩ with ⟨h16 ,⟨h17⟩⟩,
  use [F, E ,h2.1, h16.2.2 ,right_1.1],
end 

lemma pointreflectionisometry : ∀ {A B C P Q : Point},
Midpoint A B C → Midpoint P B Q → Cong A P C Q := sorry 


lemma proposition_11b (A B C P : Point): BetS A C B → ¬Col A B P → ∃ X, 
Per A C X ∧ OS X A B P := 
  
begin 
  introv h1 h2, 
cases notperp h1 h2 with M h3,
rcases proposition_12 _ _ _ h3.1 with ⟨Q, ⟨E, h4⟩⟩, 
  have h5: M ≠ Q,
  {
    intro h,
    subst h, 
  tauto
  },
have h6:= T8_2  h4.2.2.2, 
have h7: Col A B C , by collinear_tac,
have h8: Col B A E, by collinear_tac,
have h9: Col B A C, by collinear_tac,
-- rcases ⟨collinearorder h4.2.2.1, collinearorder h7⟩ with ⟨⟨_,h8⟩,_,⟨_,h10⟩⟩,  
have h10:= bet.neq h1,
have h11:= T8_2 h6,
have h12: C ≠ Q,
  intro h,
  subst' h,
  --have : Col A E C , by collinear_tac,
  --rcases collinearorder this with ⟨_, h2⟩ ,
  have h13: Col A E C:= collinear4 B h8 h9 h10.2.2.symm,
  have h14: Col E C A, by collinear_tac,
  have: Per A C M := collinearright h4.2.2.2 h14 h10.2.1,
  tauto!,
have h13: Col C Q E := collinear5 h10.2.2 h12 h7 h4.2.1 h4.2.2.1,
rcases collinearorder h13 with ⟨_, h14⟩ ,
have h15: Per C Q M := collinearright h4.2.2.2 h14.2.2.2 h12, 
cases proposition_10 _ _ h12.symm with G h16,
have h17: M ≠ G, 
  intro h, subst h,
  have h₁: Col Q C M , by collinear_tac,
  have h₂: Col B Q C := collinear4 A h4.2.1 h7 h10.2.2,
  have h₃: Col Q C B, by collinear_tac,
  -- rcases ⟨collinearorder h₁, collinearorder h₂⟩ with ⟨ ⟨ _,h₃⟩ , ⟨ _,h₄⟩ ⟩ ,
  have h₅: Col C M B := collinear4 Q h₁ h₃ h12.symm,
  have h₆: Col C B A,  by collinear_tac,
  have h₇: Col C B M, by collinear_tac,
  have h₈: Col B M A := collinear4 C h₇ h₆ h10.1,
  have : Col A B M , by collinear_tac,
  tauto,
cases postulate_extension _ _ _ _ h17 h17 with H h18, 
have h19 : Midpoint M G H := ⟨h18.1 , h18.2.symm⟩,
rcases congr_flip' h16.2 with ⟨h20, h21⟩ , 
have h21 : Midpoint Q G C:= ⟨h16.1, h21.1⟩,
have h22: Col C Q G, by collinear_tac,
have h23:= bet.neq  h16.1 ,
have h25: Per G Q M:= collinearright h15 h22 h23.2.1.symm,
cases postulate_extension _ _ _ _ h5 h5 with J h26,
have h27:= T8_2 h25,
have h28:= rightreverse h27 h26.1 h26.2.symm,
have h29:= axiom_betweennesssymmetry _ _ _ h26.1, 
rcases congr_flip' h26.2 with ⟨_,h30⟩, 
have h31: Per J Q G := ⟨ M, h29, h30.1, h28.symm, h23.2.1 ⟩ ,
have h32: J ≠ G,
  intro h,
   have h₁: Col J Q G , by collinear_identity,
   have h₂: ¬Col J Q G := rightangleNC h31,
   tauto,
cases postulate_extension _ _ _ _ h32 h32 with K h33,
have h34 : Midpoint J G K:= ⟨h33.1, h33.2.symm⟩,
have h35:= pointreflectionisometry h34 h21,
have h36:= pointreflectionisometry h19 h21, 
have h37:= pointreflectionisometry h21 h19,
have h38:= pointreflectionisometry h21 h34,
have h39:= pointreflectionisometry h19 h34,
have h40: BetS H C K:= bet_preserved h36 h39 h38 h26.1,
rcases ⟨congr_flip' h18.2 , congr_flip' h28⟩ with ⟨h41,h42⟩,
have h43:= h41.1.trans h42.2.1,
have h44:= h43.trans (h33.2.symm), 
rcases congr_flip' h44 with ⟨_, h45⟩ ,
have h47: Cong H C Q J := (h36.symm).trans (doublereverse left_1).1, 
have h48: Cong H C K C := (h47.trans h38).flipR,
have h49: Per H C G , unfold Per, use K, simp*, tauto!,
have h50:= T8_2 h49,
have h51: Col Q C G, by collinear_tac,
have h52: Col G C C, by collinear_identity,
have h53: Col A B A, by collinear_identity,
have h54: Col Q C A := collinear5 h10.2.2 h12.symm h4.2.1 h7 h53,
have h55: Col C A G := collinear4 Q h54 h51 h23.2.2,
have h56: Col G C A, by collinear_tac,
have h57: Per A C H := collinearright h50 h56 h10.2.1,
have h58: Col C A B, by collinear_tac,
have h59: Col A G B:= collinear4 C h55 h58 h10.2.1.symm,
have h60: Col A B G, by collinear_tac,
have h61:= bet.neq h18.1,
have h62: ¬ Col A B H, 
  intro h,
  have h₁: Col B G H := collinear4 A h60 h h10.2.2,
  have h₂: Col G H M, by collinear_tac,
  have h₃: Col G H B, by collinear_tac, 
  have h₄: Col H M B := collinear4 G h₂ h₃ h61.1,
  have h₅: Col H B A, by collinear_tac,
  have h₆: Col H B M, by collinear_tac,
  have h₇: Col A B M,
  by_cases (B=H),
    {
      subst h ,
      have h₁: Col G B M, by collinear_tac,
      have h₂: Col G B A, by collinear_tac, 
      have h₃:= bet.neq h18.1,
      have h₄: Col B M A := collinear4 G h₁ h₂ h61.1,
      by collinear_tac,
    },
    { have h₁: B ≠ H := h,
      have h₁: Col B A M := collinear4 H h₅ h₆ (h₁.symm),
      by collinear_tac,
     },
tauto,
have h63: OS H A B M , unfold OS, use [G], simp*, use [axiom_betweennesssymmetry _ _ _ h18.1 ],
have h64: SS P M A B:= (samesidesymmetric h3.2.1).1,
have h65: OS M A B H, unfold OS, use [G], simp*,
have h66: OS P A B H := planeseparation h64 h65,
have h67: OS H A B P := oppositesidesymmetric h66,
use [H], simp*,
--change OS to SS and change TS to OS
end 

lemma proposition_13 (A B C D : Point): 
BetS D B C → ¬Col A B C → RT C B A A B D := 

begin
  introv h1 h2, 
  rcases NCdistinct h2 with ⟨_,_,_ ,h5⟩,
  have h6:= ray4 (or.inr(or.inl ⟨A⟩)) h5.1,
  have h7: Supp  C B A A D := ⟨ h6, (axiom_betweennesssymmetry _ _ _ h1)⟩,
  rcases NCorder h2 with ⟨_,_,h8⟩,
  rcases ⟨collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h1))))), bet.neq h1⟩ with ⟨⟨_,_,h9⟩, ⟨_,h10⟩⟩,
  have h11: ¬Col D B A := NChelper h8.2.2 h9.2.2 (or.inr(or.inr(or.inl ⟨B⟩))) h10.1,
  rcases NCorder h11 with ⟨_,_ ,h13⟩,
  use [C , B, D , A , A , h7, eq_anglesrefl h8.2.2, eq_anglesrefl h13.2.2],

end 

lemma proposition_14 (A B C D E : Point): RT A B C D B E → Out B C D → OS E D B A →
   Supp A B C D E ∧ BetS A B E := 
  
begin 
  rintros ⟨a,b,e,c,d,h⟩ h1 h2,
  rcases ⟨ h.2.1.symm,  h.2.2.symm⟩ with ⟨h3, h4⟩,
  rcases ⟨ NCdistinct ( h3.NC), NCdistinct ( h4.NC)⟩ with ⟨⟨h8,_⟩ , h22, h9, _⟩ ,
  cases postulate_extension _ _ _ _ h8 h9 with T h10,
  have h13:= h.2.2.trans (supplements h3 h.1 ⟨h1, h10.1⟩),
  have h15: Col A B T , by collinear_tac,
  rcases bet.neq h10.1 with ⟨h16,_⟩ ,
  have h17: Col A B B, by collinear_identity,
  rcases ⟨NCorder (NChelper ( h3.NC) h15 h17 h16.symm), rayimpliescollinear h1⟩ with ⟨⟨_ , h19⟩, h20⟩,
  rcases collinearorder h20 with ⟨_,_,h21⟩ ,
  have h23: Col C B B , by collinear_identity,
  have h24: ¬Col D B T:= NChelper h19.2.2.2 left_1 h23 h22,
  have h25:= proposition_04 _ _ _ _ _ _ (cn_congruencereflexive B D) h10.2 ( h13.symm),
  rcases ⟨congr_flip' h25.1, congr_flip' h10.2⟩  with ⟨⟨h26,_⟩,h27,_⟩ ,
  have h28: Col D B B , by collinear_identity,
  cases oppositesidesymmetric h2 with m h29,
  rcases ⟨axiom_betweennesssymmetry _ _ _ h10.1, axiom_betweennesssymmetry _ _ _ h29.1⟩ with ⟨h30, h31⟩ ,
  have h32: SS _ _ _ _ := ⟨A, B, m, h28, h29.2.1, h30, h31, h24, ( h4.NC)⟩,
  have h33 := proposition_07 _ _ _ _ h22 h26 h27 h32,
  subst' (h33), 
  use [h1, h10.1, h10.1],
end 

lemma proposition_15 (A B C D E : Point): 
   BetS A E B → BetS C E D → ¬Col A E C → CongA A E C D E B ∧ CongA C E B A E D := 

   begin
    introv h1 h2 h3,
    rcases ⟨bet.neq h1, bet.neq h2⟩ with ⟨h4, h5⟩,
    have h6 : ¬ Col B E D,
      intro h,
        have h₁: Col B E A , by collinear_tac, 
        have h₄: Col D E C , by collinear_tac,
        have h₆:= collinearorder (collinear4 D (collinearorder (collinear4 B h h₁ h4.1.symm)).1 h₄ h5.1.symm),
      tauto,
      have h7:= ray4 (or.inr(or.inl ⟨D⟩)) h5.1,
      have h8:= ray4 (or.inr(or.inl ⟨B⟩)) h4.1,
      rcases ⟨axiom_betweennesssymmetry _ _ _ h1, (axiom_betweennesssymmetry _ _ _ h2)⟩ with ⟨h9, h10⟩,
      have h14: ¬ Col A E D,
        intro h,
        have h₁: Col A E B, by collinear_tac,
        have h₃:= collinearorder (collinear4 A h h₁ h4.2.1),
      tauto,
      have h16: ¬ Col B E C,
        intro h, 
        have h₁:= collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h1))))),
        have h₃:= collinearorder (collinear4 B h h₁.2.2.2.2 h4.1.symm),
      tauto,
      have h21:= ((ABCequalsCBA h14).trans ((supplements (ABCequalsCBA h6) (⟨h7, h9⟩) (⟨h8, h10⟩)).trans (ABCequalsCBA h16))).symm,
      have h22: E ≠ C,
        intro h,
        have : Col B E C := (or.inr(or.inr(or.inl h))),
      tauto,
      have h29:= (supplements (ABCequalsCBA h16) (⟨(ray4 (or.inr(or.inl ⟨C⟩)) h22), h9⟩) (⟨h8, h2⟩)).trans (ABCequalsCBA h6),
      have h30:= (ABCequalsCBA h3).trans h29,
      tauto,

    end 

  lemma proposition_15a : ∀ (A B C D E : Point),
  BetS A E B → BetS C E D → ¬ Col A E C → CongA A E C D E B :=

  begin 
    rintros _ _ _ _ _ h1 h2 h3,
    have h1:= proposition_15 A B C D E h1 h2 h3,
    tauto,
  end 
      
lemma proposition_15b : ∀ (A B C D E : Point),
  BetS A E B → BetS C E D → ¬ Col A E C → CongA C E B A E D :=
  begin
    rintros _ _ _ _ _ h1 h2 h3, 
    have h1:= proposition_15 A B C D E h1 h2 h3,
    tauto,
  end 

lemma proposition_16: ∀ (A B C D : Point),
   Triangle A B C → BetS B C D → LtA B A C A C D ∧ LtA C B A A C D := sorry 

lemma proposition_17 : ∀ (A B C : Point),
   Triangle A B C → ∃ X Y Z, SumA A B C B C A X Y Z := 

   begin
    rintros _ _ _ h1,
    have h2:= not_eq_of_triangle h1,
    cases postulate_extension _ _ _ _ h2.2.1 h2.2.1 with D h4,
    have h7: Col B C B , by collinear_identity,
    have h15: Col B C D , by collinear_tac,
    have h8:= NChelper (NCorder (h1)).2.1 h7 h15 (bet.neq h4.1).2.2,
    have h9:= NCorder h8,
    have h10:= proposition_16 _ _ _ _ h1 h4.1,
    have h11:= ABCequalsCBA (h1),
    rcases angleorderrespectscongruence2 h10.2 h11 with ⟨a,e,d,h12⟩,
    rcases ⟨ray5 h12.2.1, ray5 h12.2.2.1⟩ with ⟨h13, h14⟩ ,
    have h16: Col B C C , by collinear_identity,
    have h17:= NChelper (NCorder (h1)).2.1 h16 h15 (bet.neq h4.1).1,
    have h18: Col C D C, by collinear_identity,
    have h28:= collinearorder (rayimpliescollinear h13),
    cases crossbar (NCorder (NChelper (NCorder (NChelper h17 (collinearorder (rayimpliescollinear h14)).2.2.2.1 h18 (ray2 h14).symm)).2.1 (or.inr(or.inl ⟨C⟩)) h28.2.2.2.1 (ray2 h13))).1 h12.1 h13 h14 with E h32,
    have h34a: Col A E D , by collinear_tac,
    have h34:= collinearorder h34a,
    have h36:= NChelper (NCorder h17).2.1 h34.2.2.1 (or.inr(or.inr(or.inl ⟨A⟩))) (bet.neq h32.2).2.1.symm,
    have h42:= NChelper (NCorder h36).2.2.1 (or.inr(or.inl ⟨C⟩)) (collinearorder (rayimpliescollinear h32.1)).2.2.2.1 (ray2 (ray5 (ray5 h32.1))),
    have h44:= NChelper (NCorder h42).2.2.1 h28.2.2.1 (or.inr(or.inr(or.inl ⟨C⟩))) (ray2 h13).symm,
    have h49:= equalangleshelper (eq_anglesrefl ((NCorder h42)).2.2.1) (ray5 h13) (ray4 (or.inr(or.inl ⟨e⟩)) ((ray2 (ray5 (ray5 h32.1))))),
    cases postulate_Pasch_inner _ _ _ _ _ h32.2 h4.1 h9.2.2.2.2 with F h52,
    rcases ⟨collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h52.1))))), collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h52.2)))))⟩ with ⟨h53, h54⟩ ,
    rcases ⟨(axiom_betweennesssymmetry _ _ _ h52.1), (axiom_betweennesssymmetry _ _ _ h52.2)⟩ with ⟨h55, h56⟩,
    have h64:= equalangleshelper (eq_anglesrefl (NCorder h36).2.2.2.1) (ray4 (or.inr(or.inl ⟨E⟩)) (NCdistinct (NCorder h36).2.2.2.1).2.2.2.1) ((ray4 (or.inl h55) h2.2.2.symm)),
    have h65:= ((h12.2.2.2.trans h49).trans (equalangleshelper (eq_anglesrefl h44) h13 (ray5 (ray5 h32.1)))).trans ((ABCequalsCBA (NCorder h36).2.1).trans h64),
    have h67:= equalangleshelper (eq_anglesrefl (NCorder (h1)).2.1) (ray4 (or.inr(or.inl ⟨B⟩)) (bet.neq h4.1).2.1.symm) ((ray4 (or.inl h55) h2.2.2.symm)),
    have h70:= (h67).trans (ABCequalsCBA (NCorder (NChelper (NCorder (h1)).2.2.1 h53.2.2.1 (or.inr(or.inl ⟨C⟩)) (bet.neq h52.1).1)).2.2.2.2),
    use [E, C, B, F], 
    tauto,
    
   end 

lemma proposition_18 : ∀ (A B C : Point),
   Triangle A B C → Lt A B A C → LtA B C A A B C :=

  begin
    rintros _ _ _ h1 h2,
    have h3:= not_eq_of_triangle h1,
    cases proposition_03 _ _ _ _ _ _ h3.2.2 h3.1 h2 (cn_congruencereflexive A C) with D h4,
    have h5: ¬ Col B C D,
      intro h,
      have h₁:= collinearorder h,
      have h₂:= bet.neq h4.1,
      have h2a: Col A D C , by collinear_tac,
      have h₃:= (collinearorder h2a),
      have h₄:= collinear4 D h₁.2.2.2.2 (h₃.2.1) h₂.1,
      have h₅:= collinearorder h₄,
    tauto,
    have h6:= axiom_betweennesssymmetry _ _ _ h4.1,
    have h7:= proposition_16 _ _ _ _ (h5) h6,
    have h8: ¬ Col A D B,
      intro h, 
      have h₁:= collinearorder h,
      have h₂:= bet.neq h4.1,
      have h2a: Col A D C , by collinear_tac,
      have h₃:= (collinearorder(or.inr(or.inr(or.inr(or.inr(or.inl h4.1)))))),
      have h₄:= collinear4 D h₁.1 (h₃.1) h₂.2.1.symm,
      have h₅:= collinearorder h₄,
    tauto,
    have h9: isosceles _ _ _ := ⟨h8, h4.2⟩,
    have h10:= proposition_05 _ _ _ h9,
    have h11:= bet.neq h6,
    have h12:= ray4 (or.inr(or.inr h6)) h11.2.1,
    have h13:= ray5 h12,
    have h14: Out C B B := ray4 (or.inr(or.inl ⟨B⟩)) h3.2.1.symm,
    have h15: ¬ Col A C B,
    intro h,
    have h₁:= collinearorder h,
    tauto,
    have h16:= NCorder h15,
    have h17:= eq_anglesrefl h15,
    have h18:= equalangleshelper h17 h13 h14,
    have h19:= angleorderrespectscongruence2 h7.2 h18,
    have h20:= NCorder h8,
    have h21: CongA A D B B D A := ABCequalsCBA h8,
    have h23: LtA A C B A B D := angleorderrespectscongruence (angleorderrespectscongruence h19 h21) h10.symm,
    have h24: CongA B C A A C B := ABCequalsCBA h16.2.2.2.2,
    have h25: LtA B C A A B D := angleorderrespectscongruence2 h23 h24,
    have h26: CongA A B D A B D := eq_anglesrefl h20.2.2.2.1,
    have h27 : LtA _ _ _ _ _ _ := ⟨A, D, C, h4.1, (ray4 (or.inr(or.inl ⟨A⟩)) h3.1.symm), (ray4 (or.inr(or.inl ⟨C⟩)) h3.2.1), h26⟩,
    use [angleordertransitive h25 h27],
    
  end 


/--In any triangle the greater angle is subtended by the greater side.-/

lemma proposition_19 (A B C : Point) : Triangle A B C → LtA B C A A B C → Lt A B A C := 

   begin
   rintros h1 h2,
   have h3:= NCorder h1,
   have h4: ¬ Cong A C A B,
    intro hEq,
    have h₅:= angleorderrespectscongruence h2 ((ABCequalsCBA h3.2.1).trans ((proposition_05 _ _ _ (⟨h1, hEq.symm⟩)).symm)),
    have h₆ := angletrichotomy (angleorderrespectscongruence h2 (((ABCequalsCBA h3.2.1).trans ((proposition_05 _ _ _ (⟨h1, hEq.symm⟩)).symm)))),
    tauto,
    have h5: ¬ Lt A C A B,
      intro hEq,
      have h:= proposition_18 _ _ _ h3.2.2.2.1 hEq,
      have := angletrichotomy ((angleorderrespectscongruence (angleorderrespectscongruence2 h (ABCequalsCBA h1))) (ABCequalsCBA h3.2.1)),
      tauto,
      have h6:= not_eq_of_triangle h1,
        have h7: ¬ ¬ Lt A B A C,
        intro hEq,
        have h:= (trichotomy1 hEq h5 h6.1 h6.2.2).symm,
        tauto,
        use of_not_not h7,
   end 

lemma proposition_20 : ∀ (A B C : Point), Triangle A B C → TG B A A C B C :=
  begin
    rintros _ _ _ h1,
    have h2: A ≠ B ∧ B ≠ C ∧ A ≠ C := not_eq_of_triangle h1,
    cases postulate_extension _ _ _ _ ((h2.1).symm) ((h2.2.2).symm) with D h3,
    rcases ⟨bet.neq h3.1, congr_flip' h3.2⟩ with ⟨h4,h5⟩,
    have h6: ¬ Col A D C ,
      intro h,
      have h1: Col D A B, by collinear_tac,
      have h2: Col D A C, by collinear_tac,
      have h3:= collinear4 D h1 h2 h4.1.symm,
      tauto,
    have h7:= NCorder h6,
    have h8: C ≠ D,
      intro h,
      have h₁: Col A D C := or.inr(or.inr (or.inl h.symm)),
      tauto,
    have h9:= proposition_05 _ _ _ ⟨h6 , h5.2.2⟩ ,
    have h10: LtA A D C D C B := ⟨D, A, B, (axiom_betweennesssymmetry _ _ _ h3.1), (ray4 (or.inr(or.inl ⟨D⟩)) h8), (ray4 (or.inr(or.inl ⟨B⟩)) h2.2.1.symm), (h9.trans (ABCequalsCBA h7.2.2.2.1))⟩, 
    have h11: CongA _ _ _ _ _ _ := ⟨ B, C, B, C, (ray4 (or.inr(or.inr (axiom_betweennesssymmetry _ _ _ h3.1))) h4.1.symm), (ray4 (or.inr(or.inl ⟨C⟩)) h8.symm), (ray4 (or.inr(or.inl ⟨B⟩)) h4.2.2.symm),(ray4 (or.inr(or.inl ⟨C⟩)) h8.symm), (cn_congruencereflexive D B), (cn_congruencereflexive D C), (cn_congruencereflexive B C), h6⟩, 
    have h12: LtA B D C D C B := angleorderrespectscongruence2 h10 h11.symm,
    have h13: ¬ Col B C D, 
      intro h,
      have h₁: Col D B A, by collinear_tac,
      have h₂: Col D B C, by collinear_tac,
      have h₃:= collinearorder(collinear4 D h₁ h₂ h4.2.2.symm),
      tauto,
    have h14:= NCorder h13,
    unfold TG,
    use D,
    simp*,
    have h14: LtA C D B D C B := angleorderrespectscongruence2 h12 (ABCequalsCBA h14.2.1),
    have h15: LtA C D B B C D := angleorderrespectscongruence h14 (ABCequalsCBA h13),
    exact proposition_19 _ _ _ (h13) h15,

  end 

lemma proposition_21helper (A B C E : Point) : 
TG B A A E B E → BetS A E C → TT B A A C B E E C := sorry 

lemma proposition_21 (A B C D E : Point) :
   Triangle A B C → BetS A E C → BetS B D E →
   TT B A A C B D D C ∧ LtA B A C B D C := 

   begin
   rintros h1 h2 h3,
      have h₁:= (bet.neq h3).1,
      have h₂:= ((bet.neq h2).2.2),
    have h₃: ¬ Col A E B ,
    { use [NChelper ((NCorder h1).2.2.2.1) (by collinear_identity) (by collinear_tac) (bet.neq h2).2.1]},
    have h4: ¬ Col E C B , 
    {
      use [NChelper ((NCorder h1).2.2.2.1) (by collinear_tac) (by collinear_identity) (bet.neq h2).1],
     },
      have h5: ¬ Col E D C ,
      {
      use [ NChelper ((NCorder h4).2.2.2.1) (by collinear_identity) (by collinear_tac) ((bet.neq h3).1).symm],
     },
     have h: Triangle E C D := (NCorder h5).2.2.2.1,
     have h₆: TT B A A C B E E C := proposition_21helper _ _ _ _ (proposition_20 _ _ _ ((NCorder h₃)).2.2.2.1) h2,
     have h6:= proposition_21helper _ _ _ _(proposition_20 _ _ _ h) (axiom_betweennesssymmetry _ _ _ h3),
     use TTflip2(TTtransitive h₆ (TTflip(TTorder h6))),
      have h7:= proposition_16 _ _ _ _ ((NCorder h₃).2.2.1) h2,
      have h8: ¬ Col B D C := NChelper ((NCorder h4).2.2.2.1) (by collinear_identity) (by collinear_tac) ((bet.neq h3).2.1), 
      have h9 := proposition_16 _ _ _ _ ((NCorder h).1) (axiom_betweennesssymmetry _ _ _ h3),
      have h10:= angleorderrespectscongruence2 h9.2 (ABCequalsCBA (NCorder h5).2.2.1),
      have h11:= angleorderrespectscongruence h10 (ABCequalsCBA (h8)),
      have h12: LtA B A E B E C := angleorderrespectscongruence2 h7.2 (ABCequalsCBA(NCorder h₃).2.2.1),
      have h13: LtA B A E C E B := angleorderrespectscongruence h12 (ABCequalsCBA(NCorder h4).1),
      have h14: CongA B A C B A E:= equalangleshelper (eq_anglesrefl((NCorder h1).1)) (eq_implies_out ⟨⟨B⟩ , (NCdistinct h1).1⟩) (ray4 (or.inl h2) h₂),
      have h15:= angleorderrespectscongruence2 h13 h14,
      have h:=(eq_anglesrefl (NCorder h5).2.2.1),
      have h16:= equalangleshelper h (ray4 (or.inr(or.inl ⟨C⟩)) (bet.neq h2).1) (ray4 (or.inr(or.inr (axiom_betweennesssymmetry _ _ _ h3))) (h₁.symm)),
      have h17: LtA B A C C E D := angleorderrespectscongruence h15 h16,
      use angleordertransitive h17 h11,
  
   end 

lemma togethera : ∀ ( A B C D F G P Q a b c : Point ),
       TG A a B b C c → Cong D F A a → Cong F G B b → BetS D F G → Cong P Q C c → Lt P Q D G :=
       begin
       introv h h1 h2 h3 h4, simp [together h h1 h2 h3 h4],
       end


lemma proposition_22 : ∀ (A B C E F a b c : Point),
   TG A a B b C c → TG A a C c B b → TG B b C c A a → F ≠ E →
   ∃ X Y, Cong F X B b ∧ Cong F Y A a ∧ Cong X Y C c ∧ Out F E X ∧ Triangle F X Y := 

   begin
   rintros _ _ _ _ _ _ _ _ ⟨P, h1⟩ h2 h3 h4, 
   cases (layoff h4 (null3 ((bet.neq h1.1).1) h1.2.1)) with G,
   any_goals {simp*, use G,}, simp*, 
   have h5:= bet.neq h1.1,
   have h6: B ≠ b :=  (null3 ((bet.neq h1.1).1) (h1.2.1)),
   have h7:= lt_neq h1.2.2,
   cases postulate_extension _ _ _ _ (null3 h6 h.2.symm) h7.1 with H h8,
   cases postulate_extension _ _ _ _ ((null3 h6 h.2.symm).symm) h5.2.1 with D h9,
   have h10:= together h3 h.2 h8.2 h8.1 h9.2.flipL,
   cases h10.1 with M h11,
   have h12:= h11.2.trans ((h9.2).flipL),
  --  have : Lt C c D G:= togethera _ _ _ _ _ _ _ _ _ _ _  ⟨P, h1⟩ ,
  --  have: OnCirc N R,
  --  have := postulate_circle_circle,
  -- --  have : Cong F K A a ∧ G K C c := OnCirc,
  -- --  --rw this at *,
  --  -- (lt_neq h1.2.2).1),
   
  --  --(lt_neq h1.2.2).1,
   


   end  






lemma proposition_23B (A B C D E P : Point) :
   A ≠ B → ¬Col D C E → ¬Col A B P →
   ∃ X Y, Out A B Y ∧ CongA X A Y D C E ∧ OS X A B P:= sorry 




lemma proposition_23C (A B C D E P: Point) : 
A ≠ B → ¬Col D C E → ¬Col A B P →
   ∃ X Y, Out A B Y ∧ CongA X A Y D C E ∧ SS X P A B := 

begin 
  introv h1 h2 h3,
  have h4: P ≠ A,
    intro h,
    have : Col A B P, by collinear_identity,
    tauto,
  cases postulate_extension _ _ _ _ h4 h4 with Q h5, 
  have h8: ¬ Col A B Q,
    intro h,
    have h₁: Col P A Q, by collinear_tac,
    rcases ⟨collinearorder h, collinearorder h₁, bet.neq h5.1⟩ with ⟨⟨_,h₂⟩ ,⟨_,h₃⟩ , ⟨h₄,_⟩⟩,
    have := collinear4 Q h₂.2.1 h₃.2.2.2 h₄.symm, 
    contradiction,
  rcases proposition_23B _ _ _ _ _ _ h1 h2 h8 with ⟨F, G ,h10, h11, ⟨J, h12,h13,h14⟩⟩, 
  use [F, G, h10, h11, Q, J, A, h13, (or.inr(or.inl ⟨A⟩)), h12, h5.1, h14, h3], 
 
end 

lemma proposition_24 (A B C D E F: Point):
   Triangle A B C → Triangle D E F → Cong A B D E → Cong A C D F → LtA E D F B A C →
   Lt E F B C := sorry 

lemma proposition_25 (A B C D E F : Point): 
   Triangle A B C → Triangle D E F → Cong A B D E → Cong A C D F → Lt E F B C →
   LtA E D F B A C := 

begin
    introv h h1 h2 h3 h4, 
  have h5: ¬ LtA B A C E D F, 
    intro hEq,
    have h6:= proposition_24 _ _ _ _ _ _ h1 h h2.symm h3.symm hEq,
    have h7:= trichotomy2 h4,
  contradiction,
  have h6: ¬ Col B A C ∧ ¬ Col E D F ,
    constructor,
    repeat {  
      intro hEq,
      rcases collinearorder hEq, 
    contradiction,
    },
  have h7: ¬ CongA E D F B A C, 
    intro h₁, 
    have h₅: Lt B C B C := lt_cong2 h4 (proposition_04 _ _ _ _ _ _ h2 h3 ( h₁.symm)).1.symm,
    have h₆:= trichotomy2 h₅,
  contradiction,
  use [angletrichotomy2 h6.2 h6.1 h7 h5],
end 

lemma prop_26_helper (A B C D E F : Point):
   Triangle A B C → Triangle D E F → CongA A B C D E F → CongA B C A E F D → Cong A B D E →
   ¬ Lt E F B C := sorry 

lemma proposition_26A (A B C D E F : Point) :
   Triangle A B C → Triangle D E F → CongA A B C D E F → CongA B C A E F D → Cong B C E F →
   Cong A B D E ∧ Cong A C D F ∧ CongA B A C E D F := sorry

lemma proposition_26B (A B C D E F : Point):
   Triangle A B C → Triangle D E F → CongA A B C D E F → CongA B C A E F D → Cong A B D E →
   Cong B C E F ∧ Cong A C D F ∧ CongA B A C E D F := 

begin 
  introv h1 h2 h3 h4 h5,
  have h6:= prop_26_helper _ _ _ _ _ _ h1 h2 h3 h4 h5,
  rcases ⟨ h3.symm,  h4.symm⟩ with ⟨h7 , h8⟩,
  have h9:= prop_26_helper _ _ _ _ _ _  h2 h1 h7 h8 h5.symm,
  rcases ⟨not_eq_of_triangle h1, not_eq_of_triangle h2⟩ with ⟨⟨h10, h11⟩,⟨ h12, h13⟩⟩,
  have h14:= trichotomy1 h9 h6 h11.1 h13.1, 
  rcases congr_flip' h5 with ⟨ h15, _⟩ ,
  rcases proposition_04 _ _ _ _ _ _ h15 h14 h3 with ⟨_, _,_⟩,
  refine ⟨ _ , _, _⟩, 
  repeat {assumption}, 
end 

lemma proposition_27 : ∀ (A B C D E F : Point),
   BetS A E B → BetS C F D → CongA A E F E F D → OS A E F D →
   Par A B C D := sorry 


lemma proposition_27B : ∀ (A D E F : Point), CongA A E F E F D → OS A E F D →
   Par A E F D := 


begin
rintros _ _ _ _ h1 h2,
have h3:= angledistinct h1,
rcases ⟨postulate_extension _ _ _ _ (angledistinct h1).1 (h3).1, postulate_extension _ _ _ _ (h3.2.2.2.2.1).symm h3.2.2.2.2.1⟩  with ⟨⟨B ,h4⟩, C ,h5⟩, 
have h6:= proposition_27 _ _ _ _ _ _ h4.1 (axiom_betweennesssymmetry _ _ _ h5.1) h1 h2,
rcases collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h5.1))))) with ⟨_,_,h7⟩,
have h8:= collinearparallel h6 h7.1 h3.2.2.2.2.1,
rcases collinearorder (or.inr(or.inr(or.inr(or.inr(or.inl h4.1))))) with ⟨_,_,h11⟩,
have := collinearparallel ( ( h8.symm).flip).2.1 h11.1 (h3.1).symm,
use  ( (this).flip).2.1.symm,
end 

lemma proposition_28A : ∀ (A B C D E G H : Point),
   BetS A G B → BetS C H D → BetS E G H → CongA E G B G H D → SS B D G H →
   Par A B C D :=sorry 

lemma proposition_28B : ∀ (A B C D E F G H : Point),
   BetS A G B → BetS C H D → BetS E G H → BetS G H F → RT B G H G H D → SS B D G H →
   Par A B C D :=sorry 

lemma proposition_28C : ∀ (B D F G H : Point),
   BetS G H F → RT B G H G H D → SS B D G H → Par G B H D := 

begin
rintros _ _ _ _ _ h1 h2 ⟨_, _, _, h3⟩,
have h4:= NCdistinct h3.2.2.2.2.2,
have h5:= NCdistinct h3.2.2.2.2.1,
cases postulate_extension _ _ _ _ (h5.2.2.1.symm) h5.2.2.1 with A h6,
cases postulate_extension _ _ _ _ (h4.2.1.symm) h4.2.1 with C h7,
rcases ⟨axiom_betweennesssymmetry _ _ _ h6.1, axiom_betweennesssymmetry _ _ _ h7.1⟩ with ⟨h8,h9⟩, 
cases postulate_extension _ _ _ _ h4.2.2.2.1 (h4.2.2.2.1) with E h10,
have h11:= axiom_betweennesssymmetry _ _ _ h10.1,
have h12:= proposition_28B _ _ _ _ _ _ _ _ h8 h9 h11 h1 h2 ⟨_, _, _,h3⟩,
rcases collinearorder (or.inr(or.inr(or.inr((or.inl h7.1))))) with ⟨_,_,h13⟩,
have h14:= collinearparallel h12 h13.2.2 h4.2.1,
rcases collinearorder (or.inr(or.inr(or.inr((or.inl h8))))) with ⟨_,h16⟩,
use [(collinearparallel (h14.symm) h16.1 h5.2.2.1).symm],
end 

lemma proposition_28D : ∀ (B D E G H : Point),
   BetS E G H → CongA E G B G H D → SS B D G H → Par G B H D := 

begin 
rintros _ _ _ _ _ h1 h2 ⟨_, _, _, h3⟩,
have h4:= NCdistinct h3.2.2.2.2.2,
have h5:= NCdistinct h3.2.2.2.2.1,
cases postulate_extension _ _ _ _ (h5.2.2.1.symm) h5.2.2.1 with A h6,
cases postulate_extension _ _ _ _ (h4.2.1.symm) h4.2.1 with C h7,
rcases ⟨axiom_betweennesssymmetry _ _ _ h6.1, axiom_betweennesssymmetry _ _ _ h7.1⟩ with ⟨h8,h9⟩,
cases postulate_extension _ _ _ _ h4.2.2.2.1.symm (h4.2.2.2.1).symm with F h10,
have h12:= proposition_28A _ _ _ _ _ _ _ h8 h9 h1 h2 ⟨_, _, _, h3⟩,
have h13a : Col C D H, by collinear_tac, 
have h14: Par A B H D := collinearparallel h12 h13a h4.2.1,
have h14a: Col A B G, by collinear_tac,
simp [(collinearparallel (h14.symm) h14a h5.2.2.1).symm],
end 





end 

class euclidean_euclidean (Point : Type) extends euclidean_neutral_ruler_compass Point := 
  (postulate_Euclid5 : ∀ a p q r s t, BetS r t s → 
  BetS p t q → BetS r a q → Cong p t q t → Cong t r t s → 
  ¬ Col p q s → ∃ X, BetS p a X ∧ BetS s q X)

section 

  variables {Point : Type}
  variable [euclidean_euclidean Point]

  variables x y z : Point 
  variables C D E : euclidean_preneutral.Circle Point 

open euclidean_euclidean 

lemma proposition_29 :
   ∀ (A B C D E G H : Point),
   Par A B C D → BetS A G B → BetS C H D → BetS E G H → OS A G H D →
   CongA A G H G H D ∧ CongA E G B G H D ∧ RT B G H G H D := sorry 

lemma proposition_29B :
   ∀ (A D G H : Point), Par A G H D → OS A G H D → CongA A G H G H D :=


begin 
  rintros _ _ _ _ ⟨a, g, h, d, m, h1⟩ h2,
  have h3: H ≠ G,
    intro hEq, 
    have h₁: Col H D H , by collinear_identity,
    have h₂: Col A G G := by collinear_identity,
    subst hEq,
    have h3: Meet A H H D:= ⟨H, h1.1, h1.2.1, h₂, h₁⟩, 
  tauto,
  cases postulate_extension _ _ _ _ h3.symm h3.symm with F h4,
  cases postulate_extension _ _ _ _ h1.1 h1.1 with B h5,
  cases postulate_extension _ _ _ _ h1.2.1.symm h1.2.1.symm with C h6,
  cases postulate_extension _ _ _ _ h3 h3 with E h7,
  rcases bet.neq h5.1 with ⟨_,h8⟩ ,
  rcases bet.neq h6.1 with ⟨_,h9⟩,
  have h11a: Col G A B , by collinear_tac,
  have h30a: Col B A G, by collinear_tac,
  rcases collinearorder h1.2.2.1 with ⟨ h12,_⟩,
  have h13:= collinear4 G h11a (h12) h1.1.symm,
  have h13a: Col G A g, by collinear_tac, 
  have h15:= collinear4 G h11a h13a h1.1.symm,
  have h16a: Col D C H , by collinear_tac ,
  have h17a: Col H D C , by collinear_tac ,
  have h18: Col D C h := collinear4 H h17a h1.2.2.2.2.2.1 h1.2.1,
  cases collinearorder h18 with h19 _,
  have h20: Col D d C := collinear4 H h1.2.2.2.2.2.2.1 h17a h9.1.symm,
  have h21: Col C D d, by collinear_tac,
  have h22: ¬ Meet A B C D, 
    rintro ⟨M , h₁⟩,
    rcases collinearorder h₁.2.2.1 with ⟨h₂,_⟩,
    have h₄: Col A G M := collinear4 B h30a h₂ h8.2.symm,
    have h₅: Col D H M := collinear4 C (collinear1 h16a) h₁.2.2.2 h9.2.symm,
    cases collinearorder h₅ with h₆ _,
    have : Meet _ _ _ _ := ⟨ M, h1.1 ,h1.2.1 ,h₄ , h₆⟩, 
  tauto,
  have h23: Par A B C D := ⟨a, g, h, d, m, h8.2, h9.2.symm, h13, h15, h1.2.2.2.2.1, h19, h21, h1.2.2.2.2.2.2.2.1, h22, h1.2.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.2 ⟩,
  have h24: BetS C H D := axiom_betweennesssymmetry _ _ _ h6.1,
  have h25: BetS E G H := axiom_betweennesssymmetry _ _ _ h7.1,
  simp [proposition_29 _ _ _ _ _ _ _ h23 h5.1 h24 h25 h2], 
end 


lemma proposition_29C : ∀ (B D E G H : Point),
   Par G B H D → SS B D G H → BetS E G H →
   CongA E G B G H D ∧ RT B G H G H D := 

begin
  rintros _ _ _ _ _ h1 h2 h3,
  have h4:=  h1.NC,
  have h5: G ≠ B,
    intro hEq,
    have : Col G B H := or.inl hEq,
  tauto,
  cases postulate_extension _ _ _ _ h5.symm h5.symm with A h6,
  have h7:= axiom_betweennesssymmetry _ _ _ h6.1,
  cases bet.neq h7 with h8 h9,
  cases collinearorder (or.inr(or.inr(or.inr(or.inl h7)))) with h23 h10,
  have h11:=  h1.symm,
  have h12:= collinearparallel h11 h10.2.2.1 h9.2, 
  have h13:=  h12.flip,
  have h14:= collinearparallel h13.2.1 h10.2.2.2 h9.1.symm,
  have h15:=  h14.flip,
  rcases  h15.2.1.symm with ⟨a, g, h, d, m, h16⟩,
  have h17: H ≠ G, 
    rintro hEq,
    have h₁: Col H D H , by collinear_identity,
    have h₂: Col A G G , by collinear_identity,
    subst hEq,
    have h3: Meet A H H D:= ⟨H, h16.1, h16.2.1, h₂, h₁⟩, 
  tauto,
  rcases ⟨postulate_extension _ _ _ _ h17.symm h17.symm, postulate_extension _ _ _ _ h16.2.1.symm h16.2.1.symm⟩ with ⟨⟨F, h18⟩, ⟨C, h19⟩⟩,
  have h20:= axiom_betweennesssymmetry _ _ _ h3,
  cases bet.neq h19.1 with h21 h22,
  cases collinearorder h23 with h24 h25,
  cases collinearorder h16.2.2.1 with h26 h27,
  have h28: Col A B a := collinear4 G h24 h26 h16.1.symm,
  cases collinearorder h16.2.2.2.1 with h29 h30,
  have h31: Col A B g := collinear4 G h24 h29 h16.1.symm,
  cases collinearorder (or.inr(or.inr(or.inr(or.inl h19.1)))) with h32 h33,
  cases collinearorder h32 with h60 h34,
  have h35: Col D C h := collinear4 H h60 h16.2.2.2.2.2.1 h16.2.1,
  cases collinearorder h35 with h36 h37,
  have h38: Col D d C := collinear4 H h16.2.2.2.2.2.2.1 h60 h16.2.1,
  cases collinearorder h38 with h39 h40,
  have h41: ¬ Meet A B C D,
    rintro ⟨M, hEq⟩,
    cases collinearorder hEq.2.2.1 with h₁ h₂,
    have h₃: Col A G M := collinear4 B h10.2.2.2 h₁ h9.2.symm,
    have h₄: Col D H M := collinear4 C h33.2.2.2 hEq.2.2.2 hEq.2.1,
    cases collinearorder h₄ with h₅ h₆,
    have: Meet A G H D:= ⟨M, h16.1, h16.2.1, h₃, h₅⟩, 
  tauto,
  have h41: Par A B C D := ⟨_, _, _, _, _, h9.2, h22.2.symm, h28, h31, h16.2.2.2.2.1, h36, h40.2.1, h16.2.2.2.2.2.2.2.1, h41, h16.2.2.2.2.2.2.2.2.2.1, h16.2.2.2.2.2.2.2.2.2.2 ⟩,
  have h42:= axiom_betweennesssymmetry D H C h19.1, 
  have h43: Col G H G , by collinear_identity,
  cases  h1.NC with h44 h45,
  rcases NCorder h44 with ⟨_,_,_,h46,_⟩,
  have h47:= samesidesymmetric h2,
  have h48: OS B G H A := ⟨_, h6.1, h43, h46⟩ ,
  have h49:= planeseparation h47.1 h48,
  have h50:= oppositesidesymmetric h49,
  have := proposition_29 _ _ _ _ _ _ _ h41 h7 h42 h3 h50,
  tauto,

end 

lemma proposition_30A : 
∀ (A B C D E F G H K : Point),
   Par A B E F → Par C D E F → BetS G H K → BetS A G B → BetS E H F → BetS C K D → OS A G H F → OS F H K C →
   Par A B C D :=sorry 


lemma proposition_30B :
   ∀ (A B C D E F G H K : Point),
   Par A B E F → Par C D E F → BetS G K H → BetS A G B → BetS E H F → BetS C K D → OS A G H F → OS C K H F →
   Par A B C D := 

   begin 
   rintro _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8,
   have h9: K ≠ H ∧ G ≠ K ∧ G ≠ H := bet.neq h3,
   cases postulate_extension _ _ _ _ h9.2.2.symm h9.2.2 with P h10,
   cases proposition_29 A B E F P G H h1 h4 h5 (axiom_betweennesssymmetry _ _ _  h10.1) h7 with h12 h13,
   have h14: BetS P K H := T3_5b (axiom_betweennesssymmetry _ _ _  h10.1) h3,
   cases proposition_29 _ _ _ _ _ _ _ h2 h6 h5 h14 h8 with h15 h16,
   have h18: Out H K G := ray4 (or.inr(or.inr (axiom_betweennesssymmetry _ _ _  h3))) h9.1.symm,
   have h19: Out H G K := ray5 h18,
   have h20:= bet.neq h5,
   have h21a : Out H F F, by ray_identity, 
   have h22: CongA A G H K H F:= equalangleshelper h12 h19 h21a,
   have h24: CongA C K H A G H := h15.trans (h22.symm),
   have h25: Out G H K := ray4 (or.inl h3) h9.2.2,
   have h26: G ≠ B ∧ A ≠ G ∧ A ≠ B := bet.neq h4,
   have h27a : Out G A A , by ray_identity,
  --  have h27: Out G A A := ray4 (or.inr(or.inl ⟨A⟩)) h26.2.1.symm,
   have h28: CongA C K H A G K := equalangleshelper h24 h27a h25,
   cases h7 with M h30,
   cases h8 with m h31,
   cases collinearorder (or.inr(or.inr (or.inr (or.inr (or.inl h3))))) with h32 h33,
   rcases collinearorder h30.2.1 with ⟨h34, _⟩,  
   have h35:= collinear4 H h33.2.1 h34 h9.2.2.symm,
   rcases collinearorder h35 with ⟨h36,_⟩,
   have h37a: Col H K m , by collinear_tac,
   have h38:= collinear4 H h37a h33.2.2.2 h9.1.symm,
   have h39a: Col K G m , by collinear_tac,
   have h40: Col G H G , by collinear_identity,
   have h41:= NChelper h30.2.2 h40 h33.2.2.1 h9.2.1,
   have h42: ¬Col K G A := (NCorder h41).1,
   have h43: Col K H K , by collinear_identity,
   have h45:= NChelper h31.2.2 h43 h33.1 h9.2.1.symm,
   have h46: SS A C K G , use [F, M, m, h36, h39a, h30.1, h31.1, h42, h45],
   have h47:= samesidesymmetric h46,
   have h50: Par D C B A := proposition_28A _ _ _ _ _ _ _ (axiom_betweennesssymmetry _ _ _ h6) (axiom_betweennesssymmetry _ _ _ h4) ((axiom_betweennesssymmetry _ _ _  h3)) (h28.flip) h47.1,
   use [(h50.flip).2.2.symm],

  end 

 end 

open euclidean_neutral_ruler_compass 

section 

variables {Point : Type}
variable [euclidean_neutral_ruler_compass Point]

variables x y z : Point
variables C D E : euclidean_preneutral.Circle Point

lemma proposition_31 :
   ∀ (A B C D : Point),
   BetS B D C → ¬Col B C A → ∃ X Y Z, BetS X A Y 
   ∧ CongA Y A D A D B ∧ CongA Y A D B D A 
   ∧ CongA D A Y B D A ∧ CongA X A D A D C 
   ∧ CongA X A D C D A ∧ CongA D A X C D A ∧ 
   Par X Y B C ∧ Cong X A D C ∧ Cong A Y B D ∧ 
   Cong A Z Z D ∧ Cong X Z Z C ∧ Cong B Z Z Y 
   ∧ BetS X Z C ∧ BetS B Z Y ∧ BetS A Z D := sorry 


lemma proposition_31short :
   ∀ (A B C D : Point), BetS B D C → ¬Col B C A →
   ∃ X Y Z, BetS X A Y ∧ CongA X A D A D C ∧ Par X Y B C ∧ BetS X Z C ∧ BetS A Z D := sorry 



end 

open euclidean_euclidean 

section 

  variables {Point : Type}
  variable [euclidean_euclidean Point]

  variables x y z : Point 
  variables C D E : euclidean_preneutral.Circle Point 


lemma proposition_33 : ∀ (A B C D M : Point), Par A B C D → Cong A B C D → BetS A M D → BetS B M C →
   Par A C B D ∧ Cong A C B D := 
   begin
   rintros _ _ _ _ _ ⟨a, b, c, d, m, h1⟩  h2 h3 h4,
   have h5: Col B C M, by collinear_tac,
   have h6: ¬ Col B C A ,
    intro hEq,
    have h: Col C D C , by collinear_identity,
    have h₂ : Col A B C, by collinear_tac,
    have : Meet A B C D, use [C, h1.1, h1.2.1, h₂, h],
   tauto,
   have h7: OS A B C D, use [M, h3, h5, h6],
   have h8: CongA A B C B C D := proposition_29B _ _ _ _ ⟨a, b, c, d, m, h1⟩ h7,
   have h9: ¬ Col B C D,
    intro hEq,
    have h: Col A B B , by collinear_identity,
    have h₂ : Col C D B, by collinear_tac,
    have : Meet A B C D, use [B, h1.1, h1.2.1, h, h₂],
   tauto,
   have h10:= (ABCequalsCBA h9),
   have h12:= proposition_04 _ _ _ _ _ _ h2.flipL (cn_equalityreverse B C) (h8.trans h10),
   have h13 : CongA A C B C B D := ((ABCequalsCBA h6).symm).trans h12.2.2,
   have h15 : Par A C B D := proposition_27B _ _ _ _ h13 ⟨M, h3, collinear1 h5, (NCorder h6).1⟩,
   use [ h15, ((congr_flip' h12.1).2.2)],
   end

  lemma proposition_33B : ∀ (A B C D : Point), Par A B C D → Cong A B C D → SS A C B D →
   Par A C B D ∧ Cong A C B D := 
   begin
   introv h h1 h2, 
    have : ¬ CR A C B D,
    { rintro ⟨M, h₁⟩,
      have h₂: ¬ Col A B D := (h.NC).2.2.2,
      have h₃: ¬ Col B D A:= (NCorder h₂).2.1,
      have h₄: Col B D M, by collinear_tac,
      have : OS A B D C , use [M], simp*,
      exacts [samenotopposite h2 this],                  },
      cases crisscross h this with _ h4, 
   exact proposition_33 _ _ _ _ _ h h1 h4.1 (axiom_betweennesssymmetry _ _ _ h4.2),   
   end 

end

-- lemma 34 attempted rewrite
-- lemma proposition_34 : ∀ (A B C D : Point), PG A C D B → 
--    Cong A B C D ∧ Cong A C B D ∧ CongA C A B B D C ∧ CongA A B D D C A ∧ Cong_3 C A B B D C :=  

--   begin
--   rintros _ _ _ _ ⟨h1, _, _, _, _,_,h2⟩,
--   have h3: Par A C B D := h1.flip.2.1,
--   have : ¬ Col B C A ∧ ¬ Col B C D ∧ ¬Col A B D,
--     refine ⟨_,_,_⟩,
--     {intro h,
--       have : Meet A B C D , use ⟨C, h2.1, h2.2.1 , collinearreverse( collinear1 h), by collinear_identity⟩,
--       tauto, },
--      {intro h,
--       have : Meet A B C D , use ⟨B, h2.1, h2.2.1 ,  by collinear_identity, collinear2 h⟩,
--       tauto,}, 
--       {intro h,
--       have : Meet A B C D , use ⟨D, h2.1, h2.2.1 ,  h, by collinear_identity⟩,
--       tauto, 
--     },
--     have h₁:= NCorder this.1,
--     have h₂: OS A C B D ∧ OS A B C D, 
--     constructor,
--     repeat {unfold OS, cleanup_hyps}, use M, cleanup_hyps, exact by collinear_tac,
--       rcases (diagonalsmeet ⟨h1, _, _, _, _,_,h2⟩) with ⟨M ,h₁⟩, use M, simp*, exact by collinear_tac,
--     have h₃: CongA A B C B C D := proposition_29B _ _ _ _ ⟨ _, _, _, _,_,h2⟩ h₂.2,
--     have h₄:= ABCequalsCBA this.2.1,
--     have h₅:= h₃.trans h₄,
--     have h₆:= ABCequalsCBA this.1,
--     have h₇: CongA A C B C B D := proposition_29B _ _ _ _ h3 h₂.1,
--     have h₈:= h₆.trans h₇,
--     have h₉:= proposition_26A _ _ _ _ _ _ ((NCorder this.1).2.2.1) ((NCorder this.2.1).2.2.2.2) h₅ h₈ (cn_equalityreverse B C), 
--     use [h₉.1.flipR, h₉.2.1.flipR, h₉.2.2.flip],
--     have: CongA A B D D C A, unfold CongA, 
--     --use [A, D, D, A],
--     refine ⟨A,D,D,A,by ray_identity,by ray_identity, ⟨by ray_identity, by ray_identity, h₉.1.flipLR, _⟩  ⟩,
-- --    by ray_identity,
--     --repeat {by ray_identity}, 
--     use [h₉.2.1.reverse], use [cn_equalityreverse A D], tauto, simp*,
--     rw Cong_3, use [h₉.2.1.flipLR, cn_equalityreverse C B], simp*,
--    end 


 /-- In parallelogrammic areas the opposite sides and 
  angles are equal to one another,and the diameter bisects the areas.-/

  -- lemma proposition_34 : ∀ (A B C D : Point), PG A C D B → 
  --  Cong A B C D ∧ Cong A C B D ∧ CongA C A B B D C ∧ CongA A B D D C A ∧ Cong_3 C A B B D C := 

  -- begin
  -- rintros _ _ _ _ ⟨h1, _, _, _, _,_,h2⟩,
  -- have h3: Par A C B D := h1.flip.2.1,
  -- have : ¬ Col B C A ∧ ¬ Col B C D ∧ ¬Col A B D,
  --   refine ⟨_,_,_⟩,
  --   {intro h,
  --     have : Meet A B C D , use ⟨C, h2.1, h2.2.1 , collinearreverse( collinear1 h), by collinear_identity⟩,
  --     tauto, },
  --    {intro h,
  --     have : Meet A B C D , use ⟨B, h2.1, h2.2.1 ,  by collinear_identity, collinear2 h⟩,
  --     tauto,}, 
  --     {intro h,
  --     have : Meet A B C D , use ⟨D, h2.1, h2.2.1 ,  h, by collinear_identity⟩,
  --     tauto, 
  --   },
  --   have h₁:= NCorder this.1,
  --   have h₂: OS A C B D ∧ OS A B C D, 
  --   constructor,
  --   repeat {unfold OS, 
  --     rcases (diagonalsmeet ⟨h1, _, _, _, _,_,h2⟩) with ⟨M ,h₁⟩, use M, simp*, exact by collinear_tac},
  --   have h₃: CongA A B C B C D := proposition_29B _ _ _ _ ⟨ _, _, _, _,_,h2⟩ h₂.2,
  --   have h₄:= ABCequalsCBA this.2.1,
  --   have h₅:= h₃.trans h₄,
  --   have h₆:= ABCequalsCBA this.1,
  --   have h₇: CongA A C B C B D := proposition_29B _ _ _ _ h3 h₂.1,
  --   have h₈:= h₆.trans h₇,
  --   have h₉:= proposition_26A _ _ _ _ _ _ ((NCorder this.1).2.2.1) ((NCorder this.2.1).2.2.2.2) h₅ h₈ (cn_equalityreverse B C), 
  --   use [h₉.1.flipR, h₉.2.1.flipR, h₉.2.2.flip],
  --   have: CongA A B D D C A, unfold CongA, 
  --   use [A, D, D, A], use by ray_identity, use by ray_identity, simp*,--use by ray_identity, use by ray_identity,-- use by ray_identity, _, _⟩ ,
  --   -- refine ⟨A,D,D,A,by ray_identity, by ray_identity, ⟨by ray_identity, by ray_identity, h₉.1.flipLR, _⟩  ⟩,
  --   -- use [h₉.2.1.reverse], use [cn_equalityreverse A D], tauto, simp*,
  --   -- rw Cong_3, use [h₉.2.1.flipLR, cn_equalityreverse C B], simp*,
  -- end 




class area (Point : Type) extends euclidean_euclidean Point := 
  
  (EF : Point → Point → Point → Point → Point → Point → Point → Point → Prop)

  (ET : Point → Point → Point → Point → Point → Point → Prop)
  
   (axiom_congruentequal :
  ∀ A B C a b c, Cong_3 A B C a b c → ET A B C a b c)


  (axiom_ETpermutation :
   ∀ A B C a b c,
    ET A B C a b c →
    ET A B C b c a ∧
    ET A B C a c b ∧
    ET A B C b a c ∧
    ET A B C c b a ∧ 
    ET A B C c a b)

  (axiom_ETsymmetric :
   ∀ A B C a b c, ET A B C a b c → ET a b c A B C)

  (axiom_EFpermutation :
   ∀ A B C D a b c d,
   EF A B C D a b c d →
     EF A B C D b c d a ∧
     EF A B C D d c b a ∧
     EF A B C D c d a b ∧
     EF A B C D b a d c ∧
     EF A B C D d a b c ∧
     EF A B C D c b a d ∧
     EF A B C D a d c b)

  (axiom_halvesofequals :
  ∀ A B C D a b c d, ET A B C B C D →
                           OS A B C D → ET a b c b c d →
                          OS a b c d → EF A B D C a b d c → ET A B C a b c)

  (axiom_EFsymmetric :
   ∀ A B C D a b c d, EF A B C D a b c d →
                           EF a b c d A B C D)

  (axiom_EFtransitive :
   ∀ A B C D P Q R S a b c d,
     EF A B C D a b c d → EF a b c d P Q R S →
     EF A B C D P Q R S)

  (axiom_ETtransitive :
   ∀ A B C P Q R a b c,
    ET A B C a b c → ET a b c P Q R → ET A B C P Q R)

  (axiom_cutoff1 :
   ∀ A B C D E a b c d e,
    BetS A B C → BetS a b c → BetS E D C → BetS e d c →
    ET B C D b c d → ET A C E a c e →
    EF A B D E a b d e)

  (axiom_cutoff2 :
   ∀ A B C D E a b c d e,
    BetS B C D → BetS b c d → ET C D E c d e → EF A B D E a b d e →
    EF A B C E a b c e)

  (axiom_paste1 :
   ∀ A B C D E a b c d e,
    BetS A B C → BetS a b c → BetS E D C → BetS e d c →
    ET B C D b c d → EF A B D E a b d e →
    ET A C E a c e)

  (axiom_deZolt1 :
   ∀ B C D E, BetS B E D → ¬ ET D B C E B C)

  (axiom_deZolt2 : ∀ A B C E F,
  Triangle A B C → BetS B E A → BetS B F C →
  ¬ ET A B C E B F)

  (axiom_paste2 :
  ∀ A B C D E M a b c d e m,
    BetS B C D → BetS b c d → ET C D E c d e →
    EF A B C E a b c e →
    BetS A M D → BetS B M E →
    BetS a m d → BetS b m e →
    EF A B D E a b d e)

(axiom_paste3 :
   ∀ A B C D M a b c d m,
    ET A B C a b c → ET A B D a b d →
    BetS C M D →
    (BetS A M B ∨ eq A M ∨ eq M B) →
    BetS c m d →
    (BetS a m b ∨ eq a m ∨ eq m b) →
    EF A C B D a c b d)

(axiom_paste4 :
   ∀ A B C D F G H J K L M P e m,
    EF A B m D F K H G → EF D B e C G H M L →
    BetS A P C → BetS B P D → BetS K H M → BetS F G L →
    BetS B m D → BetS B e C → BetS F J M → BetS K J L →
    EF A B C D F K M L) 

open area 


section 

  variables {Point : Type}
  variable [area Point]

  variables x y z : Point 
  variables C D E : euclidean_preneutral.Circle Point 


lemma ET_refl {A B C: Point}: Triangle A B C → ET A B C A B C:= 

begin
rintros h₁,
use [axiom_congruentequal A B C A B C (Tcongr_refl h₁)],
end 

lemma rect_rot {A B C D : Point}:RE A B C D → RE B C D A := 

begin
  rintros ⟨h₁ , h₂, h₃, h₄, M, h₅⟩, 
  refine ⟨_,_,_,_,_⟩,
  repeat {assumption},
  use [M , h₅.2, axiom_betweennesssymmetry _ _ _ h₅.1],
end 



end 


