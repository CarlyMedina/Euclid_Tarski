--namespace hidden
--BEGIN

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
  (axiom_betweennessidentity : ∀ A B, ¬ BetS A B A)
  (axiom_betweennesssymmetry : ∀ A B C, BetS A B C → BetS C B A)
  (axiom_innertransitivity :∀ A B C D, BetS A B D → BetS B C D → BetS A B C)
  (axiom_connectivity : ∀ A B C D, BetS A B D → BetS A C D → ¬ BetS A B C → ¬ BetS A C B → eq B C)
  (axiom_nocollapse : ∀ A B C D, A ≠ B → Cong A B C D → C ≠ D)
  (axiom_5_line : ∀ A B C D a b c d, Cong B C b c → Cong A D a d → Cong B D b d 
  → BetS A B C → BetS a b c → Cong A B a b → Cong D C d c)
  (postulate_Euclid2 : ∀ A B, A ≠ B → exists X, BetS A B X)
  (postulate_Euclid3 : ∀ A B, A ≠ B → exists X, CI X A A B)

namespace euclidean_preneutral
variables {Point : Type}
variable [euclidean_preneutral Point]

def Col (A B C : Point) := ((A = B) ∨ (A = C) ∨ (B = C) ∨ (BetS B A C) ∨ (BetS A B C) ∨  (BetS A C B))

def OnCirc (B : Point) (J : Circle Point) := ∃ X Y U, CI J U X Y ∧ Cong U B X Y

def InCirc (P : Point) (J : Circle Point) := ∃ X Y U V W, CI J U V W ∧ (eq P U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U P U Y)) 

def OutCirc (P : Point) (J : Circle Point) := ∃ X U V W, CI J U V W ∧ BetS U X P ∧ Cong U X V W

def Equilateral (A B C : Point) := (Cong A B B C) ∧ (Cong B C C A)

def Triangle (A B C : Point) := ¬ Col A B C

def Out (A B C : Point) := ∃ X, BetS X A C ∧ BetS X A B -- C lies on Ray AB 

def Lt (A B C D : Point) := ∃ X, BetS C X D ∧ Cong C X A B -- AB is less than CD 

def Midpoint (A B C : Point) := BetS A B C ∧ Cong A B B C -- B is the midpoint of AC

def CongA (A B C a b c : Point) := ∃ U V u v, Out B A U ∧ Out B C V ∧ Out b a u 
∧ Out b c v ∧ Cong B U b u ∧ Cong B V b v ∧ Cong U V u v ∧ ¬ Col A B C   -- Angle ABC is equal to angle abc

def Supp (A B C D F : Point) := Out B C D ∧ BetS A B F --DBF is a supplement of ABC

def Per (A B C : Point) := ∃ X, BetS A B X ∧ Cong A B X B ∧ Cong A C X C ∧ B ≠ C -- ABC is a right angle

def Perp_at (P Q A B C : Point) := ∃ X, Col P Q C ∧ Col A B C ∧ Col A B X ∧ Per X C P --PQ is perpendicular to AB at C and ¬ColABP

def Perp (P Q A B : Point) := ∃ X, Perp_at P Q A B X -- PQ is perpendicular to AB

def InAngle (A B C P : Point) := ∃ X Y, Out B A X ∧ Out B C Y ∧ BetS X P Y --P is in the interior of angle ABC

def OS (P A B Q : Point) := ∃ X, BetS P X Q ∧ Col A B X ∧ ¬ Col A B P -- TS in GH (P and Q are on opposite sides of AB)
-- need to flip anywhere in doc!!! and change  
def SS (P Q A B : Point) := ∃ X U V, Col A B U ∧ Col A B V ∧ BetS P U X ∧ BetS Q V X ∧ ¬ Col A B P ∧ ¬ Col A B Q -- P and Q are on the same side of AB
--need to change all TS to SS 
def isosceles (A B C : Point) := Triangle A B C ∧ Cong A B A C -- ABC is isosceles with base BC 

def Cut (A B C D E : Point) := BetS A E B ∧ BetS C E D ∧ ¬ Col A B C ∧ ¬ Col A B D --AB cuts CD in E 

def Cong_3 (A B C a b c : Point) := Cong A B a b ∧ Cong A C a c ∧ Cong B C b c --Triangle ABC is congruent to abc (TC in beeson) 

def LtA (A B C D E F : Point) := ∃ U X V, BetS U X V ∧ Out E D U ∧ Out E F V ∧ CongA A B C D E X --Angle ABC is less than angle DEF

def TG (A B C D E F : Point) := ∃ X, BetS A B X ∧ Cong B X C D ∧ Lt E F A X -- AB and CD are together greater than EF

def TT (A B C D E F G H : Point) := ∃ X, BetS E F X ∧ Cong F X G H ∧ TG A B C D E X -- AB, CD are together greater than EF, GH 

def RT (A B C D E F : Point) := ∃ X Y Z U V, Supp X Y U V Z ∧ CongA A B C X Y U ∧ CongA D E F V Y Z -- ABC and DEF together make two right angles

def Meet (A B C D : Point) := ∃ X, A ≠ B ∧ C ≠ D ∧ Col A B X ∧ Col C D X -- AB meets CD 

def CR (A B C D : Point) := ∃ X, BetS A X B ∧ BetS C X D -- AB crossed CD

def TP (A B C D : Point) := A ≠ B ∧ C ≠ D ∧ ¬ Meet A B C D ∧ SS C D A B -- AB and CD are Tarski parallel

def Par (A B C D : Point) := ∃ U V u v X, A ≠ B ∧ C ≠ D ∧ Col A B U ∧ -- AB and CD are parallel
  Col A B V ∧ U ≠ V ∧ Col C D u ∧ Col C D v ∧ u ≠ v ∧
 ¬ Meet A B C D ∧ BetS U X v ∧ BetS u X V 

def SumA (A B C D E F P Q R : Point) := ∃ X, CongA A B C P Q X ∧ CongA D E F X Q R ∧ BetS P X R -- ABC and DEF are together equal to PQR

def PG (A B C D : Point) := Par A B C D ∧ Par A D B C -- ABCD is a parallelogram

def SQ (A B C D : Point) := Cong A B C D ∧ Cong A B B C ∧ Cong A B D A ∧ Per D A B ∧ Per A B C ∧ Per B C D ∧ Per C D A -- ABCD is a square

def RE (A B C D : Point) := Per D A B ∧ Per A B C ∧ Per B C D ∧ Per C D A ∧ CR A C B D -- ABCD is a rectangle

def RC (A B C D a b c d : Point):= RE A B C D ∧ RE a b c d ∧ Cong A B a b ∧ Cong B C b c -- ABCD and abcd are congruent rectangles

def ER (A B C D a b c d : Point) := ∃ X Y Z U x z u w W, RC A B C D X Y Z U ∧ RC a b c d x Y z u ∧ BetS x Y Z ∧ BetS X Y z ∧ BetS W U w -- ABCD and abcd are equal rectangles

def cn_equalitytransitive (A B C : Point) := (A = C) → (B = C) → A = B

def cn_equalityreflexive (A : Point) := A = A

def cn_stability (A B: Point) := ¬(A ≠ B) → (A = B)

end euclidean_preneutral


open euclidean_preneutral

class euclidean_neutral (Point : Type) extends euclidean_preneutral Point := 

(postulate_Pasch_inner : ∀ A B C P Q, BetS A P C → BetS B Q C → ¬ Col A C B → ∃ X, BetS A X Q ∧ BetS B X P)

(postulate_Pasch_outer : ∀ A B C P Q, BetS A P C → BetS B C Q → ¬ Col B Q A → ∃ X, BetS A X Q ∧ BetS B P X)


section 

variables Point : Type 
variable [euclidean_neutral Point]

variables x y z : Point 
variables C D E : euclidean_preneutral.Circle Point 


end 

class euclidean_neutral_ruler_compass (Point : Type) extends euclidean_neutral Point :=

(axiom_circle_center_radius : ∀ A B C J P, CI J A B C → OnCirc P J → Cong A P B C)


(postulate_line_circle : 
  ∀ A B C K P Q, CI K C P Q → InCirc B K → 
  A ≠ B → ∃ X Y, Col A B X ∧ Col A B Y 
  ∧ OnCirc X K ∧ OnCirc Y K ∧ BetS X B Y)

( postulate_circle_circle : 
  ∀ C D F G J K P Q R S, CI J C R S → 
  InCirc P J → OutCirc Q J → CI K D F G → OnCirc P K → OnCirc Q K 
  → ∃ X, OnCirc X J ∧ OnCirc X K)

 
(foo : 2 + 2 =4)


section 

  variables Point : Type
  variable [euclidean_neutral_ruler_compass Point]
  variables x y z : Point
  variables C D E : euclidean_preneutral.Circle Point



 end 

class euclidean_euclidean (Point : Type) extends euclidean_neutral_ruler_compass Point := 
  (postulate_Euclid5 : ∀ a p q r s t, BetS r t s → 
  BetS p t q → BetS r a q → Cong p t q t → Cong t r t s → 
  ¬ Col p q s → ∃ X, BetS p a X ∧ BetS s q X)

section 

  variables Point : Type 
  variable [euclidean_euclidean Point]

  variables x y z : Point 
  variables C D E : euclidean_preneutral.Circle Point 

end 

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


open euclidean_preneutral
open euclidean_neutral
open euclidean_neutral_ruler_compass
open euclidean_euclidean 
open area 

section 

  variables Point : Type 
  variable [area Point]

  variables x y z : Point 
  variables C D E : euclidean_preneutral.Circle Point 


#print area

#check @euclidean_preneutral.BetS

#check BetS x y z


-- --END 

 end 

open classical 


