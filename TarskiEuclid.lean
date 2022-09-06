import data.nat.basic



/--This version of the axioms of Tarski is the one given in Wolfram Schwabhäuser, 
Wanda Szmielew and Alfred Tarski, Metamathematische Methoden in der Geometrie, Springer-Verlag, Berlin, 1983.
This axioms system is the result of a long history of axiom systems for geometry studied by Tarski, 
 Schwabhäuser, Szmielew and Gupta.-/


class tarski_preneutral (Point : Type) := 
  (Bet : Point → Point → Point → Prop)
  (Cong : Point → Point → Point → Point → Prop)
  (cong_pseudo_reflexivity : ∀ A B, Cong A B B A)
  (cong_inner_transitivity : ∀ A B C D E F, Cong A B C D → Cong A B E F → Cong C D E F)
 (cong_identity : ∀ (A B C), (Cong A B C C) → A = B)
  (segment_construction : ∀ A B C D, ∃ X, Bet A B X ∧ Cong B X C D)
  (five_segment : ∀ A A' B B' C C' D D', Cong A B A' B' →
   Cong B C B' C' → Cong A D A' D' →Cong B D B' D' →
   Bet A B C → Bet A' B' C' → A ≠ B → Cong C D C' D')
  (between_identity : ∀ A B, Bet A B A → A = B) 
   (between_identity2 : ∀ A B, ¬ Bet A B A)
  (inner_pasch : ∀ A B C P Q,
   Bet A P C → Bet B Q C →
   ∃ X, Bet P X B ∧ Bet Q X A)
  (PA : Point) 
  (PB : Point)
  (PC : Point)
  (lower_dim : ¬ (Bet PA PB PC ∨ Bet PB PC PA ∨ Bet PC PA PB))

namespace tarski_preneutral
variables {Point : Type}
variable [tarski_preneutral Point]

/-- The points a, b, c, d, a', b', c', d' form one
outer five-line configuration, -/

def OFSC (A B C D A' B' C' D' : Point) := Bet A B C ∧ Bet A' B' C' ∧
Cong A B A' B' ∧ Cong B C B' C' ∧ Cong A D A' D' ∧ Cong B D B' D'


-- /-- Tarski definition 3.8 -/

def Bet_4 (A1 A2 A3 A4: Point) :=
   Bet A1 A2 A3 ∧ Bet A2 A3 A4 ∧ Bet A1 A3 A4 ∧ Bet A1 A2 A4

-- def 4.1.

def IFSC (A B C D A' B' C' D' : Point) :=
   Bet A B C ∧ Bet A' B' C' ∧
   Cong A C A' C' ∧ Cong B C B' C' ∧
   Cong A D A' D' ∧ Cong C D C' D'

-- def 4.4.

def Cong_3 (A B C A' B' C' : Point) :=
  Cong A B A' B' ∧ Cong A C A' C' ∧ Cong B C B' C'

def Cong_4 (P1 P2 P3 P4 Q1 Q2 Q3 Q4: Point) :=
  Cong P1 P2 Q1 Q2 ∧ Cong P1 P3 Q1 Q3 ∧ Cong P1 P4 Q1 Q4 ∧
  Cong P2 P3 Q2 Q3 ∧ Cong P2 P4 Q2 Q4 ∧ Cong P3 P4 Q3 Q4

def Cong_5 (P1 P2 P3 P4 P5 Q1 Q2 Q3 Q4 Q5 : Point):=
  Cong P1 P2 Q1 Q2 ∧ Cong P1 P3 Q1 Q3 ∧
  Cong P1 P4 Q1 Q4 ∧ Cong P1 P5 Q1 Q5 ∧
  Cong P2 P3 Q2 Q3 ∧ Cong P2 P4 Q2 Q4 ∧ Cong P2 P5 Q2 Q5 ∧
  Cong P3 P4 Q3 Q4 ∧ Cong P3 P5 Q3 Q5 ∧ Cong P4 P5 Q4 Q5

-- def 4.10.

def Col (A B C : Point) := A = B ∨ 
A = C ∨ C = B ∨ Bet A B C ∨ Bet B C A ∨ 
Bet C A B ∨ Bet A C B ∨ Bet B A C ∨ Bet C B A


-- def 4.15.

def FSC (A B C D A' B' C' D' : Point):=
  Col A B C ∧ Cong_3 A B C A' B' C' ∧ Cong A D A' D' ∧ Cong B D B' D'

-- def 5.4.

def Le (A B C D: Point) := ∃ E, Bet C E D ∧ Cong A B C E

def Ge (A B C D: Point) := Le C D A B

-- def 5.14.

def Lt (A B C D : Point):= Le A B C D ∧ ¬ Cong A B C D

def Gt (A B C D: Point) := Lt C D A B

/-- B belongs to the ray PA -/

def Out (P A B: Point) := A ≠ P ∧ B ≠ P ∧ (Bet P A B ∨ Bet P B A)

-- def 6.22.

def Inter (A1 A2 B1 B2 X: Point) :=
 (∃ P, Col P B1 B2 ∧ ¬Col P A1 A2) ∧
 Col A1 A2 X ∧ Col B1 B2 X

-- def 7.1.

def Midpoint (M A B: Point) := Bet A M B ∧ Cong A M M B

-- def 8.1.

def Per (A B C: Point) := ∃ C', Midpoint B C C' ∧ Cong A C A C'

-- def 8.11.

def Perp_at (X A B C D : Point):=
  A ≠ B ∧ C ≠ D ∧ Col X A B ∧ Col X C D ∧
  (∀ U V, Col U A B → Col V C D → Per U X V)

-- def 8.11.

def Perp (A B C D: Point) := ∃ X, Perp_at X A B C D

/--P and Q are on opposite sides of
line AB-/

def TS (A B P Q: Point) :=
  ¬ Col P A B ∧ ¬ Col Q A B ∧ ∃ T, Col T A B ∧ Bet P T Q

def ReflectP (A A' C: Point) := Midpoint C A A'

/--P and Q are on the same side of
line AB.-/

def OS (A B P Q: Point) := ∃ R, TS A B P R ∧ TS A B Q R

-- Satz 9.33.

def Coplanar (A B C D : Point):=
  ∃ X, (Col A B X ∧ Col C D X) ∨
            (Col A C X ∧ Col B D X) ∨
            (Col A D X ∧ Col B C X)

-- def 10.3.

def ReflectL (P' P A B : Point):=
  (∃ X, Midpoint X P P' ∧ Col A B X) ∧ (Perp A B P P' ∨ P = P')

def Reflect (P' P A B : Point) :=
 (A ≠ B ∧ ReflectL P' P A B) ∨ (A = B ∧ Midpoint A P P')

def ReflectL_at (M P' P A B: Point) :=
  (Midpoint M P P' ∧ Col A B M) ∧ (Perp A B P P' ∨ P = P')

def Reflect_at (M P' P A B: Point) :=
 (A ≠ B ∧ ReflectL_at M P' P A B) ∨ (A = B ∧ A = M ∧ Midpoint M P P')

-- def 11.2.

def CongA (A B C D E F: Point) :=
  A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧
  ∃ A', ∃ C', ∃ D', ∃ F',
  Bet B A A' ∧ Cong A A' E D ∧
  Bet B C C' ∧ Cong C C' E F ∧
  Bet E D D' ∧ Cong D D' B A ∧
  Bet E F F' ∧ Cong F F' B C ∧
  Cong A' C' D' F'


def InAngle (P A B C : Point):=
  A ≠ B ∧ C ≠ B ∧ P ≠ B ∧ ∃ X, Bet A X C ∧ (X = B ∨ Out B X P)


def LeA (A B C D E F : Point):= ∃ P, InAngle P D E F ∧ CongA A B C D E P

def GeA (A B C D E F: Point) := LeA D E F A B C


def LtA (A B C D E F: Point) := LeA A B C D E F ∧ ¬ CongA A B C D E F

def GtA (A B C D E F: Point) := LtA D E F A B C


def Acute (A B C: Point) :=
  ∃ A' B' C', Per A' B' C' ∧ LtA A B C A' B' C'


def Obtuse (A B C: Point) :=
  ∃ A' B' C', Per A' B' C' ∧ GtA A B C A' B' C'


def Par_strict (A B C D: Point) :=
  A ≠ B ∧ C ≠ D ∧ Coplanar A B C D ∧ ¬ ∃ X, Col X A B ∧ Col X C D

def Par (A B C D: Point) :=
  Par_strict A B C D ∨ (A ≠ B ∧ C ≠ D ∧ Col A C D ∧ Col B C D)


def EqA (a1 a2 : Point → Point → Point → Prop) :=
  ∀ A B C, a1 A B C ↔ a2 A B C.

-- def 13.9.

def Perp2 (A B C D P : Point):=
  ∃ X Y, Col P X Y ∧ Perp X Y A B ∧ Perp X Y C D.

-- def 14.1.

def Ar1 (O E A B C : Point):=
 O ≠ E ∧ Col O E A ∧ Col O E B ∧ Col O E C

def Ar2 (O E E' A B C : Point):=
 ¬ Col O E E' ∧ Col O E A ∧ Col O E B ∧ Col O E C

-- def 14.2.

def Pj (A B C D : Point):= Par A B C D ∨ C = D

-- def 14.3.

def Sum (O E E' A B C: Point) :=
 Ar2 O E E' A B C ∧
 ∃ A' C',
 Pj E E' A A' ∧ Col O E' A' ∧
 Pj O E A' C' ∧
 Pj O E' B C' ∧
 Pj E' E C' C

def Proj (P Q A B X Y : Point):=
  A ≠ B ∧ X ≠ Y ∧ ¬Par A B X Y ∧ Col A B Q ∧ (Par P Q X Y ∨ P = Q)

def Sump (O E E' A B C: Point) :=
 Col O E A ∧ Col O E B ∧
 ∃ A' C' P',
   Proj A A' O E' E E' ∧
   Par O E A' P' ∧
   Proj B C' A' P' O E' ∧
   Proj C' C O E E E'

-- def 14.4.

def Prod (O E E' A B C: Point) :=
 Ar2 O E E' A B C ∧
 ∃ B', Pj E E' B B' ∧ Col O E' B' ∧ Pj E' A B' C

def Prodp (O E E' A B C: Point) :=
 Col O E A ∧ Col O E B ∧
 ∃ B', Proj B B' O E' E E' ∧ Proj B' C O E A E'

-- def 14.8.

def Opp (O E E' A B : Point) := Sum O E E' B A O

-- def 14.38.

def Diff (O E E' A B C: Point) :=
  ∃ B', Opp O E E' B B' ∧ Sum O E E' A B' C

def sum3 (O E E' A B C S: Point) :=
  ∃ AB, Sum O E E' A B AB ∧ Sum O E E' AB C S

def Sum4 (O E E' A B C D S: Point) :=
  ∃ ABC, sum3 O E E' A B C ABC ∧ Sum O E E' ABC D S

def sum22 (O E E' A B C D S: Point) :=
  ∃ AB CD, Sum O E E' A B AB ∧ Sum O E E' C D CD ∧ Sum O E E' AB CD S

def Ar2_4 (O E E' A B C D: Point) :=
  ¬ Col O E E' ∧ Col O E A ∧ Col O E B ∧ Col O E C ∧ Col O E D

-- def 14.34.

def Ps (O E A: Point) := Out O A E

def Ng (O E A: Point) := A ≠ O ∧ E ≠ O ∧ Bet A O E 

def Equilateral (A B C : Point) := (Cong A B B C) ∧ (Cong B C C A)

-- def 14.38.

def LtP (O E E' A B : Point ) := ∃ D, Diff O E E' B A D ∧ Ps O E D

def LeP( O E E' A B : Point) := LtP O E E' A B ∨ A = B

def Length (O E E' A B L : Point) :=
 O ≠ E ∧ Col O E L ∧ LeP O E E' O L ∧ Cong O L A B

-- def 15.1.

def Is_length (O E E' A B L : Point ) :=
 Length O E E' A B L ∨ (O = E ∧ O = L)

def Sumg (O E E' A B C: Point ) :=
  Sum O E E' A B C ∨ (¬ Ar2 O E E' A B B ∧ C = O)

def Prodg (O E E' A B C : Point ) :=
  Prod O E E' A B C ∨ (¬ Ar2 O E E' A B B ∧ C = O)

def PythRel (O E E' A B C : Point ):=
  Ar2 O E E' A B C ∧
  ((O = B ∧ (A = C ∨ Opp O E E' A C)) ∨
   ∃ B', Perp O B' O B ∧ Cong O B' O B ∧ Cong O C A B')

-- -- def 16.1. We skip the case of dimension 1.

def Cs (O E S U1 U2 : Point) := O ≠ E ∧ Cong O E S U1 ∧ Cong O E S U2 ∧ Per U1 S U2 


-- def 16.5. P is of coordinates (X,Y) in the 
-- grip SU1U2 using unit length OE.

def Projp (P Q A B: Point) :=
  A ≠ B ∧ ((Col A B Q ∧ Perp A B P Q) ∨ (Col A B P ∧ P = Q))

def Cd (O E S U1 U2 P X Y: Point) :=
  Cs O E S U1 U2 ∧ Coplanar P S U1 U2 ∧
  (∃ PX, Projp P PX S U1 ∧ Cong_3 O E X S U1 PX) ∧
  (∃ PY, Projp P PY S U2 ∧ Cong_3 O E Y S U2 PY)

def BetS (A B C : Point): Prop := Bet A B C ∧ A ≠ B ∧ B ≠ C


-- def of the sum of segments. SumS A B C D E F 
--means that AB + CD = EF.

def SumS (A B C D E F: Point) := ∃ P Q R,
  Bet P Q R ∧ Cong P Q A B ∧ Cong Q R C D ∧ Cong P R E F

-- PQ is the perpendicular bisector of segment AB

def Perp_bisect (P Q A B: Point) := ReflectL A B P Q ∧ A ≠ B

def Perp_bisect_bis (P Q A B: Point) :=
  ∃ I, Perp_at I P Q A B ∧ Midpoint I A B

def Is_on_perp_bisect (P A B: Point) := Cong A P P B

/--The sumof angles ABC and DEF is equal to GHI  -/ 

def SumA (A B C D E F G H I: Point) :=
 ∃ J, CongA C B J D E F ∧ ¬ OS B C A J ∧ CongA A B J G H I

/-- The SAMS predicate describes the fact that 
(the sum of the two angles \ABC and \DEF is at most 180 degrees-/ 

def SAMS (A B C D E F: Point) :=
  A ≠ B ∧ (Out E D F ∨ ¬ Bet A B C) ∧
  ∃ J, CongA C B J D E F ∧ ¬ OS B C A J ∧ ¬ TS A B C J

/--Supplementary angles -/ 

def SuppA (A B C D E F: Point) :=
A ≠ B ∧ ∃ A', Bet A B A' ∧ CongA D E F C B A'

/-- def of the sum of the interior angles 
of a triangle. TriSumA A B C D E F means that
the sum of the angles of the triangle ABC is equal to the angle DEF -/

def TriSumA (A B C D E F: Point) :=
  ∃ G H I, SumA A B C B C A G H I ∧ SumA G H I C A B D E F

/-- The difference between a straight angle 
and the sum of the angles of the triangle ABC.
 It is a non-oriented angle, so we can't discriminate
 between positive and negative difference -/ 

def Defect (A B C D E F: Point) := ∃ G H I J K L,
  TriSumA A B C G H I ∧ Bet J K L ∧ SumA G H I D E F J K L

/-- P is on the circle of center A going through B-/

def OnCircle (P A B: Point) := Cong A P A B

/-- P is inside or on the circle of center A going through B-/

def InCircle (P A B: Point) := Le A P A B

/-- P is outside or on the circle of center A going through B-/

def OutCircle (P A B: Point) := Le A B A P

/-- P is strictly inside the circle of center A going through B-/

def InCircleS (P A B: Point) := Lt A P A B

/-- P is strictly outside the circle of center A going through B-/

def OutCircleS (P A B: Point) := Lt A B A P

def EqC (A B C D : Point):= ∀ X, OnCircle X A B ↔ OnCircle X C D

/--The circles of center A passing through B 
and of center C passing through D intersect in 
two distinct points P and Q -/

def InterCCAt (A B C D P Q: Point) := 
¬ EqC A B C D ∧ P≠Q ∧ OnCircle P C D ∧ OnCircle Q C D 
∧ OnCircle P A B ∧ OnCircle Q A B

/-- The circles of center A passing through B and of center C passing
through D have two distinct intersections.-/

def InterCC (A B C D : Point) := ∃ P Q, InterCCAt A B C D P Q

/--The circles of center A passing through B 
and of center C passing through D are tangent-/

def TangentCC (A B C D : Point) := ∃! X, OnCircle X A B ∧ OnCircle X C D

/--The line AB is tangent to the circle OP-/

def Tangent (A B O P : Point):= ∃! X, Col A B X ∧ OnCircle X O P

def TangentAt (A B O P T: Point) := Tangent A B O P ∧ Col A B T ∧ OnCircle T O P

/-- C is on the graduation based on AB -/
inductive Grad : Point → Point → Point → Prop 
| grad_init : ∀ A B, Grad A B B
| grad_stab : ∀ A B C C',
                  Grad A B C →
                  Bet A C C' → Cong A B C C' →
                  Grad A B C'

def Reach (A B C D : Point) := ∃ B', Grad A B B' ∧ Le C D A B'

/-- There exists n such that AC = n times AB and DF = n times DE -/ 
inductive Grad2 : Point → Point → Point → Point → Point → Point → Prop 
| grad2_init : ∀ A B D E, Grad2 A B B D E E
| grad2_stab : ∀ A B C C' D E F F',
                   Grad2 A B C D E F →
                   Bet A C C' → Cong A B C C' →
                   Bet D F F' → Cong D E F F' →
                   Grad2 A B C' D E F'

/-- Graduation based on the powers of 2 -/
inductive GradExp : Point → Point → Point → Prop 
| gradexp_init : ∀ A B, GradExp A B B
| gradexp_stab : ∀ A B C C',
                     GradExp A B C →
                     Bet A C C' → Cong A C C C' →
                     GradExp A B C'

inductive GradExp2 : Point → Point → Point → Point → Point → Point → Prop 
| gradexp2_init : ∀ A B D E, GradExp2 A B B D E E
| gradexp2_stab : ∀ A B C C' D E F F',
                  GradExp2 A B C D E F →
                  Bet A C C' → Cong A C C C' →
                  Bet D F F' → Cong D F F F' →
                  GradExp2 A B C' D E F'

/--There exists n such that the angle DEF is congruent to n times the angle ABC -/
inductive GradA : Point → Point → Point → Point → Point → Point →
                  Prop 
| grada_init : ∀ A B C D E F, CongA A B C D E F → GradA A B C D E F
| grada_stab : ∀ A B C D E F G H I,
                   GradA A B C D E F →
                   SAMS D E F A B C → SumA D E F A B C G H I →
                   GradA A B C G H I

/-- There exists n such that the angle DEF is congruent to 2^n times the angle ABC -/
inductive GradAExp : Point → Point → Point → Point → Point → Point →
                     Prop 
| gradaexp_init : ∀ A B C D E F, CongA A B C D E F → GradAExp A B C D E F
| gradaexp_stab : ∀ A B C D E F G H I,
                  GradAExp A B C D E F →
                  SAMS D E F D E F → SumA D E F D E F G H I →
                  GradAExp A B C G H I


def Parallelogram_strict (A B A' B' : Point) :=
  TS A A' B B' ∧ Par A B A' B' ∧ Cong A B A' B'

def Parallelogram_flat( A B A' B' : Point):=
  Col A B A' ∧ Col A B B' ∧
  Cong A B A' B' ∧ Cong A B' A' B ∧
  (A ≠ A' ∨ B ≠ B')

def Parallelogram (A B A' B' : Point):=
  Parallelogram_strict A B A' B' ∨ Parallelogram_flat A B A' B'

def Plg (A B C D : Point):=
  (A ≠ C ∨ B ≠ D) ∧ ∃ M, Midpoint M A C ∧ Midpoint M B D

def Rhombus (A B C D: Point) := Plg A B C D ∧ Cong A B B C

def Rectangle (A B C D : Point):= Plg A B C D ∧ Cong A C B D

def Square (A B C D : Point):= Rectangle A B C D ∧ Cong A B B C

def Kite ( A B C D : Point):= Cong B C C D ∧ Cong D A A B

def Saccheri (A B C D : Point):=
  Per B A D ∧ Per A D C ∧ Cong A B C D ∧ OS A D B C

def Lambert (A B C D : Point):=
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ D ∧ Per B A D ∧ Per A D C ∧ Per A B C

def EqV (A B C D: Point) := Parallelogram A B D C ∨ A = B ∧ C = D

def SumV (A B C D E F: Point) := ∀ D', EqV C D B D' → EqV A D' E F

def SumV_exists (A B C D E F: Point) := ∃ D', EqV B D' C D ∧ EqV A D' E F

def Same_dir (A B C D: Point) :=
  A = B ∧ C = D ∨ ∃ D', Out C D D' ∧ EqV A B C D'

def Opp_dir (A B C D: Point) := Same_dir A B D C

def CongA_3 (A B C A' B' C': Point) :=
  CongA A B C A' B' C' ∧ CongA B C A B' C' A' ∧ CongA C A B C' A' B'


def segment_circle  (A B P Q: Point) := 
  InCircle P A B →
  OutCircle Q A B →
  ∃ Z, Bet P Z Q ∧ OnCircle Z A B


/--Given a line UV which contains a point inside the circle, 
there is a point of line UV which is on the circle. -/

def one_point_line_circle (A B U V P: Point) := 
  Col U V P → U ≠ V → Bet A P B →
  ∃ Z, Col U V Z ∧ OnCircle Z A B

def circle_circle_bis (Point : Type) [tarski_preneutral Point] :=∀(A B C D P Q: Point),
  OnCircle P C D →
  InCircle P A B →
  OnCircle Q A B →
  InCircle Q C D →
  ∃ Z, OnCircle Z A B ∧ OnCircle Z C D


/--Given two circles (A,B) and (C,D), 
if there are two points of (C,D) one inside and one outside (A,B)
 then there are two points of intersection of the two circles. 
They are distinct if the inside and outside properties are strict. -/

def circle_circle_two  (A B C D P Q: Point) :=
  OnCircle P C D →
  OnCircle Q C D →
  InCircle P A B →
  OutCircle Q A B →
  ∃ Z1 Z2,
    OnCircle Z1 A B ∧ OnCircle Z1 C D ∧
    OnCircle Z2 A B ∧ OnCircle Z2 C D ∧
    (InCircleS P A B → OutCircleS Q A B → Z1≠Z2)

/--Nested A B describes the fact that the sequences A and B form
 the end points of nested non-degenerate segments -/

 def Nested (A B: nat → Point → Prop) :=
  (∀ n, ∃ An, A n An) ∧ (∀ n, ∃ Bn, B n Bn) ∧
  (∀ n An Am Bm Bn, A n An → A (nat.succ n) Am → B (nat.succ n) Bm → B n Bn → 
    Bet An Am Bm ∧ Bet Am Bm Bn ∧ Am ≠ Bm)

def cantor_s_axiom := ∀ (A B: nat → Point → Prop), Nested A B →
  ∃ X, ∀ n An Bn, A n An → B n Bn → Bet An X Bn

def dedekind_s_axiom := ∀ (Xi Upsilon : Point → Prop),
  (∃ A, ∀ X Y, Xi X → Upsilon Y → Bet A X Y) →
  (∃ B, ∀ X Y, Xi X → Upsilon Y → Bet X B Y)

def O   := (PA : Point)
def E := (PB: Point)
def E'  := (PC: Point)


@[simp] lemma cong_reflexivity (A B : Point):
 Cong A B A B := 
begin
    rintros,
    apply (cong_inner_transitivity B A A B); apply cong_pseudo_reflexivity,
end 


lemma cong_symmetry (A B C D : Point) (HCong: Cong A B C D ):   Cong C D A B :=
begin
  rintros,
  eapply cong_inner_transitivity _ _ _ _ _ _ HCong,
  apply cong_reflexivity,
end 

lemma cong_transitivity (A B C D E F : Point) (HCong1 : Cong A B C D)
 (HCong2: Cong C D E F) : Cong A B E F :=

begin
  rintros,
  apply cong_inner_transitivity _ _ _ _ _ _ (cong_symmetry _ _ _ _ HCong1),
  tauto!,
end 

lemma cong_left_commutativity (A B C D : Point)  (HCong: Cong A B C D ):   Cong B A C D:=

begin
  rintros,
  apply cong_inner_transitivity _ _ _ _ _ _ ,
  apply cong_symmetry, 
  apply cong_pseudo_reflexivity, 
  tauto!,
end 

lemma cong_right_commutativity (A B C D : Point) (HCong: Cong A B C D ): Cong A B D C := 

begin
  rintros,
  apply cong_symmetry,
  apply cong_left_commutativity _ _ _ _ (cong_symmetry _ _ _ _ HCong),
end 

lemma cong_trivial_identity (A B : Point): Cong A A B B :=
begin
  rintros,
  cases segment_construction A B A A with E H,
  apply cong_inner_transitivity,
  exact H.2,
  have HBE: B = E,
    apply cong_identity,
    exact H.2,
  subst_vars,
  apply cong_reflexivity,
end 


lemma cong_commutativity (A B C D : Point) (HCong: Cong A B C D ): Cong B A D C:=
begin
  rintros,
  apply cong_left_commutativity,
  apply cong_right_commutativity _ _ _ _ HCong,
end 

mk_simp_attribute cong_simp "simplification lemmas for congruence"

attribute [cong_simp] cong_symmetry cong_left_commutativity cong_commutativity 
cong_right_commutativity 

lemma five_segment_with_def ( A B C D A' B' C' D': Point):
 OFSC A B C D A' B' C' D' → A≠B → Cong C D C' D':=
begin
    unfold OFSC,
    rintros,
    apply (five_segment A A' B B'), 
    all_goals {tauto!,},
end 


lemma cong_diff (A B C D : Point) : A ≠ B → Cong A B C D → C ≠ D:=
begin
  rintros HAB HCong,
  intro heq,
  subst_vars,
  apply HAB,
  apply cong_identity _ _ _ HCong,
end 

lemma cong_diff2 (A B C D : Point): C ≠ D → Cong A B C D → A ≠ B:=
begin
  rintros HCD HCong,
  intro heq,
  subst_vars,
  apply HCD,
  apply cong_identity _ _ _ (cong_symmetry _ _ _ _ HCong),
end 



lemma cong_reverse_identity { A C D: Point}:
 Cong A A C D → C=D:=
begin
    rintros H,
    replace H:= cong_symmetry _ _ _ _ H,
    eapply cong_identity C D A,
    tauto,
end


lemma l2_11 ( A B C A' B' C': Point):
 Bet A B C → Bet A' B' C' → Cong A B A' B' → Cong B C B' C' → Cong A C A' C':=

begin
    rintros HBet HCong1 HCong2 HCong3,
    by_cases A = B,
      subst B,
      have : (A' = B'),
       apply (cong_identity A' B' A),
       simp * with cong_simp,
       subst_vars, assumption,
    apply cong_commutativity,
    apply (five_segment A A' B B' C C' A A'), 
    any_goals {tauto!,},
    apply cong_trivial_identity,
    exact cong_commutativity _ _ _ _ HCong2,
end 



lemma construction_uniqueness (Q A B C X Y : Point):
 Q ≠ A → Bet Q A X → Cong A X B C → Bet Q A Y → Cong A Y B C → X=Y:=
begin
    rintros HQA HBet HCong HBet1 HCong2,
    have HCong3: Cong A X A Y, apply cong_transitivity _ _ B C, 
    assumption, simp * with cong_simp,
    have HCong4: Cong Q X Q Y, apply l2_11 Q A X Q A Y, repeat {assumption,},
    apply cong_reflexivity,
    have HOFSC: (OFSC Q A X Y Q A X X), unfold OFSC, 
    refine ⟨by assumption, by assumption, cong_reflexivity Q A, cong_reflexivity A X,
     cong_symmetry Q X Q Y HCong4,cong_symmetry A X A Y HCong3⟩,
    replace HOFSC:= five_segment_with_def _ _ _ _ _ _ _ _ HOFSC HQA,
    apply cong_identity _ _ X, tauto!, 
end 


lemma bet_col (A B C: Point) (H: Bet A B C) : Col A B C := 
begin
    intros, 
    unfold Col,
    simp*,
end

lemma between_trivial (A B : Point): Bet A B B :=
begin
    rintros,
    cases segment_construction A B B B with x H,
    have Hxb: x = B,
    apply cong_reverse_identity,
    replace H:= cong_right_commutativity _ _ _ _ (cong_symmetry _ _ _ _ H.2),
    tauto!,
    subst_vars,
    tauto!,

end 

lemma between_symmetry (A B C: Point) (H: Bet A B C ): Bet C B A := sorry 


lemma Bet_cases ( A B C : Point): Bet A B C ∨ Bet C B A → Bet A B C :=
begin
    rintros HBet,
    cases_type or, assumption,
    exact between_symmetry _ _ _ HBet,
end


lemma between_trivial2 (A B : Point): Bet B B A :=
begin
    rintros,
    apply between_symmetry,
    apply between_trivial,
end

lemma between_equality ( A B C : Point): Bet A B C → Bet B A C → A = B :=
begin
    rintros,
    have : ∃ x, Bet B x B ∧ Bet A x A, apply (inner_pasch A B C),
    repeat {assumption,}, 
    cases this with x H1, 
    rcases ⟨between_identity _ _ H1.1, between_identity _ _ H1.2⟩ with ⟨H1, H2⟩,
    subst_vars,
end

lemma between_equality_2 ( A B C : Point)( H :  Bet A B C): Bet A C B → B = C:=
begin
    rintros H1,
    apply between_equality _ _ _ (between_symmetry _ _ _ H1) (between_symmetry _ _ _ H),
end


lemma between_inner_transitivity ( A B C D: Point):Bet A B D → Bet B C D → Bet A B C:= sorry


lemma bet.neq (A B C : Point): Bet A B C → B ≠ C ∧ A ≠ B ∧ A ≠ C := sorry

lemma bet_neqL { A B C : Point} ( H : Bet A B C):(A ≠ B) :=sorry

lemma bet_neqR ( A B C : Point) ( H : Bet A B C): (B≠C) :=sorry

lemma bet_neqLR ( A B C : Point) ( H : Bet A B C): (A ≠ C) :=sorry



lemma not_bet_distincts ( A B C : Point): ¬ Bet A B C → A ≠ B ∧ B ≠ C:=sorry

meta def betidentity : tactic unit := `[ try {simp*} ] >> (`[ subst_vars ] >>  ((`[ apply between_trivial, simp *] )
<|> (`[apply between_trivial2, simp *]))) <|> (`[ subst_vars ] >> ((`[ apply bet_col , simp *] )))


meta def bet : tactic unit := (`[ subst_vars ] >>  ((`[ apply between_symmetry, simp *] )))


lemma col1 (A B C : Point) : Col A B C = Col A C B := 
begin
  rintros, simp [Col], tauto!,
end 

lemma col2 (A B C : Point) : Col A B C = Col B A C := 
begin
  rintros, simp [Col], tauto!,
end 

lemma col3 (A B C : Point) : Col A B C = Col B C A := 
begin
  rintros, simp [Col], tauto!,
end 

lemma col4 (A B C : Point) : Col A B C = Col C A B := 
begin
  rintros, simp [Col], tauto!,
end 

lemma col5 (A B C : Point) : Col A B C = Col C B A :=
begin
  rintros, simp [Col], tauto!,
end 

attribute [simp] between_trivial between_trivial2 bet_col 
 

mk_simp_attribute geometry_simp "simplification lemmas for geometry"

attribute [geometry_simp] between_symmetry-- bet_col 

mk_simp_attribute bet_simp "simplification lemmas for bet"


lemma col_trivial_1 (A B : Point) : Col A A B := 
begin
  rintros,
  simp [Col],
end

lemma col_trivial_2 (A B : Point) : Col A B B := 
begin
  rintros,
  simp [Col],
end

lemma col_trivial_3 (A B : Point) : Col A B A := 
begin
  rintros,
  simp [Col],
end

lemma col_3 (X Y A B C: Point):
 X ≠ Y →
 Col X Y A → Col X Y B → Col X Y C →
 Col A B C:=sorry

mk_simp_attribute col_simp "simplification lemmas for bet"

attribute [col_simp] col1 col2 col3 col4 col5 col_trivial_1 col_trivial_2 col_trivial_3

lemma nesymm (A B : Point) : ¬ (A = B) ↔ ¬ (B = A) := 
  begin
    cc,
  end 

 lemma cong1 (A B C D : Point) : (Cong A B C D )= Cong A B D C := 
 begin
  rintros, simp [Cong], 
  apply iff.intro, 
  all_goals
  {
    intros H,
  exact cong_right_commutativity _ _ _ _ H,},
 end 

 lemma cong2 (A B C D : Point) : (Cong A B C D )= Cong B A C D := 
  begin
  rintros, simp [Cong], 
  apply iff.intro, 
  all_goals
  {
    intros H,
  exact cong_left_commutativity _ _ _ _ H,},
 end 
 lemma cong3 (A B C D : Point) : (Cong A B C D )= Cong B A D C := 
  begin
  rintros, simp [Cong], 
  apply iff.intro, 
  all_goals
  {
    intros H,
  exact cong_commutativity _ _ _ _ H,},
 end 

 lemma cong4 (A B C D : Point) : (Cong A B C D )= Cong C D A B := 
  begin
  rintros, simp [Cong], 
  apply iff.intro, 
  all_goals
  {
    intros H,
  exact cong_symmetry _ _ _ _ H,},
 end 

 lemma cong5 (A B C D : Point) : (Cong A B C D )= Cong C D B A := 
  begin
  rintros, simp [Cong], 
  apply iff.intro, 
  {
    intros H,
    exact (cong_right_commutativity _ _ _ _ (cong_symmetry _ _ _ _ H))
  },
  { intros H,
    exact cong_left_commutativity _ _ _ _ (cong_symmetry _ _ _ _ H),
  },
 end 

 lemma cong6 (A B C D : Point) : (Cong A B C D )= Cong D C A B := 
  begin
    rintros, simp [Cong], 
    apply iff.intro, 
    {
      intros H,
      exact (cong_symmetry _ _ _ _ (cong_right_commutativity _ _ _ _ H)),
    },
    {intros H,
      exact (cong_symmetry _ _ _ _ (cong_left_commutativity _ _ _ _ H)),
    },
 end 


 lemma cong7 (A B C D : Point) : (Cong A B C D )= Cong D C B A := 
  begin
    rintros,
    simp [Cong], 
    apply iff.intro, 
    all_goals
    {
      intros H,
      exact (cong_symmetry _ _ _ _ (cong_commutativity _ _ _ _ H)),
    },
  end 


meta def cleanup : tactic unit := `[ try 
{ simp only [col1, col2, col3, col4, col5, ne, 
nesymm, cong1, cong2, cong3, cong4, cong5, cong6, cong7] at *}; 
try {simp*}]



meta def cleanup_hyps : tactic unit := `[ try { simp only [col1, col2, 
col3, col4, col5, ne, nesymm] at *} ]


lemma cong_perm (A B C D : Point) (H: Cong A B C D ):
 Cong A B C D → Cong A B C D ∧ Cong A B D C ∧ Cong B A C D ∧ Cong B A D C ∧
 Cong C D A B ∧ Cong C D B A ∧ Cong D C A B ∧ Cong D C B A :=
 begin
  rintros,
  repeat {cleanup,},
 end 



lemma col_permutation_1 ( A B C: Point):Col A B C → Col B C A:=
  begin
   cleanup,
  end 


lemma col_permutation_2 ( A B C: Point): Col A B C → Col C A B:= 
  begin
   cleanup,
  end 


lemma col_permutation_3 ( A B C: Point):Col A B C → Col C B A:=
begin
   cleanup,
  end 


lemma col_permutation_4 ( A B C: Point):Col A B C → Col B A C:=
  begin
   cleanup,
  end 


lemma col_permutation_5 ( A B C: Point): Col A B C → Col A C B:=
  begin
   cleanup,
  end 

lemma Col_perm ( A B C: Point):
 Col A B C →
 Col A B C ∧ Col A C B ∧ Col B A C ∧
 Col B C A ∧ Col C A B ∧ Col C B A :=
 begin
   cleanup,
 end 
 
lemma not_col_distincts {A B C: Point} :
 ¬ Col A B C →
 ¬ Col A B C ∧ A ≠ B ∧ B ≠ C ∧ A ≠ C:= 
begin
  rintros H, 
  refine ⟨ by assumption,_,_,_⟩,
  all_goals { intro heq,
  subst_vars, apply H, simp with col_simp,
   },

end 


lemma NCol_perm : ∀ (A B C: Point),
 ¬ Col A B C → ¬ Col A B C ∧ ¬ Col A C B ∧ ¬ Col B A C ∧
 ¬ Col B C A ∧ ¬ Col C A B ∧ ¬ Col C B A:=
 begin
  cleanup,
 end 


lemma col_cong_3_cong_3_eq : ∀ (A B C A' B' C1 C2: Point),
  A ≠B → Col A B C → Cong_3 A B C A' B' C1 → Cong_3 A B C A' B' C2 → C1 = C2 :=sorry 


lemma l11_3_bis (A B C D E F : Point): ( ∃ A', ∃ C', ∃ D' , ∃ F',
  Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧
 Cong_3 A' B C' D' E F') → CongA A B C D E F := sorry 



@[simp] lemma conga_refl  (A B C: Point) (H: A ≠ B) (H' : C ≠ B) : CongA A B C A B C := 
begin
  rintros,
  apply l11_3_bis,
  use [A, C, A, C],
  repeat {split,},
  repeat {tauto!,},
  any_goals {left, simp with bet_simp,},
  all_goals {apply cong_reflexivity,},
end 


lemma conga_sym {A B C A' B' C' : Point} (H: CongA A B C A' B' C') : CongA A' B' C' A B C := 
begin
  rintros,
  unfold CongA at H,
  rcases H with ⟨_,_,_,_,A0,C0,D0,F0, H3⟩,
  unfold CongA, cleanup,
  refine ⟨_,_,_,_⟩ ,
  use D0, repeat {tauto!,},
  use F0, refine ⟨by tauto!, by tauto!, _⟩ ,
  use A0, refine ⟨by tauto!, by tauto!,_⟩ , 
  use C0, refine ⟨by tauto!, by tauto!, _⟩ ,
  simp * with cong_simp,
end 

lemma conga_trans (A B C A' B' C' A'' B'' C'':Point):
  CongA A B C A' B' C' → CongA A' B' C' A'' B'' C'' →
  CongA A B C A'' B'' C'' :=sorry 

lemma conga_pseudo_refl (A B C: Point) (H: A ≠ B) ( H' : C ≠ B) :CongA A B C C B A :=sorry 


lemma cong3_conga { A B C A' B' C' : Point}
 (HAB: A ≠ B) (HCB: C ≠ B )  (H: Cong_3 A B C A' B' C') :
 CongA A B C A' B' C' :=sorry 

lemma conga_right_comm  (A B C D E F: Point) (H: CongA A B C D E F) : CongA A B C F E D:=

begin
  rintros,
  apply conga_trans _ _ _ D E F,
  apply H,
  unfold CongA at H,
  apply conga_pseudo_refl,
  repeat {tauto!,},
end 

lemma conga_left_comm  (A B C D E F: Point)(H: CongA A B C D E F) : CongA C B A D E F:=
begin
  rintros,
  apply conga_sym,
  apply conga_trans _ _ _ A B C,
    apply conga_sym,
    apply H,
  unfold CongA at H,
  apply conga_pseudo_refl,
  repeat {tauto!,},
end 


lemma conga_trivial_1 ( A B C D: Point):
  A≠B → C≠D → CongA A B A C D C :=
begin
  rintros HAB HCD,
  unfold CongA,
  refine ⟨by tauto!, by tauto!, by tauto!, by tauto!, _⟩,
  cases segment_construction B A D C with A' H,
  cases segment_construction D C B A with C' H1,
  use [A', A', C', C'],
  refine ⟨_,_,_,_,_,_,_,_,_⟩,
  any_goals {tauto!,},
  apply cong_trivial_identity A' C',
end


lemma conga_comm (A B C D E F: Point) (H: CongA A B C D E F) : CongA C B A F E D:= 
begin
apply conga_left_comm,
apply conga_right_comm,
assumption,
end 


lemma bet_conga_bet : ∀ (A B C A' B' C' : Point), Bet A B C →
  CongA A B C A' B' C' → Bet A' B' C' := sorry


lemma conga_line {A B C A' B' C': Point}:
 A ≠ B → B ≠ C → A' ≠ B' → B' ≠ C' → Bet A B C → Bet A' B' C' →
 CongA A B C A' B' C' := sorry 


lemma collinear_lemma (A B C : Point) 
(H : Col A B C ∨ Col A C B ∨ Col B A C ∨ Col B C A ∨ Col C B A ∨ Col C A B) :
  Col A B C := 
  begin
  cases_type* or,
  tauto,
  repeat {cleanup,}, 
  end 

lemma collinear_lemma' (A B C : Point) 
(H : Bet A B C ∨ Bet A C B ∨ Bet B A C ∨ Bet B C A ∨ Bet C B A ∨ Bet C A B) :
  Col A B C :=
  begin
  unfold Col,
  tauto!,
  end 


meta def collinear_tac : tactic unit :=  `[ subst_vars ] >> (`[ apply collinear_lemma, simp *] <|> 
`[ apply collinear_lemma', simp *])


lemma NCdistinct {A B C : Point} : ¬Col A B C → A ≠ B ∧ B ≠ C ∧
A ≠ C ∧ B ≠ A ∧ C ≠ B ∧ C ≠ A :=
begin 
  rintros HNCol ,
  any_goals {cleanup_hyps, cleanup},
  refine ⟨ _, _, _, _, _, _⟩,
  all_goals { 
    intro hEq,
    have : Col A B C, by collinear_tac, 
    tauto!,
  },
end 

lemma  not_col_permutation_1 (A B C : Point): ¬ Col A B C → ¬ Col B C A:=
begin
  cleanup,
end

lemma not_col_permutation_2 (A B C : Point): ¬ Col A B C → ¬ Col C A B:=
begin
  cleanup,
end
lemma not_col_permutation_3 (A B C : Point): ¬ Col A B C → ¬ Col C B A:=
begin
  cleanup,
end

lemma  not_col_permutation_4 (A B C : Point):¬ Col A B C → ¬ Col B A C:=
begin
  cleanup,
end

lemma  not_col_permutation_5 (A B C : Point): ¬ Col A B C → ¬ Col A C B:=
begin
  cleanup,
end

end tarski_preneutral



open tarski_preneutral


class tarski_neutral_dimensionless_with_decidable_point_equality (Point : Type) 
extends tarski_preneutral Point := 

(point_equality_decidability : ∀ (A B : Point), A = B ∨ ¬ A = B)

open tarski_neutral_dimensionless_with_decidable_point_equality
open tarski_preneutral

section 

variables {Point : Type}
variable  [tarski_neutral_dimensionless_with_decidable_point_equality Point]

variables x y z : Point 

def upper_dim_axiom (Point : Type) [tarski_preneutral Point] 
:= ∀ (A B C P Q : Point),
  P ≠ Q → Cong A P A Q → Cong B P B Q → Cong C P C Q →
  (Bet A B C ∨ Bet B C A ∨ Bet C A B)


def all_coplanar_axiom (Point : Type) [tarski_preneutral Point]
:= ∀(A B C D: Point), Coplanar A B C D


lemma upper_dim_implies_all_coplanar : 
upper_dim_axiom Point → all_coplanar_axiom Point :=sorry

lemma all_coplanar (A B C D: Point): Coplanar A B C D:=sorry



lemma lower_dim_ex  (Point : Type) [tarski_preneutral Point]: ∃ (A B C : Point),  ¬ (Bet A B C ∨ Bet B C A ∨ Bet C A B) :=
begin
  rintros, use[PA, PB, PC, lower_dim],
end 

lemma two_distinct_points : ∃ (X Y: Point), X ≠ Y:=sorry


lemma l4_2 (A B C D A' B' C' D': Point): IFSC A B C D A' B' C' D' → Cong B D B' D':=sorry


lemma eq_dec_implies_between_cong (A B : Point):
 A=B ∨ A≠B →
  ∀ (A B C: Point), Bet A C B → Cong A C A B → C=B:=sorry


lemma le_trivial {A C D : Point}: Le A A C D := 
begin
  rintros,
  unfold Le,
  use C,
  split,
  simp with bet_simp,
  apply cong_trivial_identity,
end 

lemma le_transitivity (A B C D E F: Point): Le A B C D → Le C D E F → Le A B E F:=sorry 

lemma between_cong (A B C : Point): Bet A C B → Cong A C A B → C=B:=
begin
  apply eq_dec_implies_between_cong, tauto!,
end



lemma cong__le (A B C D: Point): Cong A B C D → Le A B C D:=
begin
  rintros H,
  use D,
  split,
  repeat {cleanup,},
end 

lemma le_left_comm (A B C D: Point): Le A B C D → Le B A C D:=

begin
  rintros Hle,
  apply le_transitivity _ _ A B, 
  apply cong__le,
  repeat {cleanup,},
end 

lemma le_right_comm (A B C D: Point):  Le A B C D → Le A B D C :=
begin
  rintros Hle,
  apply le_transitivity _ _ C D, assumption,
  apply cong__le, cleanup,
end 

lemma le_comm (A B C D: Point): Le A B C D → Le B A D C:=
begin
  rintros, 
  apply le_left_comm,
  apply le_right_comm,
  assumption,
end

lemma lt_right_comm (A B C D: Point): Lt A B C D → Lt A B D C:=
begin
  rintros H,
  unfold Lt at *,
  constructor,
  apply le_right_comm _ _ _ _ H.1,
  cleanup,
end 

lemma lt_left_comm  (A B C D: Point): Lt A B C D → Lt B A C D:=
begin
  rintros H,
  unfold Lt at *,
  constructor,
  apply le_left_comm _ _ _ _ H.1,
  cleanup,
end 

lemma lt_comm (A B C D: Point): Lt A B C D → Lt B A D C :=
begin
  rintros H,
  apply lt_left_comm,
  exact lt_right_comm _ _ _ _ H,
end 

lemma gt_left_comm (A B C D : Point): Gt A B C D → Gt B A C D :=
begin
  rintros H,
  unfold Gt at *,
  exact lt_right_comm _ _ _ _ H,
end 

lemma gt_right_comm (A B C D : Point): Gt A B C D → Gt A B D C :=
begin
  rintros H,
  unfold Gt at *,
  exact lt_left_comm _ _ _ _ H,
end 

lemma gt_comm (A B C D : Point): Gt A B C D → Gt B A D C :=
begin
  rintros H,
  apply lt_left_comm,
  apply lt_right_comm,
  unfold Gt at *,
  cleanup,
end 

lemma l5_12_a (A B C : Point): Bet A B C → Le A B A C ∧ Le B C A C:=
  begin
    rintros Hbet,
    split,
      unfold Le,
      use B,
     cleanup,
    apply le_comm,
    unfold Le,
    use B,
    cleanup,
    exact between_symmetry _ _ _ Hbet,
  end 

lemma bet__le1213 (A B C : Point): Bet A B C → Le A B A C :=
  begin
    rintros Hbet,
    cases l5_12_a A B C Hbet,
    assumption,
  end 

lemma bet__lt1213 ( A B C: Point): B ≠ C → Bet A B C → Lt A B A C :=
  begin
    rintros HBC Hbet,
    constructor,
      apply bet__le1213,
      cleanup,
    intro heq,
    apply HBC, 
    apply between_cong,
    repeat {tauto!,}, 
  end 

lemma bet__lt2313 ( A B C: Point): A ≠ B → Bet A B C → Lt B C A C :=
begin
  rintros,
  apply lt_comm, 
  apply bet__lt1213,cleanup,
  simp * with geometry_simp,
end 

lemma point_construction_different : ∀ (A B : Point), ∃ C, Bet A B C ∧ B ≠ C:=
begin
    rintros,
    have tdp:= two_distinct_points,
    cases tdp with x tdp,
    cases tdp with y H,
    cases segment_construction A B x y with F H0,
    use F,
    cleanup,
    have: B ≠ F,
      unfold ne,
      intro,
      subst_vars, 
      have HCong:= cong_reverse_identity H0.2,
      contradiction,
    repeat {tauto!,},
end 

lemma between_exchange3 ( A B C D : Point) : Bet A B C → Bet A C D → Bet B C D:=
begin
  rintros H1 H2,
  have : ∃ x, Bet C x C ∧ Bet B x D,
    apply inner_pasch, repeat {apply between_symmetry,
    tauto!,},
    cases this with x H1,
    have: C = x,
      apply between_identity,
      tauto, subst_vars, tauto,
end 

lemma outer_transitivity_between2 ( A B C D:Point): Bet A B C → Bet B C D → B≠C → Bet A C D :=
begin
  rintros,
  cases segment_construction A C C D with x H,
  have H: x= D,
    apply construction_uniqueness B C C D,
    assumption,
    apply between_exchange3 A B C x,
    repeat {tauto!,},
    apply cong_reflexivity C D,
    subst x,
    tauto,
end 


lemma l4_5 (A B C A' C': Point): 
  Bet A B C → Cong A C A' C' →
  ∃ B', Bet A' B' C' ∧ Cong_3 A B C A' B' C':= sorry


lemma l5_6 ( A B C D A' B' C' D': Point):
 Le A B C D → Cong A B A' B' → Cong C D C' D' → Le A' B' C' D':=sorry


lemma le_reflexivity (A B: Point): Le A B A B :=

begin 
  unfold Le,
  rintros,
  use B,
  cleanup,
end 

lemma lt__le (A B C D: Point): Lt A B C D → Le A B C D :=

begin 
  rintros Hlt,
  cases Hlt,
  tauto!,
end 

lemma le_anti_symmetry (A B C D:Point): Le A B C D → Le C D A B → Cong A B C D :=sorry



lemma sums_sym (A B C D E F: Point): SumS A B C D E F → SumS C D A B E F:=
begin 
  rintros HSumS,
  rcases HSumS with ⟨P, ⟨Q, ⟨R, ⟨HBet, ⟨HCong1 ,⟨HCong2, HCong3⟩⟩⟩⟩⟩⟩,
  use [R, Q, P], cleanup, simp * with geometry_simp,
end 

lemma le_lt12_sums2__lt  (A B C D E F A' B' C' D' E' F': Point):
  Lt A B A' B' → Le C D C' D' → SumS A B C D E F → SumS A' B' C' D' E' F' →
  Lt E F E' F':=sorry

lemma le_lt34_sums2__lt ( A B C D E F A' B' C' D' E' F': Point):
  Le A B A' B' → Lt C D C' D' → SumS A B C D E F → SumS A' B' C' D' E' F' →
  Lt E F E' F':=

begin 
  rintros HLe HLt Hsum HSum',
  apply le_lt12_sums2__lt, repeat {assumption,},
  all_goals {
    apply sums_sym, assumption,
  },
end 

lemma le_cases (A B C D: Point): Le A B C D ∨ Le C D A B:=sorry


lemma or_lt_cong_gt ( A B C D : Point) : Lt A B C D ∨ Gt A B C D ∨ Cong A B C D :=sorry



lemma angledistinct {A B C a b c : Point}:
CongA A B C a b c → A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c := sorry


lemma cong2_lt__lt (A B C D A' B' C' D': Point):
 Lt A B C D → Cong A B A' B' → Cong C D C' D' → Lt A' B' C' D' := 

begin 
  rintros Hlt HCong1 HCong2,
  cases Hlt with Hle HNCong,
  split,
  apply (l5_6 A B C D), repeat {tauto!,},
  intro heq,
  apply HNCong,
  apply (cong_transitivity _ _ A' B'), cleanup,
  apply (cong_transitivity _ _ C' D'), cleanup,
  cleanup,
end 

/-- Section T7 -/


lemma l7_21 ( A B C D P: Point):
  ¬ Col A B C → B≠D →
  Cong A B C D → Cong B C D A →
  Col A P C → Col B P D →
  Midpoint P A C ∧ Midpoint P B D :=sorry 


lemma not_col_exists (A B : Point): A≠B → ∃ C, ¬ Col A B C := sorry



--Out 

lemma l6_4_1 (A B P: Point): Out P A B → Col A P B ∧ ¬ Bet A P B:=sorry



lemma out2__bet (A B C : Point): Out A B C → Out C A B → Bet A B C := 
begin 
  rintros Hout1 Hout2,
  replace Hout2:= l6_4_1 _ _ _ Hout2,
  cases Hout2 with _ Hout2,
  rcases Hout1 with ⟨_,⟨_,⟨ _ ⟩⟩⟩,
  cleanup,
  contradiction,
end 

lemma bet_out (A B C: Point): B ≠ A → Bet A B C → Out A B C:=
begin 
  unfold Out,
  rintros,
  cleanup,
  cases bet.neq _ _ _ ᾰ_1 with _ _,
  tauto!,
end 

/-out reflexivity-/
lemma out_trivial (P A : Point) : (A ≠ P) → Out P A A := 
begin 
  unfold Out,
  cleanup,
end 

lemma out_diff1 (A B C: Point): Out A B C → B ≠ A:=
begin
    rintros H,
    unfold Out at H,
    tauto!,
end

lemma out_diff2 (A B C: Point): Out A B C → C ≠ A:=
begin
    rintros H,
    unfold Out at H,
    tauto!,
end

lemma out_distinct ( A B C: Point): Out A B C → B ≠ A ∧ C ≠ A:=
begin 
  rintros,
  split,
   apply out_diff1, assumption,
  apply out_diff2, assumption,

end 


lemma out_sym (P A B : Point) : Out P A B → Out P B A :=
begin 
  rintros,
  unfold Out at *,
  cc,
end 


lemma out_one_side (A B X Y : Point): (¬Col A B X ∨ ¬ Col A B Y) → Out A X Y → OS A B X Y:=sorry


lemma out_out_one_side (A B X Y Z: Point):
  OS A B X Y →
  Out A Y Z →
  OS A B X Z :=sorry

lemma one_side_transitivity (P Q A B C: Point):
OS P Q A B → OS P Q B C → OS P Q A C:= sorry 


lemma out_col : ∀ (A B C: Point), Out A B C → Col A B C :=
begin
    rintros _ _ _ H,
    rcases H with ⟨H,H1, H2⟩,
        unfold Col,
        cleanup_hyps, cleanup,
    induction H2, repeat {simp*,}, 
end 


mk_simp_attribute out_simp "simplification lemmas for out"

attribute [out_simp] out_trivial out_sym 

lemma l6_16_1 (P Q S X: Point): P≠Q → S≠P → Col S P Q → Col X P Q → Col X P S:=sorry

lemma col_transitivity_1 (P Q A B: Point):
  P≠Q → Col P Q A → Col P Q B → Col P A B :=
begin 
  rintros HPQ HCol1 HCol2,
  by_cases A=P,
    subst_vars,
    unfold Col,
    cleanup,
  have T:= l6_16_1 P Q A B,
  apply col_permutation_1,
  apply T,
  repeat {cleanup,},
end 

lemma col_transitivity_2 (P Q A B: Point):
 P≠Q → Col P Q A → Col P Q B → Col Q A B := 
  begin 
    rintros, 
    apply col_transitivity_1 Q P A B, all_goals {cleanup,},
  end 

lemma not_out_bet ( A B C: Point):
 Col A B C → ¬ Out B A C → Bet A B C :=sorry


lemma or_bet_out (A B C: Point): Bet A B C ∨ Out B A C ∨ ¬Col A B C:=
begin
    rintros,
    by_cases Col A B C, cleanup,
    by_cases (Out B A C), cleanup,
    left, apply not_out_bet, repeat {cleanup,}, 
    -- left; apply not_out_bet; trivial.
end 


lemma not_bet_out ( A B C: Point): Col A B C → ¬Bet A B C → Out B A C :=
begin 
  rintros,
  cases or_bet_out A B C with HBet _,
  contradiction,
  tauto!,
end 



lemma l5_2 ( A B C D: Point):
  A≠B → Bet A B C → Bet A B D → Bet B C D ∨ Bet B D C :=sorry 



lemma l6_2 (A B C P: Point): 
 A≠P → B≠P → C≠P → Bet A P C → (Bet B P C ↔ Out P A B):=sorry


lemma l6_11_existence (A B C R: Point):
R≠A → B≠C → ∃ X, Out A X R ∧ Cong A X B C:=sorry


lemma segment_construction_3 (A B X Y: Point): A ≠ B → X ≠ Y → ∃ C, Out A B C ∧ Cong A C X Y:=sorry


lemma l6_21 : ∀ (A B C D P Q: Point),
  ¬ Col A B C → C≠D → Col A B P → Col A B Q → Col C D P → Col C D Q → P=Q := sorry

/--Section T8-/
lemma l8_12 (A B C D X : Point): Perp_at X A B C D → Perp_at X C D A B :=sorry


lemma l8_18_existence (A B C : Point): ¬ Col A B C → ∃ X, Col A B X ∧ Perp A B C X:=sorry

lemma midpoint_existence (A B : Point): ∃ X, Midpoint X A B := sorry



lemma symmetric_point_construction (A P : Point) :  ∃ P', Midpoint A P P' :=
begin
    unfold Midpoint,
    cases segment_construction P A P A with E H,
    use E,
    cleanup,
end 

lemma midpoint_bet (A B C: Point): Midpoint B A C → Bet A B C :=
begin
    unfold Midpoint,
    rintros H,
    cleanup,
end 

lemma l7_2 ( M A B: Point): Midpoint M A B → Midpoint M B A:=
begin
    unfold Midpoint,
    rintros,
    cleanup,
    exact between_symmetry _ _ _ ᾰ.1,
end 


lemma l7_20 (M A B:Point):
  Col A M B → Cong M A M B → A=B ∨ Midpoint M A B:=sorry 


lemma per_not_col  {A B C : Point}: A ≠ B → B ≠ C → Per A B C → ¬Col A B C:=sorry

lemma per_perp_in  (A B C : Point): A ≠ B → B ≠ C → 
Per A B C → Perp_at B A B B C :=sorry

lemma perp_in_perp_bis (A B C D X: Point):
 Perp_at X A B C D → Perp X B C D ∨ Perp A X C D :=sorry 

lemma perp_distinct (A B C D : Point): Perp A B C D → A ≠ B ∧ C ≠ D:=sorry

lemma perp_left_comm ( A B C D : Point): Perp A B C D → Perp B A C D:=sorry 

lemma perp_right_comm ( A B C D : Point): Perp A B C D → Perp A B D C:=sorry

lemma perp_comm ( A B C D : Point): Perp A B C D → Perp B A D C :=sorry


lemma perp_at1 (X A B C D : Point) :(Perp_at X A B C D) = Perp_at X A B D C := sorry
lemma perp_at2 (X A B C D : Point) : (Perp_at X A B C D) = Perp_at X B A C D := sorry
lemma perp_at3 (X A B C D : Point) : (Perp_at X A B C D) = Perp_at X B A D C := sorry
lemma perp_at4 (X A B C D : Point) : (Perp_at X A B C D) = Perp_at X C D A B := sorry
lemma perp_at5 (X A B C D : Point) : (Perp_at X A B C D) = Perp_at X C D B A := sorry
lemma perp_at6 (X A B C D : Point) : (Perp_at X A B C D) = Perp_at X D C A B := sorry
lemma perp_at7 (X A B C D : Point) : (Perp_at X A B C D) = Perp_at X D C B A := sorry



meta def perp : tactic unit := `[try { simp only [perp_at1, perp_at2, 
perp_at3, perp_at4, perp_at5, perp_at6, perp_at7] at *}; try {simp*}]

/--Per sym-/


lemma l8_9 ( A B C : Point ): Per A B C → Col A B C → A=B ∨ C=B := sorry 


/--Section T9-/


lemma col_two_sides_bet :
 ∀ (A B X Y: Point),
 Col A X Y →
 TS A B X Y →
 Bet X A Y :=sorry

lemma one_side_not_col123 : ∀ (A B X Y : Point), OS A B X Y → ¬ Col A B X := sorry 

lemma one_side_not_col124 ( A B X Y: Point): OS A B X Y → ¬ Col A B Y:=sorry


/--Section T9-/

lemma l9_2  (A B P Q: Point) (H: TS A B P Q ): TS A B Q P:=sorry

lemma l9_5 (P Q A C R B: Point): TS P Q A C → Col R P Q → Out R A B → TS P Q B C :=sorry

lemma invert_two_sides (A B P Q: Point)
( H: TS A B P Q ): TS B A P Q := sorry 

lemma two_sides_not_col (A B X Y: Point): TS A B X Y → ¬ Col A B X :=sorry 

lemma invert_one_side ( A B P Q : Point)
 (H: OS A B P Q ): OS B A P Q:=sorry 


@[simp] lemma one_side_symmetry (P Q A B: Point) (H: OS P Q A B) : OS P Q B A:=sorry 

lemma l9_8_2 (P Q A B C : Point) : TS P Q A C →
 OS P Q A B → TS P Q B C :=sorry


lemma l9_9  (P Q A B: Point) (H: TS P Q A B) :¬ OS P Q A B:= sorry 


lemma l9_9_bis : ∀ (P Q A B: Point), OS P Q A B → ¬ TS P Q A B :=sorry 

lemma l9_19 ( X Y A B P: Point):
 X ≠ Y → Col X Y P → Col A B P → (OS X Y A B ↔ (Out P A B ∧ ¬Col X Y A)):=sorry

mk_simp_attribute side_simp "simplification lemmas for side"

attribute [side_simp] l9_2 invert_two_sides invert_one_side one_side_symmetry
l9_9 l9_9_bis


lemma l12_6 (A B C D: Point): Par_strict A B C D → OS A B C D :=sorry 



lemma col_one_side (A B C P Q: Point):
  Col A B C → A ≠ C → OS A B P Q → OS A C P Q :=sorry

lemma col_one_side_out (A B X Y: Point):
 Col A X Y →
 OS A B X Y →
 Out A X Y:=sorry

lemma conga_dec :
  ∀( A B C D E F: Point),
   CongA A B C D E F ∨ ¬ CongA A B C D E F :=sorry 


lemma cong2_conga_cong : ∀ (A B C A' B' C': Point),
 CongA A B C A' B' C' → Cong A B A' B' → Cong B C B' C' →
 Cong A C A' C':=sorry 


lemma l10_15 (A B C P : Point) : Col A B C → ¬ Col A B P →
 ∃ Q, Perp A B Q C ∧ OS A B P Q := sorry 
-- begin 

lemma angle_construction_1 (A B C A' B' P : Point):
 ¬Col A B C → ¬Col A' B' P →
 ∃ C', CongA A B C A' B' C' ∧ OS A' B' C' P :=sorry 


lemma angle_construction_2 : ∀ (A B C A' B' P: Point),
 A ≠ B → A ≠ C → B ≠ C → A' ≠ B' → ¬Col A' B' P →
 ∃ C', CongA A B C A' B' C' ∧ (OS A' B' C' P ∨ Col A' B' C') :=sorry 

lemma per_per_col : ∀ (A B C X: Point), Per A X C → X ≠ C → Per B X C → Col A B X :=sorry


lemma lea_asym : ∀ (A B C D E F: Point),
 LeA A B C D E F → LeA D E F A B C → CongA A B C D E F :=sorry 

lemma lt_transitivity (A B C D E F:Point): Lt A B C D → 
Lt C D E F → Lt A B E F:=sorry

lemma not_and_lt : ∀ (A B C D: Point), ¬ (Lt A B C D ∧ Lt C D A B) :=sorry

lemma not_and_lta : ∀ (A B C D E F: Point), ¬(LtA A B C D E F ∧ LtA D E F A B C):=sorry 

lemma nlt (A B : Point): ¬ Lt A B A B := sorry 

lemma nlta : ∀ (A B C: Point), ¬ LtA A B C A B C:=
begin
  rintros A B C heq,
  apply (not_and_lta A B C A B C), tauto!,
end 

lemma lea__nlta : ∀ (A B C D E F: Point), LeA A B C D E F → ¬ LtA D E F A B C :=sorry


lemma lta__nlea : ∀ (A B C D E F: Point), LtA A B C D E F → ¬ LeA D E F A B C:=sorry

lemma lea123456_lta__lta (A B C D E F G H I: Point ): LeA A B C D E F → LtA D E F G H I →
   LtA A B C G H I:=sorry

lemma nlta__lea : ∀ (A B C D E F: Point), ¬ LtA A B C D E F → A ≠ B → B ≠ C → D ≠ E → E ≠ F →
   LeA D E F A B C:=sorry


lemma nlea__lta : ∀ (A B C D E F: Point), ¬ LeA A B C D E F → A ≠ B → B ≠ C → D ≠ E → E ≠ F →
   LtA D E F A B C:=sorry 


lemma triangle_strict_inequality : ∀ (A B C D: Point), Bet A B D → Cong B C B D → ¬ Bet A B C →
   Lt A C A D :=sorry 


lemma in_angle_line {A B C P: Point}: P ≠ B → A ≠ B → C ≠ B → Bet A B C → InAngle P A B C := sorry



lemma ex_per_cong : ∀ (A B C D X Y : Point),
 A ≠ B → X ≠ Y → Col A B C → ¬Col A B D →
 ∃ P, Per P C A ∧ Cong P C X Y ∧ OS A B P D :=sorry 

lemma exists_cong_per (A B X Y : Point): ∃ C, Per A B C ∧ Cong B C X Y :=sorry

lemma l11_4_1 {A B C D E F : Point}:
  CongA A B C D E F → A≠B ∧ C≠B ∧ D≠E ∧ F≠E ∧
  (∀ A' C' D' F', Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧
  Cong B A' E D' ∧ Cong B C' E F' → Cong A' C' D' F') :=sorry 


lemma l11_4_2  {A B C D E F : Point}: 
  (A≠B ∧ C≠B ∧ D≠E ∧ F≠E ∧
  (∀ A' C' D' F', Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧
  Cong B A' E D' ∧ Cong B C' E F' → Cong A' C' D' F')) → CongA A B C D E F:=sorry 




lemma out_conga (A B C A' B' C' A0 C0 A1 C1: Point): 
 CongA A B C A' B' C' → Out B A A0 →
 Out B C C0 →Out B' A' A1 →Out B' C' C1 →
 CongA A0 B C0 A1 B' C1 :=sorry 

lemma l11_10 (A B C D E F A' C' D' F' : Point):
  CongA A B C D E F → Out B A' A → Out B C' C → Out E D' D → Out E F' F →
  CongA A' B C' D' E F' :=sorry 


lemma l11_17 : ∀ (A B C A' B' C' : Point),
  Per A B C → CongA A B C A' B' C' → Per A' B' C' := sorry

lemma l11_18_1  (A B C D: Point): 
  Bet C B D → B ≠ C → B ≠ D → A ≠ B → Per A B C → CongA A B C A B D :=sorry 

lemma l11_13 (A B C D E F A' D': Point):
 CongA A B C D E F → Bet A B A' → A'≠ B → Bet D E D' → 
 D'≠ E → CongA A' B C D' E F := sorry 


lemma l11_14 (A B C A' C': Point): Bet A B A' → A ≠ B → A' ≠ B → Bet C B C' → B ≠ C → B ≠ C' →
 CongA A B C A' B C':=sorry

lemma l11_30  (A B C D E F A' B' C' D' E' F': Point):
 LeA A B C D E F →
 CongA A B C A' B' C' →
 CongA D E F D' E' F' →
 LeA A' B' C' D' E' F' := sorry 

lemma in_angle_trivial_1 (A B C: Point): A ≠ B → C ≠ B → InAngle A A B C:=
begin
  rintros,
  constructor,
    tauto!,
  refine ⟨by assumption, by assumption, _⟩,
  use A,
  split,
    cleanup,
  right,
  apply out_trivial,
  assumption,
end 


lemma l11_21_b (A B C A' B' C': Point):
 Out B A C → Out B' A' C' → CongA A B C A' B' C' :=sorry
 
lemma l11_31_1 (A B C D E F : Point): Out B A C → D ≠ E → F ≠ E → Bet D E F → LeA A B C D E F:=
begin
  rintros,
  unfold LeA,
  use D,
  split,
    apply in_angle_trivial_1, tauto!, tauto!,
  apply l11_21_b,
    assumption,
  apply out_trivial,
  assumption,
end 


lemma l11_41_aux : ∀( A B C D: Point),
 ¬ Col A B C → Bet B A D → A ≠ D → LtA A C B C A D :=sorry 


lemma l11_41  (A B C D: Point):
 ¬ Col A B C → Bet B A D → A ≠ D → LtA A C B C A D ∧ LtA A B C C A D := sorry

lemma l11_29_a  {A B C D E F:Point}: LeA A B C D E F → ∃ Q, InAngle C A B Q ∧ CongA A B Q D E F:=sorry


lemma l11_29_b (A B C D E F:Point): (∃ Q, InAngle C A B Q ∧ CongA A B Q D E F) → LeA A B C D E F:=sorry

 
lemma lea_left_comm (A B C D E F: Point): LeA A B C D E F → LeA C B A D E F := 
begin
  rintros HLeA,
  unfold LeA at HLeA,
  cases HLeA with P H,
  use P,
  constructor,
    tauto!,
  exact conga_left_comm _ _ _ _ _ _ H.2,
end 

lemma lea_right_comm (A B C D E F: Point): LeA A B C D E F → LeA A B C F E D := 
begin
  rintros H,
  apply l11_29_b,
  replace H:= l11_29_a H,
  cases H with P H,
  use P,
  cleanup,
  apply conga_right_comm,
  cleanup,
end 

lemma lea_comm (A B C D E F: Point): LeA A B C D E F → LeA C B A F E D :=
begin
  rintros, 
  apply lea_left_comm,
  apply lea_right_comm,
  cleanup,
end 

lemma lta_left_comm (A B C D E F: Point): LtA A B C D E F → LtA C B A D E F :=
begin
  unfold LtA,
  rintros H0,
  constructor,
  apply lea_left_comm, cleanup,
  intro heq,
  apply H0.2, apply conga_left_comm,
  assumption,
end

lemma lta_right_comm (A B C D E F: Point): LtA A B C D E F → LtA A B C F E D :=
begin
  unfold LtA,
  rintros H0,
  constructor,
  apply lea_right_comm, cleanup,
  intro heq,
  apply H0.2, apply conga_right_comm,
  assumption,
end


lemma lta_comm (A B C D E F : Point): LtA A B C D E F → LtA C B A F E D :=
begin
    rintros HLtA,
    apply lta_left_comm,
    apply lta_right_comm,
    assumption,
end 


lemma lta_diff (A B C D E F: Point): LtA A B C D E F → LtA A B C D E F ∧ A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E := sorry 


lemma lta_not_conga : ∀ (A B C D E F : Point), A ≠ B → C ≠ B → D ≠ E → F ≠ E → 
LtA A B C D E F → ¬ CongA A B C D E F :=
begin
    rintros _ _ _ _ _ _ nEq1 nEq2 nEq3 nEq4 ⟨_,NCongA1⟩, tauto,
end



lemma l11_44_1(A B C: Point):  ¬Col A B C → (CongA B A C B C A ↔ Cong B A B C):=sorry

/--In an isosceles triangle the two base angle are equal-/

lemma l11_44_1_a (A B C: Point): ¬Col A B C → Cong B A B C → CongA B A C B C A := 
begin
  rintros HCol HCong,
  cases midpoint_existence A C with P HP,
  rw Midpoint at HP,
  have HCong3: Cong_3 B C P B A P, rw Cong_3, 
  cleanup,
  have HConga: CongA B C P B A P, 
  apply cong3_conga, exact (NCdistinct HCol).2.1,
  simp [bet_neqR _ _ _ HP.1], assumption,
  apply conga_sym,
  replace HCol:= NCdistinct HCol,
  apply l11_10 _ _ _ _ _ _ _ _ _ _ HConga (bet_out _ _ _ (HCol.2.1) (between_trivial C B)),
  apply out_sym, 
  use (bet_out _ _ _ ((bet_neqR _ _ _ HP.1)) (between_symmetry _ _ _( HP.1))),
  simp * with out_simp, 
  apply out_sym,
  use bet_out _ _ _ (ne.symm (bet_neqL (HP.1))) HP.1,
end 

lemma col_conga_col (A B C D E F: Point): Col A B C → CongA A B C D E F → Col D E F:=sorry 


lemma ncol_conga_ncol (A B C D E F: Point): ¬Col A B C → CongA A B C D E F → ¬Col D E F :=
begin
  rintros H H1 heq, 
  apply H,
  apply col_conga_col,
  exact heq,
  exact conga_sym H1,
end 


lemma l11_44_2_a : ∀ (A B C: Point), ¬Col A B C → Lt B A B C → LtA B C A B A C:= sorry
    

lemma l11_44_2_b : ∀ (A B C: Point), ¬Col A B C → LtA B A C B C A → Lt B C B A := sorry 


/--If the base angles are equal the triangle is isosceles.-/
lemma l11_44_1_b ( A B C : Point): ¬Col A B C → CongA B A C B C A → Cong B A B C :=

begin
  rintros H H1,
    replace H:= not_col_distincts H,
    rcases H with ⟨H , H2, H3, H4⟩,
    have HH:= or_lt_cong_gt B A B C,
    induction HH,
      have HH2:= l11_44_2_a _ _ _ H HH,
        have HH4:= lta_not_conga _ _ _ _ _ _ H3 H4 H2.symm H4.symm HH2,
          have H2:= conga_sym H1,
          contradiction,
    induction HH,
      unfold Gt at HH,
      replace H:= NCol_perm _ _ _ H, 
      have HH2:= l11_44_2_a _ _ _ H.2.2.2.2.2 HH,
       have HH4:= lta_not_conga _ _ _ _ _ _ H2.symm H4.symm H3 H4 HH2,
       have H2:= conga_sym H1,
          contradiction,
          assumption,
end 

lemma all_coplanar_implies_upper_dim : all_coplanar_axiom Point → upper_dim_axiom Point:=sorry

lemma upper_dim_implies_not_one_side_two_sides :
  upper_dim_axiom Point→
  (∀ (A B X Y: Point),
   A ≠ B →
   ¬ Col X A B →
   ¬ Col Y A B →
   ¬ OS A B X Y →
   TS A B X Y):=sorry



lemma not_one_side_two_sides {A B X Y: Point}:
  A ≠ B →
  ¬ Col X A B →
  ¬ Col Y A B →
  ¬ OS A B X Y →
  TS A B X Y :=
  begin
    apply upper_dim_implies_not_one_side_two_sides,
    apply all_coplanar_implies_upper_dim,
    unfold all_coplanar_axiom, apply all_coplanar,
  end 


-- /--Tarski's version of parallel postulate -/
-- def parallel_postulate  (Point : Type) [tarski_preneutral Point] := ∀( A B C D T : Point),
--   Bet A D T → Bet B D C → A ≠ D →
--   ∃ X Y, Bet A B X ∧ Bet A C Y ∧ Bet X T Y


-- /--Alternate interior angles between two parallel lines are congruent -/

def alternate_interior_angles_postulate (Point : Type) [tarski_preneutral Point] 
:= ∀ (A B C D : Point), TS A C B D → Par A B C D → CongA B A C D C A

def triangle_postulate (Point : Type) [tarski_preneutral Point]:= ∀(A B C D E F: Point),
TriSumA A B C D E F → Bet D E F

lemma alternate_interior__triangle :
  alternate_interior_angles_postulate Point → triangle_postulate Point := sorry 


lemma bet__le2313 (A B C : Point): Bet A B C → Le B C A C :=
begin
  rintros HBet,
  cases l5_12_a A B C HBet,
  assumption,
end



lemma l11_47( A B C H: Point): Per A C B → Perp_at H C H A B →
 Bet A H B ∧ A ≠ H ∧ B ≠ H :=sorry 


-- /-- This is SAS congruence. -/ 

lemma l11_49 : ∀ (A B C A' B' C' : Point),
 CongA A B C A' B' C' → Cong B A B' A' → Cong B C B' C' →
 Cong A C A' C' ∧ (A ≠ C → CongA B A C B' A' C' ∧ CongA B C A B' C' A') := 

 begin
   rintros _ _ _ _ _ _ H H1 H2,
    have H4: (Cong A C A' C'),
      apply cong2_conga_cong,
        apply H, cleanup, cleanup,
    split,
      assumption,
    intros H3,
    have: (A ≠ B ∧ C ≠ B ∧ A' ≠ B' ∧ C' ≠ B'),
      unfold CongA at H, 
      tauto!,
      cases_type* and,
    split,
      apply l11_3_bis, 
      use [B, C, B' , C'],
      refine⟨_,_,_,_,_⟩,
      repeat {apply out_trivial, tauto!,},
      apply out_trivial,
      intro heq,
        subst_vars,
        suffices : A = C,
        subst_vars,
        contradiction,
        apply cong_identity _ _ _ H4,
        refine ⟨by tauto!, by tauto! , by tauto!⟩ ,
        unfold CongA,
      apply l11_3_bis, 
      use [B, A, B' , A'],
      refine⟨_,_,_,_,_⟩,
      repeat {apply out_trivial, tauto!,},
      apply out_trivial,
      intro heq,
      subst_vars,
       suffices : A = C,
        subst_vars,
        repeat {contradiction,}, 
        apply cong_identity _ _ _ H4,
        unfold Cong_3,
      refine ⟨by assumption, by assumption,by cleanup⟩,
 end 


lemma l11_50_2 ( A B C A' B' C': Point):
  ¬Col A B C → CongA B C A B' C' A' → CongA A B C A' B' C' → Cong A B A' B' →
  Cong A C A' C' ∧ Cong B C B' C' ∧ CongA C A B C' A' B' :=sorry


lemma lta_trans  (A B C A1 B1 C1 A2 B2 C2: Point):
 LtA A B C A1 B1 C1 →
 LtA A1 B1 C1 A2 B2 C2 →
 LtA A B C A2 B2 C2 :=sorry

lemma l9_31 (A X Y Z:Point):
  OS A X Y Z →
  OS A Z Y X →
  TS A Y X Z:=sorry

lemma os_ts__inangle (A B C P:Point): TS B P A C → OS B A C P → InAngle P A B C:=sorry

lemma os2__inangle (A B C P: Point): 
OS B A C P → OS B C A P → InAngle P A B C :=
begin
  rintros Hos1 Hos2,
  apply os_ts__inangle,
  apply l9_31,
  any_goals{ simp*,},
end 
/--This is half of Euclid Book I,
Proposition 21: if D is inside the triangle ABC then BAC < BDC.-/

lemma os3__lta (A B C D: Point): OS A B C D → OS B C A D → OS A C B D →
   LtA B A C B D C:= sorry

lemma ts_distincts {A B P Q: Point}: TS A B P Q →
  A ≠ B ∧ A ≠ P ∧ A ≠ Q ∧ B ≠ P ∧ B ≠ Q ∧ P ≠ Q:=
begin
  rintros HTS,
  rcases HTS with ⟨HNCol1, ⟨HNCol2, ⟨T ,⟨HCol, HBet⟩⟩⟩⟩,
  rcases ⟨bet.neq _ _ _ HBet, NCdistinct HNCol1, NCdistinct HNCol2⟩ with ⟨HNE1, HNE2, HNE3⟩,
  refine ⟨ _,_,_,_,_,_⟩,
  all_goals{
    tauto!,
  },
end
lemma os_distincts (A B X Y: Point): OS A B X Y →
  A ≠ B ∧ A ≠ X ∧ A ≠ Y ∧ B ≠ X ∧ B ≠ Y :=
  begin
    rintros ⟨Z,⟨HTS1,HTS2⟩⟩,
    rcases ⟨ts_distincts HTS1, ts_distincts HTS2⟩ with ⟨_,_⟩,
    tauto!,
  end

lemma conga__or_out_ts : ∀ (A B C C': Point),
 CongA A B C A B C' → Out B C C' ∨ TS A B C C' :=sorry 


lemma perp_sym (A B C D: Point): Perp A B C D → Perp C D A B :=
begin
  unfold Perp,
  rintros H,
  cases H with X H,
  use X,
  apply l8_12, tauto!,
end 

lemma l7_3_2 : ∀ (A : Point), Midpoint A A A := 
begin 
  unfold Midpoint,
  cleanup,
end 


lemma l7_13 (A P Q P' Q':Point): Midpoint A P' P → Midpoint A Q' Q → Cong P Q P' Q':=sorry

lemma l8_2 (A B C : Point): Per A B C → Per C B A :=
begin 
  unfold Per,
  rintros ⟨C', H⟩,
  have: ∃ A', Midpoint B A A',
    apply symmetric_point_construction,
  cases this with A' H1,
  use A',
  split,
    assumption,
  apply cong_transitivity _ _ _ _ _ _,
  apply cong_commutativity,
  apply H.2,
  apply l7_13,
  apply H.1,
  apply l7_2,
  apply H1,
end 



lemma l8_5 (A B:Point) : Per A B B:=
begin
    unfold Per,
    intros,
    use B,
    split,
      apply l7_3_2,
    cleanup,
end 

lemma l8_7 {A B C : Point}: Per A B C → Per A C B → B=C := sorry 

lemma l8_8 (A B:Point): Per A B A → A=B:=
begin
    rintros,
    apply l8_7,
      apply l8_2,
      apply l8_5,
    assumption,
end 

lemma l8_14_2_1b (X A B C D Y: Point): Perp_at X A B C D → Col Y A B → Col Y C D → X=Y:=
begin
    rintros H0 H1 H2,
    unfold Perp_at at H0,
    rcases H0 with ⟨HAB, HCD,_,_,H4⟩ ,
    replace H4:= H4 Y Y,
      apply symm,
    apply l8_8,
    cleanup,
end 

lemma l8_14_2_1b_bis (A B C D X: Point):  Perp A B C D → Col X A B → Col X C D → Perp_at X A B C D:=
begin
    rintros ⟨Y, H0⟩ H1 H2,
    unfold Perp_at at *,
    have HYX:(Y = X),
     apply l8_14_2_1b Y _ _ _ _ ,
     apply H0,
     any_goals {cleanup,},
     subst Y,
     tauto!,
end 

lemma l8_15_1 (A B C X: Point): A≠B → Col A B X → Perp A B C X → Perp_at X A B C X:=
begin
    rintros,
    apply l8_14_2_1b_bis,
    all_goals {cleanup,},
end 
lemma perp_perp_in {A B C: Point}: Perp A B C A → Perp_at A A B C A:=
begin
    rintros H,
    apply l8_15_1,
      unfold Perp at H,
      cases H with X H0,
      unfold Perp_at at H0,
      tauto!,
    all_goals {cleanup,},
end

lemma perp_per_1 {A B C : Point}: Perp A B C A → Per B A C:=
begin
  rintros H,
  have HPerp: Perp_at A A B C A,
    apply perp_perp_in,
    assumption,
  rcases HPerp with ⟨_,_,HCol1,HCol2,HH⟩,
  apply HH,
  all_goals {cleanup,},
end 

lemma perp_per_2 (A B C: Point): Perp A B A C → Per B A C :=
begin
  rintros H,
  replace H:= perp_right_comm _ _ _ _ H,
  apply perp_per_1 H,
end 


lemma l6_4_2 (A B P: Point): Col A P B ∧ ¬ Bet A P B → Out P A B :=sorry 
/--This is SSS congruence.-/

lemma l11_51 : ∀(A B C A' B' C': Point),
  A ≠ B → A ≠ C → B ≠ C → Cong A B A' B' → Cong A C A' C' → Cong B C B' C' →
  CongA B A C B' A' C' ∧ CongA A B C A' B' C' ∧ CongA B C A B' C' A' :=sorry 




lemma conga_distinct (A B C D E F: Point):
 CongA A B C D E F → CongA A B C D E F ∧ A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E := sorry

lemma angle_bisector (A B C : Point): A ≠ B → C ≠ B → ∃ P, 
InAngle P A B C ∧ CongA P B A P B C:= sorry


lemma segment_construction_0  (A B A': Point): ∃ B', Cong A' B' A B:=sorry 



@[simp] lemma par_reflexivity : ∀ (A B: Point), A≠B → Par A B A B :=
  begin
    rintros,
    unfold Par,
    unfold Par_strict,
    simp [Col], cleanup,
  end 

lemma par_symmetry ( A B C D : Point): Par A B C D 
→ Par C D A B:=sorry

lemma l12_9 (A1 A2 B1 B2 C1 C2: Point):
 Perp A1 A2 C1 C2 → Perp B1 B2 C1 C2 →
 Par A1 A2 B1 B2 :=sorry 

lemma par_left_comm ( A B C D: Point):
 Par A B C D → Par B A C D := sorry


lemma par_right_comm (A B C D : Point):
Par A B C D → Par A B D C :=
begin
  rintros HPar,
  apply par_symmetry,
  apply par_left_comm _ _ _ _ (par_symmetry _ _ _ _ HPar),
end 

lemma par_comm (A B C D : Point):
 Par A B C D → Par B A D C :=
begin
    rintros HPar,
    apply par_left_comm,
    apply par_right_comm _ _ _ _ HPar,

end 

lemma parallel_existence : ∀ (A B P: Point), A ≠ B → 
∃ C, ∃ D, C≠D ∧ Par A B C D ∧ Col P C D :=
begin
  rintros, 
  by_cases HCol: (Col A B P),
  {use [A, B], cleanup,},
  have: ∃ P' , Col A B P' ∧ Perp A B P P',
  apply l8_18_existence, assumption,
  cases this with P' H1,
  have : P ≠ P',
    intro heq,
    subst P',
    tauto!,
  by_cases P' = A,
    subst P',
    have: ∃ Q, Per Q P A ∧ Cong Q P A B ∧ OS A P Q B,
    apply ex_per_cong,
    any_goals{tauto!,}, 
    simp [Col], 
    cleanup,
    cases this with Q H3,
    use [P, Q],
    simp [Col],
    have H4: P ≠ Q,
      intro heq,
      subst heq,
      cleanup, 
      suffices: A = B ,
      contradiction, 
      apply cong_identity _ _ _ H3.2.1, simp*,
      apply l12_9, apply H1.2,
      replace H4:= per_perp_in _ _ _ H4.symm this H3.1,
      replace H4:= perp_in_perp_bis _ _ _ _ _ H4,
      induction H4,
      replace H4:= perp_distinct _ _ _ _ H4,
      tauto!,
      apply perp_left_comm, 
      assumption,
      have H5: ∃ Q, Per Q P P' ∧ Cong Q P A B ∧ OS P' P Q A,
      apply ex_per_cong, tauto!, tauto!,
      simp [Col], 
      intro,
      apply HCol,
      apply col_transitivity_1 _ _ _ _ (ne.symm h), 
      any_goals {cleanup,},
      cases H5 with Q H5,
      use [P, Q],
        have HPQ: P ≠ Q, 
        intro heq,
        subst heq,
        replace H5:= cong_identity _ _ _ H5.2.1,
        contradiction,
        simp*,
         apply l12_9 _ _ _ _ _ _ H1.2,
         replace H5:= per_perp_in _ _ _ (ne.symm HPQ) ( this) H5.1,
         replace H5:= perp_in_perp_bis _ _ _ _ _ H5,
         induction H5,
         replace H5:=perp_distinct _ _ _ _ H5,
         tauto!,
        apply perp_left_comm, 
        assumption,
end 

lemma par_col_par : ∀( A B C D D': Point),
 C ≠ D' → Par A B C D → Col C D D' → Par A B C D' := sorry 

lemma parallel_existence1 (A B P : Point): A ≠ B → ∃ Q, Par A B P Q:=
begin
  rintros,
  have T:= parallel_existence A B P ᾰ,
  rcases T with ⟨H, x, T⟩,
  by_cases x = P,
    subst x,
      use H, 
      apply par_right_comm,
    tauto!,
  use x,
  apply par_right_comm,
  apply par_col_par _ _ _ _ _ h (par_right_comm _ _ _ _ T.2.1),
    cleanup,
end 

lemma par_strict_left_comm {A B C D: Point}:
 Par_strict A B C D → Par_strict B A C D:=sorry


lemma par_strict_right_comm {A B C D: Point}:
 Par_strict A B C D → Par_strict A B D C :=sorry

lemma par_strict_comm (A B C D: Point):
 Par_strict A B C D → Par_strict B A D C :=
 begin
  rintros H,
  replace H:= par_strict_left_comm H,
  apply par_strict_right_comm,
  tauto!,
 end 

lemma par_not_col_strict (A B C D P: Point):
 Par A B C D → Col C D P → ¬Col A B P → Par_strict A B C D :=sorry 

lemma par_strict_not_col_1 (A B C D: Point):
Par_strict A B C D → ¬ Col A B C :=
begin
  rintros HPar, 
  unfold Par_strict at HPar,
  intro HCol,
  apply HPar.2.2.2,
  use C,
  cleanup,
end 

lemma par_strict_not_col_2 (A B C D: Point):
 Par_strict A B C D → ¬ Col B C D :=
 begin
  rintros HPar, 
  unfold Par_strict at HPar,
  intro HCol,
  apply HPar.2.2.2,
  use B,
  cleanup,
end 


lemma par_strict_not_col_3 (A B C D: Point):
 Par_strict A B C D → ¬ Col C D A :=
 begin
  rintros HPar, 
  unfold Par_strict at HPar,
  intro HCol,
  apply HPar.2.2.2,
  use A,
  cleanup,
end 


lemma par_strict_not_col_4 (A B C D: Point):
 Par_strict A B C D → ¬ Col A B D:=
 begin
  rintros HPar, 
  unfold Par_strict at HPar,
  intro HCol,
  apply HPar.2.2.2,
  use D,
  cleanup,
end 
 

lemma par_id_1 (A B C : Point): Par A B A C → Col B A C :=
begin
    rintros HPar,
    unfold Par at HPar,
    induction HPar,
      unfold Par_strict at HPar,
      exfalso,
      apply HPar.2.2.2,
      use A,
      cleanup, cleanup,

end 

lemma par_id_2 (A B C: Point): Par A B A C → Col B C A :=
begin
    rintros HPar,
    unfold Par at HPar,
    induction HPar,
      unfold Par_strict at HPar,
      exfalso,
      apply HPar.2.2.2,
      use A,
      cleanup, cleanup,

end 

lemma par_id_3 (A B C: Point): Par A B A C → Col A C B:=
begin
    rintros HPar,
    unfold Par at HPar,
    induction HPar,
      unfold Par_strict at HPar,
      exfalso,
      apply HPar.2.2.2,
      use A,
      cleanup, cleanup,
end 

lemma par_id_4 (A B C: Point): Par A B A C → Col C B A:= 
begin
    rintros HPar,
    unfold Par at HPar,
    induction HPar,
      unfold Par_strict at HPar,
      exfalso,
      apply HPar.2.2.2,
      use A,
      cleanup, cleanup,
end 

lemma par_id_5 (A B C: Point): Par A B A C → Col C A B:=
begin
    rintros HPar,
    unfold Par at HPar,
    induction HPar,
      unfold Par_strict at HPar,
      exfalso,
      apply HPar.2.2.2,
      use A,
      cleanup, cleanup,
end 

lemma par_strict_symmetry (A B C D :Point) : Par_strict A B C D → Par_strict C D A B :=sorry


lemma par_strict_col_par_strict ( A B C D E : Point) :
 C ≠ E → Par_strict A B C D → Col C D E →
 Par_strict A B C E:=sorry

lemma par_strict_col2_par_strict ( A B C D E F: Point) :
 E ≠ F → Par_strict A B C D → Col C D E → Col C D F →
 Par_strict A B E F :=sorry

lemma par_distincts (A B C D: Point): 
 Par A B C D → (Par A B C D ∧ A ≠ B ∧ C ≠ D) :=
begin
    rintros H,
    split,
    assumption,
    unfold Par at H,
    induction H,
      unfold Par_strict at H,
      all_goals {tauto!,},
end 


meta def par : tactic unit := `[ try 
{ simp only [par_id_1, par_id_2, par_id_3, par_id_4, par_id_5] at *}; 
try {simp*}]


lemma l12_17 (A B C D P : Point): A ≠ B → 
Midpoint P A C → Midpoint P B D → Par A B C D :=sorry

 lemma l12_21 : ∀( A B C D: Point),
 TS A C B D →
 (CongA B A C D C A ↔ Par A B C D) :=sorry 

lemma l12_22_a (A B C D P: Point):
 Out P A C → OS P A B D → Par A B C D →
 CongA B A P D C P := sorry
 


 lemma l12_22_aux :
 ∀ (A B C D P: Point),
  P ≠ A → A ≠ C → Bet P A C → OS P A B D →
  CongA B A P D C P →
  Par A B C D :=sorry

lemma l12_22_b (A B C D P: Point):
  Out P A C → OS P A B D → CongA B A P D C P →
  Par A B C D :=
begin
  rintros HOut HOS Hconga, 
      by_cases A=C,
        subst C,
        unfold Par,
        right,
        unfold CongA at Hconga,
        refine ⟨ by tauto!,by tauto!,by cleanup,_⟩ ,
        replace Hconga:= conga_comm _ _ _ _ _ _ Hconga,
        replace Hconga:= conga__or_out_ts _ _ _ _ Hconga,
        induction Hconga,
          replace Hconga:= out_col _ _ _ Hconga,
          cleanup,
       replace Hconga:= l9_9 _ _ _ _ Hconga,
       unfold Out at HOut,
        contradiction,
      unfold Out at HOut,
      rcases HOut with ⟨HAB, HPC, HBet⟩,
      induction HBet,
        apply l12_22_aux,
          apply bet_neqL HBet,
          repeat {tauto!,},
      apply par_symmetry,
      apply l12_22_aux,
      apply bet_neqL HBet,
        tauto!,
        tauto,
        apply (col_one_side _ A),
          replace HBet:= bet_col _ _ _ HBet,
          cleanup,
          tauto!,
        apply one_side_symmetry,
        assumption,
      apply conga_sym,
      assumption,
end 
/-- Section T14-/

lemma project_uniqueness (P P' Q' A B X Y: Point):
Proj P P' A B X Y → Proj P Q' A B X Y → P' = Q' :=sorry 


lemma sum_A_O (A: Point) {O E E' : Point} : Col O E A → Sum O E E' A O A :=sorry 

lemma sum_O_B (B: Point) {O E E': Point}: Col O E B → Sum O E E' O B B:=sorry


lemma prod_to_prodp : ∀ (O E E' A B C: Point), Prod O E E' A B C → Prodp O E E' A B C:=sorry


lemma prod_0_l {O E E' A : Point}:
  ¬ Col O E E' → Col O E A → Prod O E E' O A O :=sorry

lemma prod_uniqueness (O E E' A B C D: Point): 
Prod O E E' A B C → Prod O E E' A B D → C = D := 
begin
    rintros HProd1 HProd2,
    replace H1:= prod_to_prodp _ _ _ _ _ _ HProd1,
    replace H2:= prod_to_prodp _ _ _ _ _ _ HProd2,
    unfold Prodp at *,
    cases H1.2.2 with B' H3,
    cases H2.2.2 with B'' H4,
    have HBB: B'=B'',
      apply (project_uniqueness B B' B'' O E' E E') H3.1 H4.1,
    subst B'',
    apply (project_uniqueness B' _ _ O E A E') H3.2 H4.2,
end 

/--Left distributivity of product over sum.-/
lemma distr_l ( O E E' A B C D AB AC AD: Point):
 Sum O E E' B C D → Prod O E E' A B AB → Prod O E E' A C AC →
 (Prod O E E' A D AD → Sum O E E' AB AC AD):=sorry

lemma length_id_1 ( O E E' A B: Point):
  Length O E E' A B O → A=B := 
begin
  rintros H,
  unfold Length at H,
  apply cong_reverse_identity H.2.2.2,
end 


lemma length_id_2 (O E E' A: Point):
  O≠E → Length O E E' A A O :=
  begin
  rintros H,
  unfold Length,
  refine ⟨by assumption, by cleanup, _, _⟩ ,
  unfold LeP,
  tauto!, apply cong_trivial_identity,
end 



lemma length_id (O E E' A B : Point):
 Length O E E' A B O ↔ (A=B ∧ O≠E) :=
begin
  rintros,
  constructor,
    rintros H,
    split,
    apply length_id_1,assumption,
    unfold Length at *, 
    tauto!,
    rintros H,
    cases H with H H1,
    subst_vars,
    apply length_id_2,
    assumption,
end 

-- -- /-- Section T 15-/

lemma length_uniqueness(O E E' A B AB AB': Point):
  Length O E E' A B AB → Length O E E' A B AB' → AB = AB':= sorry

lemma triangular_equality_bis (O E E' A B C AB BC AC: Point):
  A ≠ B ∨ A ≠ C ∨ B ≠ C → O≠E → Bet A B C →
  Length O E E' A B AB → Length O E E' B C BC → Length O E E' A C AC →
  Sum O E E' AB BC AC :=sorry

lemma length_existence (O E E' A B: Point):
  ¬ Col O E E' → ∃ AB, Length O E E' A B AB :=sorry 

lemma l15_7_1 (O E E' A B C H AB AC AH AC2 : Point):
  O≠E → Per A C B → Perp_at H C H A B →
  Length O E E' A B AB → Length O E E' A C AC → Length O E E' A H AH →
  Prod O E E' AC AC AC2 →
  Prod O E E' AB AH AC2 :=sorry 

lemma length_sym {O E E' A B AB : Point }:
  Length O E E' A B AB → Length O E E' B A AB :=
  begin
  rintros H, 
  unfold Length at *, 
  refine ⟨by simp*,by simp*, by simp*, by cleanup⟩ , 
  end 

lemma pythagoras (O E E' A B C AC BC AB AC2 BC2 AB2 : Point):
  O≠E → Per A C B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' B C BC →
  Prod O E E' AC AC AC2 → Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 →
  Sum O E E' AC2 BC2 AB2 := 

begin
  rintros HOE HPer HL HL2 HL3 H4 H5 H6,
  have HCol: ¬ Col O E E' ∧  Col O E AB2 ∧ Col O E AC2 ∧ Col O E BC,
    unfold Prod at *,
    unfold Ar2 at H4 H5 H6,
    tauto!,
    by_cases Col A C B,
      have HH:= l8_9 A C B HPer h,
      induction HH,
      subst C,
      have: AB = BC,
      apply length_uniqueness O E E' A B _ _ HL,
      apply length_sym HL3,
      subst BC,
      have: AB2 = BC2,
      apply prod_uniqueness O E E' AB AB _ _ H6 H5,
      subst BC2,
      have : AC = O,
      apply length_uniqueness O E E' A A _ _ HL2,
      apply length_id_2 _ _ _ _ HOE,
      subst AC,
      have: AC2=O,
      apply prod_uniqueness O E E' O O _ _ H4,
      apply prod_0_l HCol.1, simp with col_simp,
      subst AC2,
      apply sum_O_B _ , cleanup, subst C,
      have: AB=AC,
      apply length_uniqueness O E E' A B _ _ HL HL2,
      subst AC,
      have: AB2=AC2,
      apply prod_uniqueness O E E' AB AB _ _ H6 H4,
      subst AC2,
      have: BC=O,
      apply length_uniqueness O E E' B B _ _ HL3,
      apply length_id_2 _ _ _ _ HOE,
      subst BC,
      have: BC2=O,
      apply prod_uniqueness O E E' O O _ _ H5,
      apply prod_0_l HCol.1, simp with col_simp,
      subst BC2,
      apply sum_A_O _ HCol.2.1,
      have H: ∃ X : Point, Col A B X ∧ Perp A B C X,
        apply l8_18_existence A B C, cleanup,
        cases H with P H12,
        have HPerp: Perp_at P A B C P,
        apply l8_14_2_1b_bis A B C P P H12.2, simp * with col_simp,
        simp with col_simp,
      have: Bet A P B ∧ A ≠ P ∧ B ≠ P, apply l11_47 A B C P HPer,
      apply l8_12 _ _ _ _ _ HPerp,
      have HL1:= length_existence O E E' A P HCol.1,
      have HL2:= length_existence O E E' B P HCol.1,
      rcases HL1 with ⟨AP, HL1⟩,
      rcases HL2 with ⟨BP, HL2⟩,
      have HSum: Sum O E E' AP BP AB,
      apply triangular_equality_bis O E E' A P B AP BP AB, any_goals {tauto!,},
      exact length_sym HL2,
      have HProd1: Prod O E E' AB AP AC2,
        apply l15_7_1 O E E' A B C P AB AC AP AC2, any_goals {tauto!,}, perp,
      have HProd2: Prod O E E' AB BP BC2,
        apply l15_7_1 O E E' B A C P AB BC, {any_goals {tauto!,},}, 
        use l8_2 _ _ _ HPer, 
        perp,
        apply length_sym, tauto!,
        any_goals {tauto!,},
      exact distr_l O E E' AB AP BP AB AC2 BC2 AB2 HSum HProd1 HProd2 H6,
end 


lemma exists_grid : ∃ (O E E' S U1 U2: Point), ¬ Col O E E' ∧ Cs O E S U1 U2 :=sorry


lemma lea121345 (A B C D E F: Point): A≠B → C≠D → D≠E → LeA A B A C D E:=sorry 

lemma exists_grid_spec : ∃ (S U1 U2 : Point), Cs PA PB S U1 U2 := sorry 


lemma suma_distincts : ∀ (A B C D E F G H I: Point), SumA A B C D E F G H I →
   A≠B ∧ B≠C ∧ D≠E ∧ E≠F ∧ G≠H ∧ H≠I:=
begin
  rintros A B C D E F G H I Hsuma,
  rcases Hsuma with ⟨J, ⟨HCongaC,HnOS,HCongaA⟩⟩,
  unfold CongA at *, tauto!,
end

lemma ex_suma : ∀ (A B C D E F: Point), A≠B → B≠C → D≠E → E≠F →
   ∃ G H I, SumA A B C D E F G H I :=sorry 

lemma suma2__conga (A B C D E F G H I G' H' I': Point):
   SumA A B C D E F G H I → SumA A B C D E F G' H' I' → 
   CongA G H I G' H' I' :=sorry 


lemma conga3_suma__suma (A B C D E F G H I A' B' C' D' E' F' G' H' I': Point):
   SumA A B C D E F G H I →
   CongA A B C A' B' C' →
   CongA D E F D' E' F' →
   CongA G H I G' H' I' →
   SumA A' B' C' D' E' F' G' H' I' :=sorry 


lemma suma_sym (A B C D E F G H I: Point): SumA A B C D E F G H I → SumA D E F A B C G H I:=sorry

lemma inangle__suma : ∀ (A B C P: Point), InAngle P A B C → SumA A B P P B C A B C := sorry

lemma  lea_in_angle (A B C P: Point): LeA A B P A B C → OS A B C P →
   InAngle P A B C:=sorry


lemma sams_chara ( A B C D E F A': Point): A≠B → A'≠B → Bet A B A' →
   (SAMS A B C D E F ↔ LeA D E F C B A'):=sorry

lemma bet__suma : ∀ (A B C P: Point), A ≠ B → B ≠ C → P ≠ B → Bet A B C →
  SumA A B P P B C A B C := 
begin
  rintros A B C P HAB HBC HPB HBet,
  apply inangle__suma, 
  cleanup,
  simp[in_angle_line (ne.symm HPB) 
  (HAB) (ne.symm HBC) HBet], 
end 


lemma bet2_out_out(A B C B' C': Point): B ≠ A → B' ≠ A → Out A C C' → Bet A B C →
 Bet A B' C' → Out A B B':=sorry


lemma out2_bet_out : ∀ (A B C X P: Point),
 Out B A C → Out B X P → Bet A X C → Out B A P ∧ Out B C P :=sorry

 
lemma col123__nos (A B P Q: Point): Col P Q A → ¬ OS P Q A B:=sorry 


lemma suppa_sym (A B C D E F: Point): SuppA A B C D E F -> SuppA D E F A B C:=sorry

lemma suppa2__conga456(A B C D E F D' E' F': Point):
  SuppA A B C D E F -> SuppA A B C D' E' F' -> CongA D E F D' E' F':=sorry


lemma suppa2__conga123 : ∀( A B C D E F A' B' C': Point),
  SuppA A B C D E F -> SuppA A' B' C' D E F -> CongA A B C A' B' C' :=
begin
  rintros, 
  apply suppa2__conga456,
  apply suppa_sym _ _ _ D E F,
  assumption,
  apply suppa_sym _ _ _ _ _ _ ᾰ_1,
end 


lemma bet_suma__suppa ( A B C D E F G H I : Point):
  SumA A B C D E F G H I -> Bet G H I -> SuppA A B C D E F:=sorry

lemma conga_diff1 ( A B C A' B' C': Point): CongA A B C A' B' C' → A ≠ B :=
begin
    rintros H,
    unfold CongA at H,
    tauto!,
end 

lemma conga_diff2 ( A B C A' B' C': Point):  CongA A B C A' B' C' → C ≠ B:=
begin
    rintros H,
    unfold CongA at H,
    tauto!,
end 

lemma per2_suma__bet (A B C D E F G H I : Point): Per A B C → Per D E F →
   SumA A B C D E F G H I → Bet G H I := 
begin
  rintros HBRight HERight HSuma,
  rcases HSuma with ⟨A1 ,⟨HConga1 ,⟨HNos , HConga2⟩⟩⟩, 
  have HPer: (Per A1 B C) := l11_17 D E F _ _ _ HERight (conga_sym (conga_left_comm _ _ _ _ _ _ HConga1)),
  apply (bet_conga_bet A B A1), 
  apply (col_two_sides_bet _ C),
  rw col5 at *,
  apply (per_per_col _ _ C), tauto!,
  rcases HBRight with ⟨C', ⟨B,_⟩,HB⟩, 
  exact (bet_neqR _ _ _ (between_symmetry _ _ _ B)),
  assumption,
  rcases ⟨conga_diff1 _ _ _ _ _ _ HConga1, conga_diff1 _ _ _ _ _ _ HConga2,
  conga_diff2 _ _ _ _ _ _ HConga2⟩ with ⟨HBC, HNE1, HNE2⟩,
  apply not_one_side_two_sides,
  tauto!,
  apply per_not_col, 
  any_goals {tauto!,},
  apply per_not_col,
  any_goals {tauto!,},
end 

lemma suma_left_comm : ∀ (A B C D E F G H I : Point),
   SumA A B C D E F G H I → SumA C B A D E F G H I := sorry 

lemma bet_suma__sams ( A B C D E F G H I: Point): SumA A B C D E F G H I → Bet G H I →
  SAMS A B C D E F :=sorry

lemma sams123231 : ∀ (A B C: Point), A ≠ B → A ≠ C → B ≠ C → SAMS A B C B C A := sorry


lemma sams2_suma2__conga123 ( A B C A' B' C' D E F G H I: Point):
   SAMS A B C D E F → SAMS A' B' C' D E F →
   SumA A B C D E F G H I → SumA A' B' C' D E F G H I →
   CongA A B C A' B' C' :=sorry

lemma ncol_suma__ncol : ∀( A B C D E F : Point),
 ¬ Col A B C → SumA A B C B C A D E F → ¬ Col D E F :=sorry 


lemma sums2__cong56 : ∀ (A B C D E F E' F': Point), SumS A B C D E F → SumS A B C D E' F' →
  Cong E F E' F' :=sorry 

lemma sums112323 (A B C : Point): SumS A A B C B C:=sorry

lemma sums__cong2345 : ∀ (A B C D E: Point), SumS A A B C D E → Cong B C D E:=sorry

lemma ex_sums (A B C D: Point): ∃ E F, SumS A B C D E F:=
begin
  rcases segment_construction A B C D with ⟨R, ⟨HR1, HR2⟩⟩,
  use [A, R, A, B, R],
  refine ⟨by assumption, by cleanup, by cleanup, by cleanup⟩,
end 

lemma lta__lea (A B C D E F : Point): LtA A B C D E F → LeA A B C D E F :=sorry

lemma ex_trisuma : ∀( A B C : Point), A ≠ B → B ≠ C → A ≠ C →
  ∃ D E F, TriSumA A B C D E F :=sorry


lemma l12_21_b (A B C D: Point):
 TS A C B D →
 CongA B A C D C A → Par A B C D :=

 begin
  rintros HTS HCong1, 
  unfold TS at HTS,
  rcases ⟨NCdistinct HTS.1, NCdistinct HTS.2.1⟩ with ⟨HTS1, HTS2⟩,
  have H:= conga_distinct _ _ _ _ _ _ HCong1, 
    have: ¬ Col A B C,
      intro,
      cleanup, tauto!,
    have HH:= segment_construction_3 C D A B (ne.symm HTS2.2.2.1) (ne.symm HTS1.1),
    cases HH with D' HH, 
    have HCong2 : CongA B A C D' C A,
      apply l11_10, 
        apply HCong1,
        apply out_trivial, 
        tauto!, apply out_trivial, tauto!,
        apply out_sym, tauto!,
        apply out_trivial,
        tauto!,
    have HCong3: Cong D' A B C,
      apply cong2_conga_cong,
        apply conga_sym HCong2,
        cleanup,
      cleanup,
    have HTS3: TS A C D' B,
      apply l9_5,
        apply l9_2,
        apply HTS,
        apply col_trivial_3,
      simp*,
     unfold TS at HTS3,
    rcases HTS3 with ⟨H4, H5, M, H6⟩,
    have HBD: (B ≠ D'),
      intro heq, 
      cases bet.neq _ _ _ H6.2 with H7,
      tauto!,
    have HM: Midpoint M A C ∧ Midpoint M B D',
      apply l7_21,
        assumption,
        assumption,
        cleanup,
        cleanup,
        cleanup,
      apply bet_col,
      exact between_symmetry _ _ _ H6.2,
    have HPar: Par A B C D',
      apply l12_17,
        tauto!,
        apply HM.1,
      tauto!,
    apply par_col_par,
      tauto!,
      apply HPar,
      apply out_col, 
      apply out_sym,
      tauto!,
 end 


end

class tarski_2D (Point : Type) extends tarski_neutral_dimensionless_with_decidable_point_equality Point := 

(upper_dim : ∀ A B C P Q, P ≠ Q → Cong A P A Q → Cong B P B Q → Cong C P C Q →
  (Bet A B C ∨ Bet B C A ∨ Bet C A B))

open tarski_2D
open tarski_preneutral
open tarski_neutral_dimensionless_with_decidable_point_equality

--section Book_1_prop_1_circle_circle
section 

variables {Point : Type}
variable  [tarski_2D Point]

variables x y z : Point 

lemma prop_1_circle_circle : circle_circle_bis Point →
 ∀(A B: Point), ∃ C, Cong A B A C ∧ Cong A B B C:= sorry


/--To place at a given point (as an extremity) 
a straight line equal to a given straight line.-/

lemma prop_2 : ∀ (A B C D : Point), ∃ E, Bet A B E ∧ Cong B E C D :=
  begin
  apply segment_construction,
  end 

/--Given two unequal straight lines, to cut off from the
 greater a straight line equal to the less-/

lemma prop_3a (A B C D : Point) : Le A B C D → ∃ (E : Point), Bet C E D ∧ Cong A B C E :=
begin
  tauto,
end 

/--Given two unequal straight lines, to cut
 off from the greater a straight line equal to the less.-/

lemma prop_4 : ∀ (A B C A' B' C' : Point), CongA A B C A' B' C' → Cong B A B' A' → Cong B C B' C' →
  Cong A C A' C' ∧ (A ≠ C → CongA B A C B' A' C' ∧ CongA B C A B' C' A') := 
begin
  apply l11_49, 
end 

/--In isosceles triangles the angles at the base are equal to one another,
 and, if the equal straight lines be produced further, the angles 
 under the base will be equal to one another.-/

lemma prop_5_1 : ∀ (A B C : Point), ¬ Col A B C → Cong B A B C → 
CongA B A C B C A := 
begin
  apply l11_44_1_a,
end 

lemma prop_5_2  (A B C A' C': Point): ¬ Col A B C → Cong B A B C →
  Bet B A A' → A ≠ A' → Bet B C C' → C ≠ C' →
  CongA A' A C C' C A := 

  begin
    intros HCol HCong HBet HAA HBet HCC,
    apply l11_13 B A C B C A,
    apply l11_44_1_a,
    repeat {tauto!,},
  end 

/--If in a triangle two angles be equal to one another, 
the sides which subtend the equal angles will 
also be equal to one another. -/

lemma prop_6 : ∀ (A B C : Point), ¬ Col A B C → CongA B A C B C A → Cong B A B C :=  
begin
  apply l11_44_1_b,
end


/--Given two straight lines constructed on a straight line (from its extremities) 
and meeting in a point, there cannot be constructed on the same straight line 
(from its extremities), and on the same side of it, two other straight lines 
meeting in another point and equal to the former two respectively, namely each 
to that which has the same extremity with it.-/

lemma prop_7 (A B C C' : Point): Cong A C A C' → Cong B C B C' 
→ OS A B C C' → C = C' := 

begin
  rintros Hconga Hcongb HOS,
  have HNCol:= one_side_not_col123 A B C C' HOS, 
  have HH:= NCdistinct HNCol,
  rcases (l11_51 A B C A B C' HH.1 HH.2.2.1 HH.2.1 
  (cong_reflexivity A B) (Hconga) (Hcongb)) with ⟨HCongAA , ⟨HCongAB ,HCongAC⟩⟩,
  have HOS2 := l9_9_bis _ _ _ _ HOS,
  cases (conga__or_out_ts B A C C' HCongAA) with HOutA Habs,
  cases (conga__or_out_ts A B C C' HCongAB) with HOutB Habs,
  apply l6_21 A C B C, cleanup, repeat {tauto!,}, cleanup,
  exact out_col _ _ _ HOutA,
  simp * with out_simp,
  exact out_col  _ _ _ HOutB,
  exfalso,
  apply HOS2,
  exact invert_two_sides _ _ _ _ Habs,
end 

/--If two triangles have the two sides equal to two 
sides respectively, and have also the base equal to the base, 
they will also have the angles equal which are contained by the equal straight lines.
-/

lemma prop_8 (A B C A' B' C' : Point): A ≠ B → A ≠ C → B ≠ C →
       Cong A B A' B' → Cong A C A' C' → Cong B C B' C' →
       CongA B A C B' A' C' ∧ CongA A B C A' B' C' ∧ CongA B C A B' C' A' := 

begin
    rintros H H1 H2 H3 H4 H5,
    have: (Cong_3 B A C B' A' C' ∧ 
    Cong_3 A B C A' B' C' ∧ Cong_3 B C A B' C' A'),
    refine ⟨ _ , _, _ ⟩ ,
    repeat {unfold Cong_3, cleanup,},
    refine ⟨ _ , _, _⟩ ,
      all_goals {apply cong3_conga, 
      repeat {tauto!,},
      },
end


-- /-- To bisect a given rectilineal angle.-/

lemma prop_9 : ∀( A B C: Point), A ≠ B → C ≠ B →
  ∃ P : Point, InAngle P A B C ∧ CongA P B A P B C := 
begin
  apply angle_bisector,
end

-- /--To bisect a given finite straight line.-/ 

lemma prop_10 : ∀( A B: Point), ∃ X : Point, Midpoint X A B :=
begin
  apply midpoint_existence,
end

/--To draw a straight line at right angles to a given straight line from a 
 given point on it.-/

lemma prop_11 : ∀( A B C: Point), A ≠ B → Col A B C → ∃ X, Perp A B X C :=
begin
  rintros A B C HAB HCol,
  rcases (not_col_exists A B HAB) with ⟨ P,  HNCol⟩ ,
  rcases (l10_15 _ _ _ _ HCol HNCol) with ⟨ X, ⟨ HPerp , HOS⟩⟩, tauto!,
end 

/-- To a given infinite straight line, 
from a given point which is not on it, to draw a perpendicular straight line.-/

lemma prop_12 ( A B C: Point): ¬ Col A B C → ∃ X : Point, 
Col A B X ∧ Perp A B C X := 

begin
  apply l8_18_existence,

end 

/-- If a straight line set up on a straight line make angles, 
it will make either two right angles or angles equal to two right angles.-/

lemma prop_13 ( A B C D P Q R: Point): A ≠ B → B ≠ C → B ≠ D → Bet A B C →
  P ≠ Q → Q ≠ R → Per P Q R →
  SumA A B D D B C A B C ∧ SumA P Q R P Q R A B C :=

begin
  rintros HAB HBC HBD HBet HPQ HQR HPer,
  split,
    apply bet__suma, repeat {tauto!,},
    rcases (ex_suma P Q R P Q R HPQ HQR HPQ HQR) with ⟨S ,⟨T, ⟨U, HSuma⟩⟩⟩,
  apply conga3_suma__suma _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HSuma,
  any_goals {
  apply conga_refl, repeat {tauto},},
  apply conga_line, any_goals {tauto!,},
  unfold SumA at *, unfold Per at *, 
  cases HSuma with x Hsum,
  unfold CongA at Hsum, tauto!,
  cases HSuma with x Hsum, unfold CongA at Hsum, tauto!,
  apply (per2_suma__bet P Q R P Q R _ _ _ HPer HPer HSuma),
end 


/-- Proposition 14
 If with any straight line, and at a point on it, two straight lines not lying on the same
 side make the adjacent angles equal to two right angles, the two straight lines will 
 be in a straight line with one another.-/ 

lemma prop_14 (A B C D: Point): TS A B C D → Per A B C → Per A B D → Bet C B D := 

begin
  rintros HTS HPer1 HPer2,
    apply per2_suma__bet A B C A B D _ _ _ HPer1 HPer2,
    apply suma_left_comm,
    use D,
    unfold TS at *,
    rcases ⟨NCdistinct HTS.1, NCdistinct HTS.2.1⟩ with ⟨HTS1, HTS2⟩ ,
    refine ⟨_,_,_⟩,
    use conga_refl _ _ _ HTS1.2.1 HTS2.2.2.1,
    intro heq, 
    replace heq:= invert_one_side _ _ _ _ heq,
    have HH:=  l9_9 _ _ _ _ HTS, tauto!, 
    use conga_refl _ _ _ HTS1.2.2.1 HTS2.2.2.1,

end


/-- If two straight lines cut one another, they make the vertical angles equal to one another. -/

lemma prop_15 : ∀( A B C A' C': Point), Bet A B A' → A ≠ B → A' ≠ B →
  Bet C B C' → B ≠ C → B ≠ C' →
  CongA A B C A' B C' :=
begin
    rintros _ _ _ _ _ HBetA HAB HA'B HBetC HBC HBC',
    have HConga': (CongA A' B C C' B A),
    { 
      apply l11_13,
      apply conga_pseudo_refl, any_goals {tauto!,},
    },
      apply l11_13 ,
      apply conga_right_comm, repeat {tauto!,}, bet,
end


/-- In any triangle, if one of the sides is produced, 
the exterior angle is greater than either of the interior and opposite angles. -/

lemma prop_16 : ∀ (A B C D: Point), ¬ Col A B C → Bet B A D → A ≠ D →
  LtA A C B C A D ∧ LtA A B C C A D := 
  begin
  apply l11_41,
  end 
  

/-- In any triangle two angles taken together
 in any manner are less than two right angles.-/

lemma prop_17 : ∀( A B C D E F: Point), ¬ Col A B C → SumA A B C B C A D E F →
  SAMS A B C B C A ∧ ¬ Col D E F :=
begin
  rintros _ _ _  A B C HNCol HSumA,
  split,
  apply sams123231 _ _ _(not_col_distincts HNCol).2.1 
  (not_col_distincts HNCol).2.2.2(not_col_distincts HNCol).2.2.1, 
  apply (ncol_suma__ncol _ _ _ _ _ _) HNCol HSumA,
end 

/--In any triangle the greater side subtends the greater angle.-/

lemma prop_18 : ∀ (A B C: Point), ¬ Col A B C → Lt B A B C → Lt C A C B →
  LtA B C A B A C ∧ LtA A B C B A C :=

begin
  rintros _ _ _ NCol LtB LtC,
  split,
  apply l11_44_2_a, repeat{assumption},
  apply lta_comm, 
  apply l11_44_2_a _ _ _, cleanup, tauto,
end 

/-- In any triangle the greater angle is subtended by the greater side.-/

lemma prop_19 : ∀ (A B C: Point), ¬ Col A B C → LtA B A C B C A → LtA B A C A B C →
  Lt B C B A ∧ Lt C B C A :=
begin
  rintros _ _ _ NCol HLtA1 HLtA2,
  split,
  apply l11_44_2_b,
 repeat {assumption,},
  apply l11_44_2_b, cleanup,
    apply lta_comm, tauto!,
end 

/-- In any triangle two sides taken 
together in any manner are greater than the remaining one.-/

lemma prop_20 (A B C D E : Point): ¬ Bet A B C → 
SumS A B B C D E → Lt A C D E := 

begin
  rintros HNBet HSum,
  rcases (segment_construction A B B C) with ⟨D' , ⟨HBet , HCong⟩⟩,
  apply (cong2_lt__lt A C A D'), cleanup,
    apply triangle_strict_inequality _ _ _ _ HBet HCong HNBet, simp*,
  apply (sums2__cong56 A B B C), use [A, B, D'], simp*, tauto!,

end 


/-- If on one of the sides of a triangle, from its extremities,
 there be constructed two straight lines meeting within the triangle, 
 the straight lines so constructed will be less than the remaining two
  sides of the triangle, but will contain a greater angle. First half: 
  if D is inside the triangle ABC then BAC < BDC.of Euclid Book I, 
Proposition 21-/

lemma prop_21_1 : ∀ (A B C D: Point), OS A B C D → 
OS B C A D → OS A C B D → LtA B A C B D C:=
begin
apply os3__lta,
end 


lemma sums_assoc_1 (A B C D E F G H I J K L: Point):
  SumS A B C D G H → SumS C D E F I J → SumS G H E F K L →
  SumS A B I J K L :=sorry

lemma prop_21_2 (A B C D A1 A2 D1 D2: Point): OS A B C D → OS B C A D → OS A C B D →
  SumS A B A C A1 A2 → SumS D B D C D1 D2 → Lt D1 D2 A1 A2 := sorry



-- Proposition 22
-- Out of three straight lines, which are equal to three given straight lines, 
-- to construct a triangle: thus it is necessary that two of the straight lines 
-- taken together in any manner should be greater than the remaining one (cf. I. 20).
-- This needs Circle/Circle intersection axiom

lemma prop_22_aux (A B C D E F A' B' E' F' C1 C2 E1: Point):
  SumS A B C D E' F' → SumS C D E F A' B' → Le E F E' F' → Le A B A' B' →
  Out A B C1 → Cong A C1 C D → Bet B A C2 → Cong A C2 C D →
  Out B A E1 → Cong B E1 E F →
  Bet C1 E1 C2 := sorry


-- lemma prop_22 (A B C D E F A' B' C' D' E' F': Point) : 
--   circle_circle_bis Point → 
--   SumS A B C D E' F' → SumS A B E F C' D' → SumS C D E F A' B' →
--   Le E F E' F' → Le C D C' D' → Le A B A' B' →
--   ∃ P Q R, Cong P Q A B ∧ Cong P R C D ∧ Cong Q R E F :=sorry 
-- begin
--  rintros Hcc HSum1 HSum2 HSum3 HLe1 HLe2 HLe3, use [A, B],
--  by_cases A=B,
--   by_cases C=D, 
--     by_cases E=F,
--   cases segment_construction_0 C D A with P HCong,
--   use P, refine ⟨ by cleanup,by tauto!,_⟩ , 
--   subst B, 
--   apply cong_transitivity _ _ _ _ _ _ , exact HCong,
--   apply le_anti_symmetry,
--       apply l5_6 _ _ _ _ _ _ _ _ HLe2,  simp*, 
--     apply (sums2__cong56 A A E F), tauto!, 
--     apply sums112323,
--     apply l5_6 _ _ _ _ _ _ _ _ HLe1, cleanup, 
--     apply sums2__cong56, apply HSum1,apply sums112323,
--     use A, 
--     refine ⟨by cleanup, by simp * , _⟩,
--       apply (sums2__cong56 C C E F),
      

/-- On a given straight line and at a point on it to 
construct a rectilineal angle equal to a given rectilineal angle.-/

lemma prop_23 (A B C A' B' C': Point) :  A ≠ B → A ≠ C → B ≠ C → A' ≠ B' →
  ∃ C', CongA A B C A' B' C' :=
begin
  rintros HAB HAC HBC HAB',
  cases (not_col_exists A' B' HAB') with P HnCol,  
  cases angle_construction_2 A B C A' B' P HAB HAC HBC HAB' HnCol with C' HC,
  tauto!,
end 

/--  If two triangles have the two sides equal to 
two sides respectively, but have the one of the 
angles contained by the equal straight lines greater 
than the other, they will also have the base greater than the base.-/

lemma prop_24 (A B C D E F : Point): Cong A B D E → Cong A C D F → LtA F D E C A B →
  Lt E F B C := 
begin
 rintros HCongAB HCongAC Hlta,
  replace Hlta := lta_diff _ _ _ _ _ _ Hlta,
  rcases Hlta.1 with ⟨Hlta1,HnConga⟩,
  by_cases HCol: Col A B C, 
    by_cases HBet: Bet B A C,
      have HC' := segment_construction E D A C,
      rcases HC' with ⟨C', ⟨⟩⟩,
      apply cong2_lt__lt E F E C', 
      apply (triangle_strict_inequality _ D),
      tauto!,
      exact cong_symmetry _ _ _ _ ( cong_transitivity _ _ _ _ _ _ (HC'_h_right) ( HCongAC )),
      intro, 
      apply HnConga, 
      apply conga_line,
      repeat {tauto!,},
      simp * with geometry_simp,
      simp * with geometry_simp,
      exact cong_reflexivity E F,
      apply (l2_11 _ D _ _ A),
      repeat {assumption,},
      exact cong_commutativity _ _ _ _ (cong_symmetry _ _ _ _ HCongAB),
      exfalso,
      apply nlta C A B,
      apply lea123456_lta__lta _ _ _ F D E,
      apply lta__lea,
      have:= (lea_comm _ _ _ _ _ _ Hlta1),sorry

end 

/-- If two triangles have the two sides equal 
to two sides respectively, but have the base greater
 than the base, they will also have the one of the angles 
 contained by the equal straight lines greater than the other.-/

lemma prop_25 : ∀ (A B C D E F: Point), A ≠ B → A ≠ C →
  Cong A B D E → Cong A C D F → Lt E F B C →
  LtA F D E C A B := 

  begin
  rintros A B C D E F HAB HAC HCongAB HCongAC Hlt,
  apply nlea__lta, 
  intro HLea,
    by_cases CongA C A B F D E, 
    rintro,
    exfalso,
    cases Hlt with Hle HNCong,
    apply HNCong,
    have HSAS:= l11_49 C A B F D E h HCongAC HCongAB,
    cases HSAS with HCong1 HSAS, cleanup,
    apply not_and_lt E F B C,
    refine ⟨by assumption,_⟩ ,
    apply prop_24 D _ _ A, any_goals {cleanup,}, 
    unfold LtA, tauto!,
    exact cong_diff _ _ _ _ (HAC) HCongAC, 
    exact cong_diff _ _ _ _ (HAB) HCongAB,
  end 

/--this is ASA congruence-/
lemma prop_26_1 (A B C A' B' C': Point): ¬ Col A B C →
       CongA B A C B' A' C' → CongA A B C A' B' C' → Cong A B A' B' →
       Cong A C A' C' ∧ Cong B C B' C' ∧ CongA A C B A' C' B' :=
begin
   rintros,
    have HNE : A ≠ B ∧ C ≠ B ∧ A' ≠ B' ∧ C' ≠ B', 
    unfold CongA at *, tauto!, 
    have :(∃ C'', Out B' C'' C' ∧ Cong B' C'' B C),
      apply l6_11_existence, repeat {tauto!,},--;auto.
    cases this with C'' H7, --ex_and H7 C''.
    have HBC : B' ≠ C'',
      unfold Out at *, tauto!, --by (unfold Out in *;intuition).
    have HNCol: ¬ Col A' B' C', 
      apply ncol_conga_ncol _ _ _ _ _ _ ᾰ, assumption,
    have HNCol2 : (¬ Col A' B' C''),
      intro heq,
      apply HNCol,
      replace H7:= out_col _ _ _ H7.1,
      apply col_permutation_2,
      apply col_transitivity_1 _ C'',
      repeat {tauto!,},
      apply col_permutation_1,
      assumption,
    have HH:=l11_4_1 ᾰ_1,
    rcases HH with ⟨ HH1,HH2,HH3,HH4, HH5⟩ ,
    have HCong: Cong A C A' C'',
      apply HH5,
      refine ⟨_,_,_,_⟩ ,sorry 
    
      
end 


lemma prop_26_2 : ∀ (A B C A' B' C': Point), ¬ Col A B C →
       CongA B C A B' C' A' → CongA A B C A' B' C' → Cong A B A' B' →
       Cong A C A' C' ∧ Cong B C B' C' ∧ CongA C A B C' A' B' := 
  
  begin 
    apply l11_50_2,
  end 



/--  If a straight line falling on two straight lines 
make the exterior angle equal to the interior and opposite 
angle on the same side, or the interior angles on the same side 
equal to two right angles, the straight lines will be parallel to one another. -/ 

lemma prop_28_1 : ∀ (A B C D P: Point), Out P A C → OS P A B D → CongA B A P D C P → Par A B C D :=
begin
  apply l12_22_b,
end 


lemma prop_28_2 (A C G H P Q R: Point): OS G H A C → 
SumA A G H G H C P Q R → Bet P Q R →Par A G C H := 

begin
    rintros HOS HSumA HBet,
    have HNE:= suma_distincts _ _ _ _ _ _ _ _ _ HSumA,
    rcases (segment_construction C H C H) with ⟨D , ⟨HBet1, HCong⟩⟩,
    apply par_comm,
    apply par_col_par _ _ _ D,
    tauto!,
    apply l12_21_b,
    apply l9_8_2 _ _ C _ _,
    have HNCol := one_side_not_col124 G H A C HOS,
    have:= NCdistinct HNCol,
    refine ⟨ by cleanup,_,_⟩ ,
      intro,
      apply HNCol,
      have:= bet_col _ _ _ HBet1,
      replace ᾰ:= col_permutation_4 _ _ _ ᾰ,
      apply col_permutation_2,
      have HNE:= bet.neq _ _ _ HBet1,
      apply col_transitivity_1 _ _ _ _ HNE.1,
      cleanup, cleanup,
      use H, 
      try {cleanup, simp*,},
      apply suppa2__conga123 A G H G H C ,
      apply bet_suma__suppa A G H G H C P Q R HSumA HBet,
      split,
      exact (ne.symm (bet.neq _ _ _ HBet1).1),
      use C,
      split,
      simp * with geometry_simp,
      replace HOS:= os_distincts _ _ _ _ HOS,
      try {apply conga_refl}, repeat {tauto!,},
      simp [Col], 
      tauto!,

end     

end

class tarski_2D_euclidean (Point : Type) extends tarski_2D Point :=

 (euclid : ∀ (A B C D T: Point), Bet A D T → Bet B D C → A≠D → ∃ X, ∃ Y,
  Bet A B X ∧ Bet A C Y ∧ Bet X T Y)
  

open tarski_2D_euclidean
open tarski_preneutral
open tarski_2D
open tarski_neutral_dimensionless_with_decidable_point_equality 

section

  variables {Point : Type}
  variable  [tarski_2D_euclidean Point]


variables x y z : Point 


lemma col__coplanar  (A B C D: Point):
  Col A B C -> Coplanar A B C D:=
begin
  rintros,
  use C,
  cleanup,
end 


lemma ncop__ncol (A B C D: Point):
  ¬ Coplanar A B C D -> ¬ Col A B C:=
begin
  rintros HCoplanar,
  intro heq,
  apply HCoplanar,
  apply col__coplanar _ _ _ _ heq,
end 


/--Tarski's version of parallel postulate -/
def tarski_parallel_postulate  (Point : Type) [tarski_preneutral Point] : Prop := 
∀( A B C D T : Point),
  Bet A D T → Bet B D C → A ≠ D →
  ∃ X Y, Bet A B X ∧ Bet A C Y ∧ Bet X T Y

def consecutive_interior_angles_postulate (Point : Type) [tarski_preneutral Point]
: Prop := ∀ (A B C D P Q R: Point), OS B C A D → Par A B C D → SumA A B C B C D P Q R →
Bet P Q R



lemma alternate_interior__consecutive_interior :
alternate_interior_angles_postulate Point → 
consecutive_interior_angles_postulate Point :=
sorry

def playfair_s_postulate (Point : Type) [tarski_preneutral Point] :=  ∀ (A1 A2 B1 B2 C1 C2 P: Point),
  Par A1 A2 B1 B2 → Col P B1 B2 →
  Par A1 A2 C1 C2 → Col P C1 C2 →
  Col C1 B1 B2 ∧ Col C2 B1 B2 

def postulate_of_transitivity_of_parallelism (Point : Type) [tarski_preneutral Point] :=  
∀ (A1 A2 B1 B2 C1 C2 P: Point), Par A1 A2 B1 B2 → Par B1 B2 C1 C2 → 
Par A1 A2 C1 C2

lemma playfair_implies_par_trans  :
playfair_s_postulate Point → postulate_of_transitivity_of_parallelism Point  :=

begin
  rintros HP A1, rintros _ _ _ _ _ _ Hp1 Hp2,
  replace Hp1:= par_distincts _ _ _ _ Hp1,
  replace Hp2:= par_distincts _ _ _ _ Hp2,
  by_cases HCol: Col A1 A2 C1,
  right,
  have: (Col A1 C1 C2 ∧ Col A2 C1 C2),  
  exact HP B1 B2 C1 C2 A1 A2 C1 Hp2.1 (col_trivial_1 C1 C2) 
  (par_symmetry _ _ _ _ Hp1.1) (col_permutation_2 _ _ _ HCol),
  cleanup,
  left,
  refine ⟨by tauto!,by tauto!,_,_⟩ ,
  try {apply all_coplanar,},
  intro HX,
  cases HX with X HX,
    have: Col C1 A1 A2 ∧ Col C2 A1 A2,
    exact HP B1 B2 A1 A2 C1 C2 X (par_symmetry _ _ _ _ Hp1.1)
    HX.1 Hp2.1 HX.2,
  cleanup,
  tauto!,
end 

lemma tarski_s_euclid : tarski_parallel_postulate Point := 
begin
  unfold tarski_parallel_postulate,
  rintros _ _ _ _ _ HBet1 HBet2 HAD,
  apply euclid A B C D T HBet1 HBet2 HAD,
end

lemma tarski_s_euclid_implies_playfair :
tarski_parallel_postulate Point → playfair_s_postulate Point :=sorry 

lemma parallel_uniqueness ( A1 A2 B1 B2 C1 C2 P : Point):
  Par A1 A2 B1 B2 → Col P B1 B2 →
  Par A1 A2 C1 C2 → Col P C1 C2 →
  Col C1 B1 B2 ∧ Col C2 B1 B2 :=
begin
    rintros,
    apply tarski_s_euclid_implies_playfair,
    try{ assumption}, 
    apply tarski_s_euclid, 
    repeat 
    {tauto!,},
end 

lemma par_trans ( A1 A2 B1 B2 C1 C2 : Point):
  Par A1 A2 B1 B2 → Par B1 B2 C1 C2 → Par A1 A2 C1 C2:=
 begin
    rintros,
    apply playfair_implies_par_trans ,
    try {assumption,},
    unfold playfair_s_postulate,
    apply parallel_uniqueness , 
    repeat {tauto!,},
  end




def euclid_s_parallel_postulate (Point : Type) [tarski_preneutral Point] := 
∀ (A B C D P Q R: Point), OS B C A D → SAMS A B C B C D → 
SumA A B C B C D P Q R → ¬ Bet P Q R → ∃ Y, Out B A Y ∧ Out C D Y

def euclid_5 (Point : Type) [tarski_preneutral Point] := ∀ (P Q R S T U: Point),
  Bet P T Q → Bet R T S → Bet Q U R → ¬ Col P Q S →
  Cong P T Q T → Cong R T S T →
  ∃ I, Bet S Q I ∧ Bet P U I

lemma l5_3 ( A B C D: Point):
 Bet A B D → Bet A C D → Bet A B C ∨ Bet A C B :=sorry

lemma par_strict_distinct (A B C D:Point):
 Par_strict A B C D → A≠B ∧ C≠D:=sorry


lemma tarski_parallel_implies_euclid_5 :
  tarski_parallel_postulate Point → euclid_5 Point := sorry
  begin
    rintros HT P Q R S T U HPTQ HRTS HQUR HNC HCong1 HCong2, 
    cases symmetric_point_construction P R with V HMid,
    rcases inner_pasch V Q R P U (between_symmetry _ _ _ HMid.1) HQUR with ⟨W , ⟨HPWQ , HUWV⟩⟩,
    rcases ⟨bet.neq _ _ _  HPWQ , bet.neq _ _ _ HUWV, bet.neq _ _ _ HMid.1, NCdistinct HNC⟩ 
    with ⟨HNE1, HNE2, HNE3, HNE4⟩ ,
    unfold tarski_parallel_postulate at HT,
    rcases HT P V U W Q HPWQ (between_symmetry _ _ _ HUWV) HNE1.2.1 with ⟨X ,⟨Y ,⟨HPVX ,⟨HPUY, HXQY⟩⟩⟩⟩,
    rcases ⟨NCdistinct HNC, bet.neq _ _ _ HPVX, bet.neq _ _ _ HPUY,
    bet.neq _ _ _ HXQY, bet.neq _ _ _  HQUR⟩ with ⟨HNE5, HNE6, HNE7, HNE8, HNE10⟩,
    have HRPV:= midpoint_bet _ _ _ HMid,
    have HPar : Par_strict Q S P R,
    {
    apply par_not_col_strict _ _ P _ P,
    apply l12_17 _ _ _ _ T HNE4.2.1, any_goals {split, simp * with geometry_simp, cleanup,},
    simp [Col], cleanup,},
    have HTS: TS Q S P Y,
    {apply l9_8_2 _ _ X _, split,
      apply par_strict_not_col_2 _,
      apply par_strict_symmetry,
      apply par_strict_col_par_strict _ _ _ R _, exact HNE6.2.2,
      tauto!, apply col_permutation_4, apply bet_col,
      exact outer_transitivity_between _ _ _ _  HRPV HPVX HNE6.2.1,
      constructor,
      have HNC1: ¬ Col X Q S, 
      { apply par_strict_not_col_2 _,
      apply par_strict_symmetry,
      apply par_strict_col_par_strict _ _ _ R _, exact HNE6.2.2,
      tauto!, apply col_permutation_4, apply bet_col,
      exact outer_transitivity_between _ _ _ _  HRPV HPVX HNE6.2.1,},
      intro HCol, have: Q = Y, {apply l6_21 Q S X Q,
      cleanup, 
      rcases NCdistinct HNC1 with ⟨HNE9⟩ ,
      cleanup, cleanup, cleanup, cleanup, 
      exact bet_col _ _ _ HXQY,},
      have HQU: Q = U, {apply l6_21 Q P R Q, 
      apply par_strict_not_col_2 S, 
      exact par_strict_left_comm _ _ _ _ HPar, 
      tauto!, 
      cleanup, 
      tauto!,
      tauto!, tauto!,}, 
      tauto!,
      use Q, 
      cleanup,
      apply l12_6, 
      apply par_strict_right_comm,
      apply par_strict_col_par_strict _ _ _ R, 
      any_goals {cleanup,},
      apply col_permutation_4, 
      apply bet_col, 
      exact outer_transitivity_between _ _ _ _  HRPV HPVX HNE6.2.1,
      },
      rcases HTS with ⟨Hc1, ⟨Hc2,⟨I,⟨HCol, HBet⟩⟩⟩⟩, use Y,
      clear Hc1, clear Hc2, cleanup,
      by_contradiction,
      suffices : R = U, tauto!,
      apply l6_21 P R Q U ,
       have HPRQ:= par_strict_not_col_1 _ _ _ _ 
      (par_strict_symmetry _ _ _ _ HPar), 
      have HQSR:= par_strict_not_col_1 _ _ _ _ 
      (par_strict_right_comm _ _ _ _ HPar), 
      have HRSQ:= not_col_permutation_3 _ _ _( par_strict_not_col_1 _ _ _ _ 
      (par_strict_right_comm _ _ _ _ HPar)), cleanup, tauto!,
      cleanup, apply bet_col, rw bet_neq, tauto!,
      apply bet_col, tauto!, 
      cleanup,
       end 

lemma per_col (A B C D : Point):
 B ≠ C → Per A B C → Col B C D → Per A B D:=sorry 

lemma per__ex_saccheri (A B D: Point): Per B A D → A ≠ B → A ≠ D →
  ∃ C, Saccheri A B C D :=
begin
  rintros HPer HAB HBD,
  have HNCol : ¬ Col B A D, apply per_not_col,
  any_goals {tauto!,}, 
  rcases (l10_15 A D D B (col_trivial_2 A D) 
  (not_col_permutation_1 _ _ _ HNCol)) with ⟨C0,⟨_⟩⟩,
  have HnCol: ¬ Col A D C0, 
    apply (one_side_not_col123 _ _ _ B), simp*,
  rcases ⟨NCdistinct HnCol, os_distincts _ _ _ _ h_right⟩ with ⟨HNE, HNE2⟩,
  rcases (segment_construction_3 D C0 A B HNE.2.1 HAB) with ⟨C ,⟨_⟩⟩,
  use C,
  split, assumption,
  split,
  apply per_col _ _ C0, tauto!,
  apply perp_per_1,
  exact perp_left_comm _ _ _ _ h_left,
  apply out_col _ _ _ h_left_1,
  split,
  exact cong_symmetry _ _ _ _ (cong_left_commutativity _ _ _ _ h_right_1),
  apply invert_one_side,
  apply out_out_one_side _ _ _ C0, 
  exact invert_one_side _ _ _ _ h_right,
  assumption,
end

lemma sac_rectangle (A B C D : Point):Saccheri A B C D → Rectangle A B C D :=sorry

lemma plg_cong (A B C D: Point):
  Parallelogram A B C D →
 Cong A B C D ∧ Cong A D B C :=sorry 


lemma plg_conga (A B C D: Point): A ≠ B ∧ A ≠ C ∧ B ≠ C 
→ Parallelogram A B C D → CongA A B C C D A ∧ CongA B C D D A B :=sorry 

lemma mid_plgf (A B C D M: Point):
  (A ≠ C ∨ B ≠ D ) →
  Col A B C →
  Midpoint M A C → Midpoint M B D →
  Parallelogram_flat A B C D :=sorry 

lemma mid_plgs (A B C D M: Point):
  ¬ Col A B C → Midpoint M A C → Midpoint M B D →
  Parallelogram_strict A B C D := sorry 

lemma mid_plg (A B C D M: Point): (A ≠ C ∨ B ≠ D ) →
 Midpoint M A C → Midpoint M B D →
 Parallelogram A B C D := 
begin
  rintros,
  unfold Parallelogram,
  by_cases HCol: Col A B C,
    right,
    apply (mid_plgf _ _ _ _ M),
  repeat {assumption,},
  left,
  apply (mid_plgs _ _ _ _ M),
  repeat {assumption,},
end 

lemma plgs_permut (A B C D: Point):
  Parallelogram_strict A B C D →
  Parallelogram_strict B C D A :=sorry 

lemma plgf_permut (A B C D: Point):
  Parallelogram_flat A B C D →
  Parallelogram_flat B C D A :=sorry 

lemma plg_permut (A B C D: Point):
  Parallelogram A B C D → Parallelogram B C D A :=
begin
intros HPara,
cases HPara, 
  {
  left, apply plgs_permut, tauto!,
  },

  {right, apply plgf_permut, tauto!,
  }
end 

lemma plg_mid (A B C D: Point):
  Parallelogram A B C D →
  ∃ M, Midpoint M A C ∧ Midpoint M B D:=sorry 

lemma plg_to_parallelogram (A B C D: Point): Plg A B C D → Parallelogram A B C D:=
begin
  rintros H,
  unfold Plg at H,
  cases H.2 with M HPlg,
  apply (mid_plg _ _ _ _ M),
  induction H,
  repeat {tauto!,},
end

lemma parallelogram_to_plg (A B C D: Point):  Parallelogram A B C D → Plg A B C D:=sorry 

lemma plg_par (A B C D: Point): A ≠ B → B ≠ C → Parallelogram A B C D → 
Par A B C D ∧ Par A D B C:=sorry

lemma rect_permut ( A B C D : Point ) : Rectangle A B C D → Rectangle B C D A:=
begin
  rintros HRect,
  unfold Rectangle at HRect,
  cases HRect with HPlg HCongA,
  split,
  replace HPlg:= plg_permut _ _ _ _( plg_to_parallelogram _ _ _ _ HPlg),
  exact parallelogram_to_plg _ _ _ _ HPlg,
  cleanup,
end 

lemma exists_square ( A B: Point): A ≠ B →  ∃ C D, Square A B C D:= 
begin
  rintros, 
  rcases exists_cong_per A B A B with ⟨C, ⟨HC1, HC2⟩ ⟩ ,
  cases (per__ex_saccheri B C A (l8_2 _ _ _ HC1)  (cong_diff2 _ _ _ _ ᾰ HC2) (ne.symm ᾰ)) with D HSac,
  use [C, D],
  have: Rectangle B C D A , apply sac_rectangle, tauto, unfold Square, cleanup,
  exact rect_permut _ _ _ _ (rect_permut _ _ _ _(rect_permut _ _ _ _ this)),
end 


lemma l12_21_a (A B C D : Point):
  TS A C B D → (Par A B C D → CongA B A C D C A):= sorry

/-- 
 If a straight line falling on two straight lines 
make the alternate angles equal to one another, 
the straight lines will be parallel to one another.-/
lemma prop_27 : ∀ (A B C D: Point), TS A C B D → CongA B A C D C A → Par A B C D := 
begin
  apply l12_21_b,
end 

lemma prop_29_1  (A B C D: Point): TS A C B D → Par A B C D → CongA B A C D C A:= 
begin
  apply l12_21_a,
end 

lemma prop_29_2 : ∀ (A B C D P: Point), Out P A C → OS P A B D → Par A B C D →
  CongA B A P D C P :=
begin
  apply l12_22_a,
end 

lemma prop_29_3 : ∀ (A B C D P Q R: Point), OS B C A D → 
Par A B C D → SumA A B C B C D P Q R →
  Bet P Q R := 
begin 
  apply alternate_interior__consecutive_interior,
  unfold alternate_interior_angles_postulate,
  apply l12_21_a,
end 

/--Straight lines parallel to the same straight 
line are also parallel to one another.-/

lemma prop_30  (A1 A2 B1 B2 C1 C2: Point ): Par A1 A2 B1 B2 → Par B1 B2 C1 C2 →
   Par A1 A2 C1 C2 := 
   begin
   apply par_trans,
   end 


/-- Through a given point to draw a straight line
 parallel to a given straight line.-/

lemma prop_31 ( A B P: Point): A ≠ B → ∃ Q, Par A B P Q := 
begin
  apply parallel_existence1,
end 


/--
 In any triangle, if one of the sides be produced, 
the exterior angle is equal to the two interior and opposite angles, 
and the three interior angles of the triangle are equal to two right angles. -/

lemma prop_32_1 : ∀ (A B C D E F: Point), TriSumA A B C D E F → Bet D E F:= 
begin 
  apply alternate_interior__triangle,
  unfold alternate_interior_angles_postulate,
  apply l12_21_a,
end 

lemma prop_32_2 : ∀ (A B C D: Point), A ≠ B → B ≠ C → A ≠ C → Bet B C D → C ≠ D →
  SumA C A B A B C A C D := 
  begin
    rintros A B C D HAB HBC HAC HBet HCD,
    rcases (ex_trisuma C A B (ne.symm HAC) HAB (ne.symm HBC)) 
    with ⟨P ,⟨Q ,⟨R, HTri⟩⟩⟩,
    have HBet2: Bet P Q R, apply (prop_32_1 C A B _ _ _) HTri, 
    rcases ⟨bet.neq _ _ _ HBet,bet.neq _ _ _ HBet2⟩ with ⟨HN1, HN2⟩ , 
    rcases HTri with ⟨S ,⟨T ,⟨U, ⟨HSuma1, HSuma2⟩⟩⟩⟩,
    apply conga3_suma__suma C A B A B C S T U,
    any_goals {try {apply conga_refl,}, repeat {tauto!,},},
    have HCongA: CongA B C D P Q R,
      apply conga_line, 
      repeat{tauto!,},
    have HSumA' : SumA A C D B C A P Q R,
      apply conga3_suma__suma A C D B C A B C D,
      apply suma_sym,
      apply bet__suma,
      repeat {tauto!,},
      exact conga_refl _ _ _ HAC (ne.symm HCD),
      exact conga_refl _ _ _ HBC HAC,
      apply sams2_suma2__conga123 _ _ _ _ _ _ _ _ _ _ _ _ _ ,
      apply bet_suma__sams _ _ _ _ _ _ _ _ _ ,
      repeat {assumption,},
      apply bet_suma__sams _ _ _ _ _ _ _ _ _ HSuma2 HBet2,
end 



lemma prop_33 : ∀ (A B C D: Point),
 TS A C B D → Par A B C D → Cong A B C D →
 Cong A B C D ∧ Cong A D B C ∧ Par A D B C := 

begin
  rintros A B C D HTS HPAR HC,
  have HPara :Parallelogram A B C D, 
  unfold Parallelogram,
  left,
  unfold Parallelogram_strict, tauto!,
  have T:=plg_cong A B C D HPara,
  have HBC:B≠C, intro heq,
  unfold TS at *, cleanup, 
  apply (NCdistinct HTS.1).2.1, 
  assumption,
  have HPar:= plg_par A B C D (ne.symm(NCdistinct HTS.1).1) HBC HPara,
  tauto!,
end 



lemma prop_34 (A B C D: Point) :
  A ≠ B ∧ A ≠ C ∧ B ≠ C →
  Parallelogram A B C D → (CongA A B C C D A ∧ CongA B C D D A B)
   ∧ (Cong A B C D ∧ Cong A D B C):=

   begin
   rintros H0 H1,
   refine ⟨_,_⟩,
   apply plg_conga, repeat {tauto!,}, 
   exact plg_cong _ _ _ _ H1,
   end 

  

lemma prop_46 : ∀ (A B: Point), A≠B → ∃ C D, Square A B C D := 
begin
  exact exists_square,
end 

/-- In right-angled triangles the square on the side subtending 
the right angle is equal to the squares on the sides containing 
the right angle. This is the Pythagoras theorem. Pythagoras is tied 
to the parallel postulate, in the sense that we need the parallel postulate 
to express it. Here, we have a statement based on the geometric definition 
of addition and multiplication as predicates.-/

lemma prop_47 :
     ∀ (O E E' A B C AC BC AB AC2 BC2 AB2: Point),
       O ≠ E →
       Per A C B → Length O E E' A B AB → Length O E E' A C AC →  Length O E E' B C BC →
       Prod O E E' AC AC AC2 →Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 →
       Sum O E E' AC2 BC2 AB2 := 
    begin 
    exact pythagoras,
    end 
  


end 

