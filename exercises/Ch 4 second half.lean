import data.real.basic



variables log exp     : real → real
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc
   log (x * y) = log (log (exp x)) + log (log (exp y)) : by rw log_exp_eq
   ... = 





-- -- Prove the theorem below, using only the ring properties 
-- --of ℤ enumerated in Section 4.2 and the theorem sub_self.

-- -- import data.int.basic

-- -- #check sub_self

-- -- example (x : ℤ) : x * 0 = 0 :=
-- -- begin
-- --  intros x,
-- --  rw sub_self 0,


-- -- end 
import data.real.basic
example (x y: ℝ) : (x + y) * (x + y) = x * x + x * y + x * y  + y * y :=
calc
   (x + y) * (x + y) = (x + y) * x + (x + y) * y : by rw mul_add
   ... = (x * x + y * x) + (x * y + y * y) : by rw [add_mul, add_mul] 
   ... = x * x + x * y + x * y  + y * y : by rw [mul_comm y x, ←add_assoc]


example (x y: ℝ) : (x + y) * (x + y) = x * x + x * y + x * y  + y * y :=
  by rw [mul_add, add_mul, add_mul, mul_comm y x, ←add_assoc]
