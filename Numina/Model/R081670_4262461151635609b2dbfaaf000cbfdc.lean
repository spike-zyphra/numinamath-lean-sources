import Mathlib

theorem number_theory_287480 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hsum : x + y = 60) (hlcm : Nat.lcm x y = 273) :
    x = 21 ∧ y = 39 ∨ x = 39 ∧ y = 21 := by
  have h1 : y = 60 - x := by omega
  rw [h1] at hlcm
  have h2 : x ≤ 59 := by 
    omega 
  interval_cases x <;> norm_num [Nat.lcm] at hlcm <;> 
    omega