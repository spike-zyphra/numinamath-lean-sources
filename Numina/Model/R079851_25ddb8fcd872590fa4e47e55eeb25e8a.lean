import Mathlib

theorem number_theory_2741
    {x y : ℕ}
    (hxpos : 0 < x)
    (hypos : 0 < y)
    (hsum : x + y = 60)
    (hlcm : Nat.lcm x y = 273) :
    x * y = 819 := by
  have h1 : x ≤ 60 := by linarith
  have h2 : y ≤ 60 := by linarith
  interval_cases x <;> interval_cases y <;> norm_num [Nat.lcm] at hlcm hsum ⊢ <;> omega