import Mathlib

theorem algebra_278178 (a k n : ℝ) (ha : 0 < a ∧ a ≠ 1) (hk : 0 < k) :
    Real.logb (a ^ k) (a ^ n) = n / k := by
  have ha1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2
  have h1 : Real.logb (a ^ k) (a ^ n) = (Real.log (a ^ n)) / (Real.log (a ^ k)) := by
    rw [Real.logb]
  rw [h1]
  have h2 : Real.log (a ^ n) = n * Real.log a := by
    rw [Real.log_rpow]
    all_goals
      try linarith
  have h3 : Real.log (a ^ k) = k * Real.log a := by
    rw [Real.log_rpow]
    all_goals
      try linarith
  rw [h2, h3]
  have h4 : Real.log a ≠ 0 := by
    have h5 : a > 0 := ha1
    have h6 : a ≠ 1 := ha2
    exact Real.log_ne_zero_of_pos_of_ne_one ha1 ha2
  field_simp [h4]
  <;> ring