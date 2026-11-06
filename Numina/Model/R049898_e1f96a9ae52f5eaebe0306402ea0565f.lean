import Mathlib

open Real
open scoped BigOperators

theorem calculus_11373 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : (a + b + c) * (a + b - c) = 3 * a * b) :
  arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) * 180 / π = 60 := by
  -- to prove angle is 60 degree, we need prove a^2+b^2-c^2=ab. Then use cos formula
  have h1 : a^2 + b^2 - c^2 = a * b := by
    -- expanding (a + b + c)(a + b - c) = 3ab
    nlinarith

  have h2 : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) = 1 / 2 := by
    -- Substitute h1 into the expression
    have h3 : a ^ 2 + b ^ 2 - c ^ 2 = a * b := by linarith only [h1]
    have h4 : a * b ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    rw [h3]
    field_simp [h4]
    <;> linarith

  have h3 : arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) = Real.pi / 3 := by
    rw [h2]
    have h : arccos (1 / 2) = Real.pi / 3 := by
      have h1 : cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
      rw [← h1]
      apply arccos_cos
      all_goals linarith [Real.pi_pos]
    exact h

  rw [h3]
  field_simp [Real.pi_pos]
  <;> linarith