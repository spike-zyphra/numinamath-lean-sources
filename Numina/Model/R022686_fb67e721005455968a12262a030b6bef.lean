import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12629 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
  (h : a = 2 ∧ b = sqrt 2) :
  (sqrt 2)^2 / a^2 + 1^2 / b^2 = 1 ∧ ¬(∀ a b : ℝ, a ≠ 0 → b ≠ 0 →
  (√2)^2 / a^2 + 1^2 / b^2 = 1 → a = 2 ∧ b = sqrt 2) := by
  rcases h with ⟨ha2, hb2⟩
  constructor
  · -- Prove (sqrt 2) ^ 2 / a ^ 2 +1^2 / b ^ 2= 1.
    -- Substitute a = 2, b = sqrt 2, which is given from h
    rw [ha2, hb2]
    have h1 : (sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [h1]
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
  · -- Prove the condition is not necessary by finding a couterexample
    intro h1
    have h2 := h1 (Real.sqrt 3) (Real.sqrt 3) (by positivity) (by positivity)
    have h2' : (√2 : ℝ) ^ 2 / (Real.sqrt 3) ^ 2 + (1 : ℝ) ^ 2 / (Real.sqrt 3) ^ 2 = 1 := by
      have h5 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h5' : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      rw [h5, h5']
      field_simp
      <;> norm_num
      <;> linarith
    specialize h2 h2'
    -- h2 gives that sqrt 3 = 2 ∧ sqrt 3 = sqrt 2, which is false
    have h3 : Real.sqrt 3 = (2 : ℝ) := by 
      linarith [h2.1, h2.2]
    -- sqrt 3 < 2 is false
    have h4 : Real.sqrt 3 < (2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]