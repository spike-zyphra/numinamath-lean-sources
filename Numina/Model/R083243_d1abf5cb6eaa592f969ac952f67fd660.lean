import Mathlib

theorem algebra_203521 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a = 2 ∧ b = Real.sqrt 2) :
    (√2 ^ 2 / a ^ 2 + 1 ^ 2 / b ^ 2 = 1) ∧ ¬
    (∀ a b : ℝ, a ≠ 0 → b ≠ 0 → (√2 ^ 2 / a ^ 2 + 1 ^ 2 / b ^ 2 = 1) → a = 2 ∧ b = Real.sqrt 2) := by
  constructor
  · -- Show (√2 ^ 2 / a ^ 2 + 1 ^ 2 / b ^ 2 = 1) given (a = 2 ∧ b = Real.sqrt 2)
    rcases h with ⟨ha2, hb2⟩
    rw [ha2, hb2]
    have h1 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
    have h3 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by rw [Real.sq_sqrt]; norm_num
    field_simp [h1, h2, h3]
    <;> norm_num
  · -- Show ¬∀ a b : ℝ, a ≠ 0 → b ≠ 0 → (√2 ^ 2 / a ^ 2 + 1 ^ 2 / b ^ 2 = 1) → a = 2 ∧ b = Real.sqrt 2
    intro h1
    have h2 := h1 (Real.sqrt 3) (Real.sqrt 3) (by positivity) (by positivity) (by
      have h3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h1 : (1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h3]
      rw [h2]
      rw [h1]
      norm_num
    )
    have h3 : Real.sqrt 3 = 2 := by
      have h4 : Real.sqrt 3 = 2 := by 
        have h5 : Real.sqrt 3 = 2 := by
          linarith [h2.1]
        linarith
      linarith
    have h4 : Real.sqrt 3 < 2 := by
      have h5 : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h6 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith
    linarith [h3, h4]