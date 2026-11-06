import Mathlib

theorem algebra_148444 (p : ℝ → ℝ) (hp : p = fun x => -2 * x ^ 3 + 6 * x) :
    ∃ a d, ∀ x, p x = 0 ↔ x = a ∨ x = a + d ∨ x = a + 2 * d := by 
  use -Real.sqrt 3 
  use Real.sqrt 3 
  intro x
  have h1 : p x = -2 * x ^ 3 + 6 * x := by
    rw [hp]
  constructor
  · -- Assume p x = 0, prove the disjunction 
    intro h
    rw [h1] at h
    have h2 : -2 * x ^ 3 + 6 * x = 0 := by 
      linarith 
    have h3 : -2 * x ^ 3 + 6 * x = -2 * x * (x ^ 2 - 3) := by 
      ring 
    rw [h3] at h2 
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case h4: -2 * x = 0. Then x = 0. 
      have hx0 : x = 0 := by 
        nlinarith 
      right 
      left 
      linarith 
    · -- Case h5: x^2 - 3 = 0. 
      have hx2 : x ^ 2 = 3 := by 
        nlinarith 
      have h6 : x = Real.sqrt 3 ∨ x = -Real.sqrt 3 := by 
        have h7 : x ^ 2 = (3 : ℝ) := hx2 
        have h8 : x = Real.sqrt 3 ∨ x = -Real.sqrt 3 := by 
          apply eq_or_eq_neg_of_sq_eq_sq 
          field_simp 
          linarith 
        exact h8 
      cases h6 with 
      | inl h7 => 
        right 
        right 
        nlinarith 
      | inr h8 => 
        left 
        nlinarith 
  · -- Assume the disjunction, prove p x = 0 
    intro h 
    rcases h with (h | h | h)
    · -- Case x = -Real.sqrt 3 
      rw [h1]
      rw [h] 
      have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Case x = 0 
      rw [h1]
      rw [h] 
      all_goals norm_num 
    · -- Case x = Real.sqrt 3 
      rw [h1]
      rw [h] 
      have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]