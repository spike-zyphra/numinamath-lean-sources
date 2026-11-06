import Mathlib

theorem algebra_14971 (z : ℝ) :
    z^4 - 4 * z^2 + 3 = 0 ↔
    z = -Real.sqrt 3 ∨ z = -1 ∨ z = 1 ∨ z = Real.sqrt 3 := by
  constructor
  · -- Forward direction: z^4 - 4z^2 + 3 = 0 implies the four solutions
    intro h
    have h1 : (z^2 - 1) * (z^2 - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case where z^2 - 1 = 0, so z^2 = 1
      have h4 : z^2 = 1 := by linarith
      have h5 : z = 1 ∨ z = -1 := by
        rw [sq_eq_one_iff] at h4
        exact h4
      cases' h5 with h6 h7
      · -- z = 1
        simp [h6]
      · -- z = -1
        simp [h7]
        <;> tauto
    · -- Case where z^2 - 3 = 0, so z^2 = 3
      have h8 : z^2 = 3 := by linarith
      have h9 : z = Real.sqrt 3 ∨ z = -Real.sqrt 3 := by
        have h11 : z^2 = 3 := by linarith
        have h12 : z^2 = (Real.sqrt 3) ^ 2 := by
          rw [h11]
          rw [Real.sq_sqrt]
          all_goals nlinarith
        have h13 : z = Real.sqrt 3 ∨ z = -Real.sqrt 3 := by
          apply eq_or_eq_neg_of_sq_eq_sq
          all_goals nlinarith
        exact h13
      cases' h9 with h18 h19
      · -- z = Real.sqrt 3
        simp [h18]
      · -- z = -Real.sqrt 3
        simp [h19]
        <;> tauto
  · -- Reverse direction: the four solutions satisfy z^4 - 4z^2 + 3 = 0
    rintro (h | h | h | h)
    · -- z = -Real.sqrt 3
      rw [h]
      have h1 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [h1, Real.sqrt_nonneg 3]
    · -- z = -1
      rw [h]
      norm_num
    · -- z = 1
      rw [h]
      norm_num
    · -- z = Real.sqrt 3
      rw [h]
      have h1 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [h1, Real.sqrt_nonneg 3]