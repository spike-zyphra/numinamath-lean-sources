import Mathlib

theorem algebra_241771 (x y : ℝ) :
    4 * (x^4 + 3 * x^2 + 1) * (y^4 - 5 * y^2 + 19) = 51 ↔
    (x = 0 ∧ y = Real.sqrt (5 / 2)) ∨ (x = 0 ∧ y = -Real.sqrt (5 / 2)) := by
  constructor
  · -- Assume equation, solve
    intro h
    have h1 : x^4 + 3 * x^2 + 1 ≥ 1 := by 
      nlinarith [sq_nonneg (x^2), sq_nonneg (x^2 - 0)]
    have h2 : y^4 - 5 * y^2 + 19 ≥ 51 / 4 := by
      nlinarith [sq_nonneg (2 * y^2 - 5)]
    have h_eq1 : x^4 + 3 * x^2 + 1 = 1 := by
      nlinarith [h, mul_nonneg (show (0 : ℝ) ≤ x^4 + 3 * x^2 + 1 by linarith) (show (0 : ℝ) ≤ y^4 - 5 * y^2 + 19 by nlinarith), h1, h2]
    have h_eq2 : y^4 - 5 * y^2 + 19 = 51 / 4 := by
      nlinarith [h, mul_nonneg (show (0 : ℝ) ≤ x^4 + 3 * x^2 + 1 by linarith) (show (0 : ℝ) ≤ y^4 - 5 * y^2 + 19 by nlinarith), h1, h2]
    have hx1 : x^2 = 0 := by
      nlinarith [sq_nonneg (x^2), h_eq1]
    have hx : x = 0 := by
      nlinarith
    have hy2 : y^2 = 5 / 2 := by
      nlinarith [sq_nonneg (2 * y^2 - 5), h_eq2]
    have hy1 : y = Real.sqrt (5 / 2) ∨ y = -Real.sqrt (5 / 2) := by
      have h1 : y^2 = 5 / 2 := hy2
      have h2 : y^2 - 5 / 2 = 0 := by linarith
      have h3 : (y - Real.sqrt (5 / 2)) * (y + Real.sqrt (5 / 2)) = 0 := by
        have h4 : y^2 - 5 / 2 = 0 := h2
        have h5 : (y - Real.sqrt (5 / 2)) * (y + Real.sqrt (5 / 2)) = y^2 - (Real.sqrt (5 / 2)) ^ 2 := by ring
        rw [h5]
        rw [Real.sq_sqrt (by norm_num)]
        linarith
      cases (mul_eq_zero.mp h3) with
      | inl h6 =>
        left
        linarith
      | inr h7 =>
        right
        nlinarith [Real.sqrt_nonneg (5 / 2)]
    cases hy1 with
    | inl hy =>
      left
      exact ⟨hx, hy⟩
    | inr hy =>
      right
      exact ⟨hx, hy⟩
  · -- Conversely
    rintro (h | h)
    · -- Case where (x,y) = (0, Real.sqrt(5/2))
      rcases h with ⟨rfl, rfl⟩
      have h1 : Real.sqrt (5 / 2) ^ 2 = 5 / 2 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h2 : Real.sqrt (5 / 2) ^ 4 = (5 / 2) ^ 2 := by
        calc
          Real.sqrt (5 / 2) ^ 4 = (Real.sqrt (5 / 2) ^ 2) ^ 2 := by ring
          _ = (5 / 2) ^ 2 := by rw [h1]
      nlinarith [h1, h2]
    · -- Case where (x,y) = (0, -Real.sqrt(5/2))
      rcases h with ⟨rfl, rfl⟩
      have h1 : (-Real.sqrt (5 / 2)) ^ 2 = 5 / 2 := by
        have h2 : Real.sqrt (5 / 2) ^ 2 = 5 / 2 := Real.sq_sqrt (by norm_num)
        nlinarith [h2]
      have h2 : (-Real.sqrt (5 / 2)) ^ 4 = (5 / 2) ^ 2 := by
        calc
          (-Real.sqrt (5 / 2)) ^ 4 = ((-Real.sqrt (5 / 2)) ^ 2) ^ 2 := by ring
          _ = (5 / 2) ^ 2 := by rw [h1]
      nlinarith [h1, h2]