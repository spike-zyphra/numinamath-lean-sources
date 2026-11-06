import Mathlib

theorem algebra_291077 :
  {a : ℝ | ∃ x y : ℝ, x + y^2 = a ∧ y + x^2 = a} = {a : ℝ | a ≥ -1 / 4} := by
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume there exist real numbers x, y such that both equations hold
    intro h
    rcases h with ⟨x, y, h1, h2⟩
    have eq1 : x + y^2 = y + x^2 := by linarith
    have eq2 : (x - y) * (1 - (x + y)) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq2) with h3 h4
    · -- Case where x = y
      have hxy : x = y := by linarith
      have eq3 : y = x := by linarith [hxy]
      rw [eq3] at h1 h2
      have h3 : x ^ 2 + x - a = 0 := by nlinarith
      have h4 : (x + 1 / 2) ^ 2 ≥ 0 := by apply sq_nonneg
      nlinarith
    · -- Case where x + y = 1
      have h5 : x + y = 1 := by linarith
      have eq4 : y = 1 - x := by linarith
      rw [eq4] at h1 h2
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1 / 2)]
  · -- Assume a >= -1/4, prove there exists a real solution.
    intro ha
    by_cases h : a ≥ 3 / 4
    · -- If a >= 3/4, use solution from Case 2.
      use (1 + Real.sqrt (4 * a - 3)) / 2, (1 - Real.sqrt (4 * a - 3)) / 2
      constructor
      · -- Show that x + y^2 = a
        nlinarith [Real.sqrt_nonneg (4 * a - 3), Real.sq_sqrt (show (4 * a - 3) ≥ 0 by linarith)]
      · -- Show that y + x^2 = a
        nlinarith [Real.sqrt_nonneg (4 * a - 3), Real.sq_sqrt (show (4 * a - 3) ≥ 0 by linarith)]
    · -- If a < 3/4, use solution from Case 1.
      have ha' : a ≥ -1 / 4 := by linarith
      use (-1 + Real.sqrt (1 + 4 * a)) / 2, (-1 + Real.sqrt (1 + 4 * a)) / 2
      constructor
      · -- Show that x + y^2 = a
        nlinarith [Real.sqrt_nonneg (1 + 4 * a), Real.sq_sqrt (show (1 + 4 * a) ≥ 0 by linarith)]
      · -- Show that y + x^2 = a
        nlinarith [Real.sqrt_nonneg (1 + 4 * a), Real.sq_sqrt (show (1 + 4 * a) ≥ 0 by linarith)]