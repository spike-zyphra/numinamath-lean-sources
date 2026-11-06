import Mathlib

theorem algebra_251941 (x : ℝ) :
    Real.sqrt (1 + 3 * x) = 1 - x ↔ x = 0 := by
  constructor
  · -- Forward: If sqrt(1 + 3x) = 1 - x, then x = 0
    intro h
    have h1 : Real.sqrt (1 + 3 * x) = 1 - x := by linarith
    have h2 : 0 ≤ (1 + 3 * x) := by
      by_contra h2
      push_neg at h2
      have h3 : Real.sqrt (1 + 3 * x) = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals nlinarith
      rw [h3] at h1
      nlinarith
    have h3 : 0 ≤ (1 - x : ℝ) := by
      nlinarith [Real.sqrt_nonneg (1 + 3 * x), h1]
    have eq1 : (Real.sqrt (1 + 3 * x)) ^ 2 = (1 - x) ^ 2 := by
      rw [h1]
      all_goals nlinarith
    have h4 : (Real.sqrt (1 + 3 * x)) ^ 2 = 1 + 3 * x := by
      rw [Real.sq_sqrt]
      linarith
    have eq2 : 1 + 3 * x = (1 - x) ^ 2 := by
      nlinarith [h4, eq1]
    have eq5 : 1 + 3 * x = 1 - 2 * x + x ^ 2 := by
      nlinarith [eq2]
    have eq6 : x ^ 2 - 5 * x = 0 := by
      nlinarith [eq5]
    have eq7 : x * (x - 5) = 0 := by
      nlinarith [eq6]
    cases (mul_eq_zero.mp eq7) with
    | inl h10 =>
      linarith
    | inr h11 =>
      nlinarith [h11, h3]
  · -- Backward: If x = 0, then sqrt(1 + 3x) = 1 - x
    intro h
    rw [h]
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq, sq]