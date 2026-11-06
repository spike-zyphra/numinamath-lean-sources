import Mathlib

theorem algebra_9041 {a : ℝ} (ha : a ≠ 0) :
  {x | x^2 - (2 + a) * x + 2 * a > 0} = {x | x > (max a 2) ∨ x < (min a 2)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume the quadratic expression is greater than zero
    intro h
    have h1 : x ^ 2 - (2 + a) * x + 2 * a = (x - 2) * (x - a) := by
      nlinarith
    have h2 : (x - 2) * (x - a) > 0 := by
      linarith [h1, h]
    have h3 : (x - 2) > 0 ∧ (x - a) > 0 ∨ (x - 2) < 0 ∧ (x - a) < 0 := by
      apply mul_pos_iff.mp at h2
      tauto
    rcases h3 with h3 | h3
    · -- Both factors are positive; so $x > 2 \land x > a$
      left
      cases max_cases a 2 with
      | inl hmax =>
        linarith
      | inr hmax =>
        linarith
    · -- Both factors are negative; so $x < 2 \land x < a$
      right
      cases min_cases a 2 with
      | inl hmin =>
        linarith
      | inr hmin =>
        linarith
  · -- Assume the equivalent condition holds, prove the inequality.
    intro h
    have h1 : x ^ 2 - (2 + a) * x + 2 * a = (x - 2) * (x - a) := by
      nlinarith
    rw [h1]
    rcases h with h | h
    · -- Case where $x > \max(a, 2)$
      cases max_cases a 2 with
      | inl hmax =>
        have h4 : x > (a : ℝ) := by linarith
        have h5 : x > (2 : ℝ) := by nlinarith
        nlinarith
      | inr hmax =>
        have h6 : x > (2 : ℝ) := by linarith
        have h7 : x > (a : ℝ) := by nlinarith
        nlinarith
    · -- Case where $x < \min(a, 2)$
      cases min_cases a 2 with
      | inl hmin =>
        have h8 : x < (a : ℝ) := by linarith
        have h9 : x < (2 : ℝ) := by nlinarith
        nlinarith
      | inr hmin =>
        have h10 : x < (2 : ℝ) := by linarith
        have h11 : x < (a : ℝ) := by nlinarith
        nlinarith