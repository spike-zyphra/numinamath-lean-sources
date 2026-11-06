import Mathlib

theorem algebra_249420 (a : ℝ) :
    (∀ x : ℝ, (x < 1 ∨ x > 5) → x^2 - 2 * (a - 2) * x + a > 0) ↔
    1 < a ∧ a ≤ 5 := by
  constructor
  · -- Assume the quadratic is positive for x < 1 or x > 5, prove 1 < a ∧ a ≤ 5
    intro h
    have h1 : a ≤ 5 := by
      by_contra h2
      push_neg at h2
      have h2' : a > 5 := by linarith
      have h3 := h (a) (Or.inr (by linarith))
      nlinarith [sq_nonneg (a - 5)]
    have h2 : 1 < a := by
      by_contra h3
      push_neg at h3
      have h4 := h (-1) (Or.inl (by norm_num))
      nlinarith
    constructor
    · exact h2
    · exact h1
  · -- Assume 1 < a ∧ a ≤ 5, prove the quadratic is positive for x < 1 or x > 5
    rintro ⟨ha1, ha2⟩
    intro x h
    rcases h with (h | h)
    · -- Case x < 1
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 5), sq_nonneg (x - (a - 2)), sq_nonneg (a - 4), sq_nonneg (a - 1), sq_nonneg (a - 5)]
    · -- Case x > 5
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 5), sq_nonneg (x - (a - 2)), sq_nonneg (a - 4), sq_nonneg (a - 1), sq_nonneg (a - 5)]