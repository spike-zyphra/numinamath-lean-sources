import Mathlib

theorem algebra_12297 (a : ℝ) :
    (∀ x : ℝ, (x < 1 ∨ x > 5) → x^2 - 2 * (a - 2) * x + a > 0) ↔
    1 < a ∧ a ≤ 5 := by
  constructor
  · -- Forward direction:
    intro h
    have h1 : a > 1 := by 
      have h2 := h (-1) (Or.inl (by norm_num))
      nlinarith 
    have h2 : a ≤ 5 := by 
      by_contra h3 
      push_neg at h3 
      -- Assume a > 5 and derive a contradiction
      have h4 := h a (Or.inr (by linarith))
      have h5 : -a^2 + 5 * a > 0 := by 
        nlinarith 
      -- We have (a > 5) and (-a^2 + 5*a > 0)
      nlinarith 
    exact ⟨h1, h2⟩ 
  · -- Backward direction: 
    rintro ⟨ha1, ha2⟩ 
    intro x h 
    rcases h with h | h 
    · -- Case x < 1 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 5), sq_nonneg (x - (a - 2)), sq_nonneg (a - 1), sq_nonneg (5 - a)]
    · -- Case x > 5 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 5), sq_nonneg (x - (a - 2)), sq_nonneg (a - 1), sq_nonneg (5 - a)]