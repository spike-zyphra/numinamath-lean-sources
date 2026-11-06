import Mathlib

theorem algebra_144020 {f : ℝ → ℝ} (hf : f = fun x => (1/4) * (x + 1) * (x - 1)^2 * (x - 4)) :
    ∀ x, f x < 0 ↔ x ∈ Set.Ioo (-1) 1 ∪ Set.Ioo 1 4 := by
  intro x
  simp [hf]
  constructor
  · -- Assume f(x) < 0, need to prove x ∈ (-1, 1) ∪ (1, 4)
    intro h
    have h2 : (x + 1) * (x - 4) < 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x - 4), show (x - 1) ^ 2 ≥ 0 by positivity]
    have h3 : -1 < x := by nlinarith
    have h4 : x < 4 := by nlinarith
    by_cases h5 : x < 1
    · -- x < 1, so x ∈ (-1, 1)
      left
      exact ⟨h3, h5⟩
    · -- x ≥ 1
      have h6 : x > 1 := by
        by_contra h7
        push_neg at h7
        have h8 : x = 1 := by linarith
        rw [h8] at h2
        nlinarith
      right
      exact ⟨h6, h4⟩
  · -- Assume x ∈ (-1, 1) ∪ (1, 4), need to prove f(x) < 0
    rintro (h | h)
    · -- x ∈ (-1, 1)
      rcases h with ⟨h1, h2⟩
      have h3 : x + 1 > 0 := by linarith
      have h4 : x - 4 < 0 := by linarith
      have h5 : (x - 1) ^ 2 > 0 := by
        nlinarith
      nlinarith [show (x + 1) * (x - 4) < 0 by nlinarith, h5, sq_nonneg (x + 1), sq_nonneg (x - 4)]
    · -- x ∈ (1, 4)
      rcases h with ⟨h1, h2⟩
      have h3 : x + 1 > 0 := by linarith
      have h4 : x - 4 < 0 := by linarith
      have h5 : (x - 1) ^ 2 > 0 := by
        nlinarith
      nlinarith [show (x + 1) * (x - 4) < 0 by nlinarith, h5, sq_nonneg (x + 1), sq_nonneg (x - 4)]