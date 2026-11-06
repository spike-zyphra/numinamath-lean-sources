import Mathlib

theorem algebra_226267 {P : ℝ → ℝ} (hP : P = fun t => t^4 - t + 1 / 2) :
    ∀ t, P t ≠ 0 ∧ P t > 0 := by
  intro t
  have h1 : P t = t^4 - t + 1 / 2 := by
    rw [hP]
  have h2 : P t ≠ 0 := by
    rw [h1]
    by_contra h
    have h3 : t^4 - t + 1 / 2 = 0 := by linarith
    nlinarith [sq_nonneg (t^2 - 1 / 2), sq_nonneg (t^2 - t), sq_nonneg (t^2 + t), sq_nonneg (t - 1), sq_nonneg (t), sq_nonneg (t - 1 / 2), sq_nonneg (t - (1 / 2)^(1 / 3)), sq_nonneg (t - (1 / 4)^(1 / 3)), sq_nonneg (t + (1 / 4)^(1 / 3))]
  have h3 : P t > 0 := by
    rw [h1]
    nlinarith [sq_nonneg (t^2 - 1 / 2), sq_nonneg (t^2 - t), sq_nonneg (t^2 + t), sq_nonneg (t - 1), sq_nonneg (t), sq_nonneg (t - 1 / 2), sq_nonneg (t - (1 / 2)^(1 / 3)), sq_nonneg (t - (1 / 4)^(1 / 3)), sq_nonneg (t + (1 / 4)^(1 / 3))]
  exact ⟨h2, h3⟩