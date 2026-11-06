import Mathlib

theorem algebra_9117 {f : ℝ → ℝ} (hf : f = λ x => x + Real.sin x) :
    (∀ x, f (-x) = -f x) ∧ Monotone f := by
  constructor
  · -- Show that $f$ is odd
    intro x
    rw [hf]
    simp [Real.sin_neg]
    <;> ring
  · -- Show that $f$ is monotone
    apply monotone_of_deriv_nonneg
    all_goals
      -- Show f is differentiable and derivative is non-negative
      intro x
      rw [hf]
      simp [deriv_add, deriv_id'', Real.deriv_sin]
      all_goals
        -- Show the derivative is positive. Since $1 + \cos x ≥ 0.
        have h_nonneg : 0 ≤ 1 + Real.cos x := by
          linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
        linarith