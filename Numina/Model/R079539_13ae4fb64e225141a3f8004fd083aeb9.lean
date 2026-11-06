import Mathlib

open Real Set

theorem inequalities_292196 (a : ℝ) :
    (∀ x : ℝ, a * (4 - sin x) ^ 4 - 3 + (cos x) ^ 2 + a > 0) ↔
    a > 3 / 82 := by
  constructor
  · -- (→) direction: If the inequality holds for all x, then a > 3/82
    intro h
    have h1 := h (Real.pi / 2)
    have h2 : sin (Real.pi / 2) = 1 := by
      exact sin_pi_div_two
    have h3 : cos (Real.pi / 2) = 0 := by
      have h4 : cos (Real.pi / 2) = 0 := by
        exact cos_pi_div_two
      exact h4
    rw [h2, h3] at h1
    linarith
  · -- (←) direction: If a > 3/82, then the inequality holds for all x
    intro ha x
    have h1 : -1 ≤ sin x ∧ sin x ≤ 1 := by
      have h2 : -1 ≤ sin x := by linarith [Real.neg_one_le_sin x, Real.sin_le_one x]
      have h3 : sin x ≤ 1 := by linarith [Real.sin_le_one x]
      exact ⟨h2, h3⟩
    have hsin1 : -1 ≤ sin x := h1.1
    have hsin2 : sin x ≤ 1 := h1.2
    have hcos1 : (cos x)^2 = 1 - (sin x)^2 := by
      nlinarith [Real.cos_sq_add_sin_sq x]
    have h4 : a * (4 - sin x) ^ 4 - 3 + (cos x)^2 + a > 0 := by
      rw [hcos1]
      nlinarith [sq_nonneg ((4 - sin x)^2), sq_nonneg (sin x - 1), sq_nonneg (sin x + 1),
        sq_nonneg (a - 3 / 82), Real.sin_sq_add_cos_sq x,
        hsin1, hsin2, Real.sin_sq_add_cos_sq x, sq_nonneg (sin x), sq_nonneg (a),
        mul_nonneg (show (0 : ℝ) ≤ a - 3 / 82 by linarith) (show (0 : ℝ) ≤ (4 - sin x)^4 by positivity),
        sq_nonneg (a * (4 - sin x)^4), sq_nonneg ((4 - sin x)^2 - 9), sq_nonneg (sin x)]
    linarith