import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_318297 {f : ℝ → ℝ}
  (hf : f = λ x => sin x * abs (cos x / sin x)) :
  ∀ x ∈ Ioo 0 Real.pi, f x = sqrt (1 - sin x ^ 2) := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_gt_three, hx1, hx2]
    linarith [Real.pi_gt_three, hx1, hx2]
  have h2 : sin x ≠ 0 := by linarith
  have h3 : abs (cos x / sin x) = abs (cos x) / abs (sin x) := by
    field_simp [abs_div, h2]
    all_goals linarith
  have h4 : abs (sin x) = sin x := by
    rw [abs_of_pos]
    exact h1
  have h5 : abs (cos x / sin x) = abs (cos x) / sin x := by
    rw [h3]
    rw [h4]
    all_goals linarith
  have h6 : sin x * abs (cos x / sin x) = abs (cos x) := by
    rw [h5]
    field_simp [show sin x ≠ 0 by linarith]
    all_goals linarith
  have h7 : 1 - sin x ^ 2 = cos x ^ 2 := by
    have h8 : cos x ^ 2 + sin x ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq x
    nlinarith
  have h8 : sqrt (cos x ^ 2) = abs (cos x) := by
    rw [Real.sqrt_sq_eq_abs]
  calc
    f x = sin x * abs (cos x / sin x) := by rw [hf]
    _ = abs (cos x) := by rw [h6]
    _ = sqrt (cos x ^ 2) := by rw [h8]; all_goals nlinarith
    _ = sqrt (1 - sin x ^ 2) := by rw [h7]