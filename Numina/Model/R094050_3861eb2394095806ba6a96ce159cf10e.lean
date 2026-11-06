import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_207032 {f : ℝ → ℝ}
  (hf : f = λ x => sin x * abs (cos x / sin x)) :
  ∀ x ∈ Ioo 0 Real.pi, f x = sqrt (1 - sin x ^ 2) := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h2 : abs (sin x) = sin x := by
    rw [abs_of_pos h1]
  have h3 : abs (cos x / sin x) = abs (cos x) / abs (sin x) := by
    field_simp [abs_div]
  have h5 : f x = abs (cos x) := by
    rw [hf]
    have h4 : abs (sin x) = sin x := h2
    have h6 : abs (cos x / sin x) = abs (cos x) / abs (sin x) := h3
    simp [h6, h4]
    <;> field_simp [h4]
    <;> ring_nf <;> norm_num
    all_goals linarith
  have h7 : sqrt (1 - sin x ^ 2) = abs (cos x) := by
    have h8 : 1 - sin x ^ 2 = (cos x) ^ 2 := by
      have h9 : sin x ^ 2 + cos x ^ 2 = 1 := by
        exact sin_sq_add_cos_sq x
      nlinarith
    rw [h8]
    rw [Real.sqrt_sq_eq_abs]
  linarith [h5, h7]