import Mathlib

open Real Set
open scoped Real

/-- If $$
\sec \alpha \left( 1 + \tan^2 \alpha \right) + \tan \alpha \left( \csc^2 \alpha - 1 \right) = \tan^2 \alpha
$$
, determine the sign of the product $\sin(\cos \alpha) \cdot \cos(\sin \alpha)$.
-/
theorem Trigonometry_4175 (α : Real) (hsin : sin α ≠ 0) (hcos : cos α ≠ 0) (h : (cos α)⁻¹ * √(1 + (tan α) ^ 2) + tan α * √((sin α)⁻¹ ^ 2 - 1) = (tan α) ^ 2) : 0 < sin (cos α) * cos (sin α) := by
  -- First, $\tan^2 \alpha \neq 0$.
  have htan : tan α ≠ 0 := by simp [tan_eq_sin_div_cos, hsin, hcos]
  rw [← inv_inv (√_), ← sqrt_inv, inv_one_add_tan_sq hcos, sqrt_sq_eq_abs, inv_pow, ← tan_sq_div_one_add_tan_sq hcos, inv_div, add_div, div_self (by simp [htan]), add_sub_cancel_right, sqrt_div (zero_le_one), sqrt_one, sqrt_sq_eq_abs, mul_div, mul_one] at h
  nth_rw 1 [← sign_mul_abs ((cos α)⁻¹), ← sign_mul_abs (tan α)] at h
  rw [abs_inv, mul_div_cancel_right₀ _ (by simp [hcos, htan]), mul_assoc, ← pow_two] at h
  -- $0 < \cos \alpha$
  replace hcos : 0 < cos α := by
    cases hs : SignType.sign (cos α)⁻¹
    · simp [hcos] at hs
    · simp [hs] at h
      have : -(cos α ^ 2)⁻¹ ≤ -1 := by
        simp
        apply one_le_inv
        simp [sq_pos_iff, hcos]
        simp [abs_cos_le_one]
      have : 0 < tan α ^ 2 := by
        simp [sq_pos_iff, htan]
      have : (SignType.sign (tan α) : ℝ) ≤ 1 := by
        cases SignType.sign (tan α) <;> simp
      linarith
    · simpa [sign_eq_one_iff] using hs
  simp [hcos, ← inv_one_add_tan_sq hcos.ne'] at h
  rw [add_right_comm, add_left_eq_self, add_eq_zero_iff_neg_eq, eq_comm] at h
  have htan : tan α < 0 := by
    cases hs : SignType.sign (tan α)
    · simp [hs] at h
    · simpa [sign_eq_neg_one_iff] using hs
    · simp [hs] at h
      norm_num at h
  -- Because $0 < \cos \alpha$ and $\tan \alpha < 0$, $\sin \alpha < 0$
  have hsin : sin α < 0 := by
    rw [tan_eq_sin_div_cos, div_neg_iff] at htan
    simpa [hcos, hcos.le.not_lt] using htan
  -- Thus, $\sin \alpha \in \left[-1, 0 \right)$, $\cos \alpha \in \left(0, 1\right]$
  -- So we have $0 < \sin \left(\cos \alpha\right)$ and $0 < \cos \left(\sin \alpha\right)$
  have : 0 < sin (cos α) :=
    sin_pos_of_pos_of_lt_pi hcos (by linarith [cos_le_one α, show (1 : ℝ) < 3 by norm_num, pi_gt_three])
  have : 0 < cos (sin α) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_one_le_sin α, show (1 : ℝ) < 3 by norm_num, pi_gt_three], hsin.trans (by linarith [pi_pos])⟩
  positivity
