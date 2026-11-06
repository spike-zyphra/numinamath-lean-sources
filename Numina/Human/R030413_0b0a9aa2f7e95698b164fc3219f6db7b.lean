import Mathlib

open Real Set
open scoped Real

/- 7. Let $x \in\left(0, \frac{\pi}{2}\right)$. Then the minimum value of the function $y=\frac{1}{\sin ^{2} x}+\frac{12 \sqrt{3}}{\cos x}$ is $\qquad$ -/
theorem algebra_181642 :
    IsLeast {y | ∃ x : ℝ, x ∈ Ioo 0 (π/2) ∧ y = 1/sin x ^ 2 + 12 * sqrt 3 / cos x} 28 := by
  constructor <;> simp
  -- use x = π/6 to show 28 is attiainable
  . use π / 6
    and_intros
    . linarith [pi_pos]
    . linarith [pi_pos]
    . rw [sin_pi_div_six, cos_pi_div_six]
      ring_nf
      simp
      ring
  -- to prove 28 is an upper bound consider such an x
  . rintro y ⟨x, ⟨hx_lb, hx_ub⟩, hy⟩
    calc
      -- first show 28 as following expression, 1/2 and 9/4 will be used in inequalitesi
      _ = (16:ℝ) * (1/2) + 16 * (9/4) - 16 := by ring
      -- prove 1 / 2 ≤ 16 * sin x ^ 2 + sin x ^ 2 using am-gm of 2 variables
      _ ≤ 16 * (1 / (16 * sin x ^ 2) + sin x ^ 2) + 16 * (9/4) - 16 := by
        gcongr
        rw [show 1 / 2 = (2 : ℝ) * (1 / 4) by norm_num]
        apply two_mul_le_add_of_sq_eq_mul
        . positivity
        . positivity
          -- sin x is positivite is needed here
        . have : 0 < sin x := sin_pos_of_pos_of_lt_pi hx_lb (by linarith)
          field_simp
          ring
      -- next show 9/4 ≤ ((3 * √3 / (8 * cos x)) + (3 * √3 / (8 * cos x)) + cos x ^ 2) using 3 variable am-gm
      _ ≤ 16 * (1 / (16 * sin x ^ 2) + sin x ^ 2) + 16 * ((3 * √3 / (8 * cos x)) + (3 * √3 / (8 * cos x)) + cos x ^ 2) - 16 := by
        gcongr
        have : 0 < cos x := by
          refine cos_pos_of_mem_Ioo ?_
          simp
          and_intros <;> linarith
        have : (0 : ℝ) ≤ 1 / 3 := by norm_num
        have ineq := geom_mean_le_arith_mean3_weighted this this this
            (show 0 ≤ 3 * √3 / (8 * cos x) by positivity) (show 0 ≤ 3 * √3 / (8 * cos x) by positivity)
            (show 0 ≤ cos x ^ 2 by positivity) (by norm_num)
        repeat rw [← mul_rpow (by positivity) (by positivity)] at ineq
        ring_nf at ineq
        field_simp at ineq
        rw [show 3 * 9 / 64 = (3 / 4 : ℝ) ^ 3 by norm_num, ← rpow_natCast, ← rpow_mul (by norm_num)] at ineq
        simp at ineq
        ring_nf at ineq ⊢
        rw [show cos x ^ 3 * (cos x)⁻¹  = cos x ^ 2 by field_simp; ring] at ineq
        linear_combination 3 * ineq
      -- finally simplify, sin x^2 + cos x^2 will be truned to 1 and we're done
      _ = (sin x ^ 2)⁻¹ + 12 * √3 / cos x + 16 * (sin x ^2 + cos x^2 -1) := by ring
      _ = y := by
        rw [hy, sin_sq_add_cos_sq]
        ring