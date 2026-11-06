import Mathlib

open Real Set
open scoped Real

/- Given that $x$ is an acute angle, the minimum value of $\frac{8}{\sin x}+\frac{1}{\cos x}$ is ___          ___. -/
theorem inequalities_8515 (x : Real) (hx : x ∈ Ioo 0 (π / 2)) :
  8 / sin x + 1 / cos x ≥ 5 * sqrt 5 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h4 : 8 / sin x + 1 / cos x - 5 * sqrt 5 ≥ 0 := by
    have h5 : 0 < sin x * cos x := by
      positivity
    have h6 : 8 * cos x + sin x - 5 * sqrt 5 * (sin x * cos x) ≥ 0 := by
      nlinarith [sq_nonneg (sin x - 2 / Real.sqrt 5), sq_nonneg (cos x - 1 / Real.sqrt 5),
        Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
        sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x - 2 * cos x),
        h1, h2, mul_pos h1 h2, Real.sqrt_nonneg 5, sq_nonneg (sin x * cos x - 2 / 5)]
    have h7 : (8 / sin x + 1 / cos x - 5 * sqrt 5) = (8 * cos x + sin x - 5 * sqrt 5 * (sin x * cos x)) / (sin x * cos x) := by
      field_simp [h1, h2]
      <;> ring
    rw [h7] at *
    apply div_nonneg
    linarith
    positivity
  linarith