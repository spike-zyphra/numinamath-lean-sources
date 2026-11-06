import Mathlib

open Real Set
open scoped Real

theorem algebra_304011 (x y : ℝ) (h : sin x + sin y = 1 / 3) :
    sin y - cos x ^ 2 ≤ 4 / 9 ∧ ∃ x y, sin x + sin y = 1 / 3 ∧ sin y - cos x ^ 2 = 4 / 9 := by
  have h1 : sin x = 1 / 3 - sin y := by linarith
  have h2 : cos x ^ 2 = 1 - sin x ^ 2 := by
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    linarith
  have h3 : sin y - cos x ^ 2 = sin y ^ 2 + (1 / 3) * sin y - 8 / 9 := by
    rw [h2, h1]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, sq_nonneg (sin y - 1)]
  constructor
  · -- Show that $\sin y - \cos^2 x \leq 4/9$
    rw [h3]
    have h4 : -1 ≤ sin y ∧ sin y ≤ 1 := by
      constructor
      · linarith [Real.neg_one_le_sin y]
      · linarith [Real.sin_le_one y]
    nlinarith [sq_nonneg (sin y - 1)]
  · -- Show that there exists $y$ such that $\sin x + \sin y = 1/3$ and $\sin y - \cos x^2 = 4/9$
    use arcsin (-2 / 3), Real.pi / 2
    constructor
    · -- Show that $\sin x + \sin y = 1/3$
      have h5 : sin (Real.arcsin (-2 / 3 : ℝ)) = -2 / 3 := by
        apply Real.sin_arcsin
        all_goals norm_num
      have h6 : sin (Real.pi / 2 : ℝ) = 1 := Real.sin_pi_div_two
      linarith [h5, h6]
    · -- Show that $\sin y - \cos x ^ 2 = 4 / 9$
      have h5 : sin (Real.arcsin (-2 / 3 : ℝ)) = -2 / 3 := by
        apply Real.sin_arcsin
        all_goals norm_num
      have h6 : sin (Real.pi / 2 : ℝ) = 1 := Real.sin_pi_div_two
      have h7 : cos (Real.arcsin (-2 / 3 : ℝ)) ^ 2 = 1 - sin (Real.arcsin (-2 / 3 : ℝ)) ^ 2 := by
        have h10 : cos (Real.arcsin (-2 / 3 : ℝ)) ^ 2 + sin (Real.arcsin (-2 / 3 : ℝ)) ^ 2 = 1 := by
          exact Real.cos_sq_add_sin_sq (Real.arcsin (-2 / 3 : ℝ))
        linarith
      rw [show cos (Real.arcsin (-2 / 3 : ℝ)) ^ 2 = 1 - (-2 / 3) ^ 2 by
        rw [h7, h5]
        all_goals norm_num
      ]
      nlinarith [h5, h6, Real.sin_sq_add_cos_sq (Real.arcsin (-2 / 3 : ℝ)), Real.sin_sq_add_cos_sq (Real.pi / 2 : ℝ)]