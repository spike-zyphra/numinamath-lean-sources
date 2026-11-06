import Mathlib

/- Given the quadratic function $f(x)=a{{x}^{2}}+bx+c$ satisfies $f(5-x)=f(5+x)$ and $a>0$, then the three function values $f(\sqrt{40}), f(2\pi), f(5\sin 45{}^\circ)$ in ascending order are ___          ___. -/
theorem algebra_10857 {a b c : ℝ} (ha : a > 0) (h : ∀ x, a * (5 - x) ^ 2 + b * (5 - x) + c = a * (5 + x) ^ 2 + b * (5 + x) + c)
    (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 2 + b * x + c) :
    f (2 * Real.pi) < f (Real.sqrt 40) ∧ f (Real.sqrt 40) < f (5 * Real.sin (Real.pi / 4)) := by

  have h_b : b = -10 * a := by
    have eq1 := h 0
    have eq2 := h 1
    ring_nf at eq1 eq2
    nlinarith
  have hf2 : ∀ x, f x = a * x^2 - 10 * a * x + c := by
    intro x
    rw [hf]
    simp [h_b]
    all_goals ring_nf
  have h1 : f (2 * Real.pi) < f (Real.sqrt 40) := by
    rw [hf2 (2 * Real.pi), hf2 (Real.sqrt 40)]
    have h4 : Real.sqrt 40 > 6 := by
      have h1 : Real.sqrt 40 > Real.sqrt 36 := by
        apply Real.sqrt_lt_sqrt
        all_goals norm_num
      have h2 : Real.sqrt 36 = 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    have h5 : 2 * Real.pi < Real.sqrt 40 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 40 by norm_num : (0 : ℝ) < 40), Real.sq_sqrt (show (0 : ℝ) ≤ 40 by norm_num : (0 : ℝ) ≤ 40), Real.pi_gt_31415, Real.pi_lt_31416, h4]
    have h6 : (5 - (2 * Real.pi))^2 < (5 - Real.sqrt 40)^2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 40 by norm_num : (0 : ℝ) < 40), Real.sq_sqrt (show (0 : ℝ) ≤ 40 by norm_num : (0 : ℝ) ≤ 40), Real.pi_gt_31415, Real.pi_lt_31416, h4, h5]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 40 by norm_num : (0 : ℝ) ≤ 40), Real.pi_gt_31415, Real.pi_lt_31416, Real.sqrt_pos.mpr (show (0 : ℝ) < 40 by norm_num : (0 : ℝ) < 40), Real.sqrt_nonneg 40, sq_nonneg (5 - (2 * Real.pi)), sq_nonneg (5 - Real.sqrt 40)]
  have h2 : f (Real.sqrt 40) < f (5 * Real.sin (Real.pi / 4)) := by
    rw [hf2 (Real.sqrt 40), hf2 (5 * Real.sin (Real.pi / 4))]
    have h7 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    rw [h7]
    have h8 : Real.sqrt 40 > 6 := by
      have h1 : Real.sqrt 40 > Real.sqrt 36 := by
        apply Real.sqrt_lt_sqrt
        all_goals norm_num
      have h2 : Real.sqrt 36 = 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    have h9 : (5 - Real.sqrt 40)^2 < (5 - 5 * (Real.sqrt 2 / 2))^2 := by
      have h10 : Real.sqrt 2 > 0 := by positivity
      have h11 : 5 * (Real.sqrt 2 / 2) > 0 := by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
      have h12 : 5 * (Real.sqrt 2 / 2) < 5 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have h13 : (5 - Real.sqrt 40)^2 < (5 - 5 * (Real.sqrt 2 / 2))^2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 40 by norm_num : (0 : ℝ) < 40), Real.sq_sqrt (show (0 : ℝ) ≤ 40 by norm_num : (0 : ℝ) ≤ 40), Real.sqrt_nonneg 40, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 40 by norm_num : (0 : ℝ) ≤ 40), Real.sqrt_nonneg 40, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), sq_nonneg (5 - Real.sqrt 40), sq_nonneg (5 - 5 * (Real.sqrt 2 / 2)), Real.sqrt_nonneg (40 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
  constructor
  · linarith [h1]
  · linarith [h2]