import Mathlib

theorem algebra_324938 (θ : ℝ) (hθ : θ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) (h : Real.sin θ + Real.cos θ = 1 / 3) :
    θ = -Real.arcsin ((Real.sqrt 17 - 1) / 6) := by
  have h1 : -Real.pi / 2 < θ := hθ.left
  have h2 : θ < Real.pi / 2 := hθ.right
  have h3 : Real.cos θ > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [h1]
    · linarith [h2]
  have h4 : Real.sin θ = (1 / 3) - Real.cos θ := by linarith
  have h5 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h6 : Real.sin θ ^ 2 = ((1 / 3) - Real.cos θ) ^ 2 := by
    rw [h4]
  rw [h6] at h5
  -- cos θ satisfies the equation x ^ 2 - 1/3 x - 4 / 9 = 0
  have h7 : ((1 / 3 : ℝ) - Real.cos θ) ^ 2 + Real.cos θ ^ 2 = 1 := by
    linarith
  -- decompose the above equation to get a formula for cos θ. this leads to two cases to be dissussed.
  have h8 : (Real.cos θ - (1 + Real.sqrt 17) / 6) * (Real.cos θ - (1 - Real.sqrt 17) / 6) = 0 := by
    have h_eq : ((1 / 3 : ℝ) - Real.cos θ) ^ 2 + Real.cos θ ^ 2 = 1 := h7
    ring_nf at h_eq
    nlinarith [Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), mul_self_nonneg (Real.cos θ), mul_self_nonneg (Real.cos θ - 1 / 3)]
  cases' (mul_eq_zero.mp h8) with h_cos_add h_cos_sub
  · -- Case $\cos \theta = \frac{1 + \sqrt{17}}{6}$
    have h_cos : Real.cos θ = (1 + Real.sqrt 17) / 6 := by linarith
    have h_sin : Real.sin θ = (1 - Real.sqrt 17) / 6 := by
      have h9 : Real.sin θ = (1 / 3) - Real.cos θ := h4
      rw [h9, h_cos]
      ring
    have h10 : Real.arcsin ((Real.sqrt 17 - 1) / 6) = -θ := by
      have h11 : Real.sin (-θ) = (Real.sqrt 17 - 1) / 6 := by
        rw [show Real.sin (-θ) = -Real.sin θ by rw [Real.sin_neg]]
        linarith [h_sin]
      have h12 : -Real.pi / 2 ≤ -θ := by linarith [h2]
      have h13 : -θ ≤ Real.pi / 2 := by linarith [h1]
      have h14 : Real.arcsin ((Real.sqrt 17 - 1) / 6) = -θ := by
        have h15 : Real.sin (-θ) = (Real.sqrt 17 - 1) / 6 := h11
        have h16 : -Real.pi / 2 ≤ -θ := h12
        have h17 : -θ ≤ Real.pi / 2 := h13
        rw [←h15]
        apply Real.arcsin_sin
        all_goals linarith
      exact h14
    linarith [h10]
  · -- Case $\cos \theta = \frac{1 - \sqrt{17}}{6}$, but it's negative
    have h_cos : Real.cos θ = (1 - Real.sqrt 17) / 6 := by linarith
    have h14 : Real.cos θ < 0 := by
      have h15 : Real.sqrt 17 > 4 := by
        have h16 : Real.sqrt 17 > Real.sqrt 16 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have h17 : Real.sqrt 16 = 4 := Real.sqrt_eq_cases.mpr (by norm_num)
        linarith
      nlinarith [h_cos, Real.sqrt_pos.mpr (show (0:ℝ) < 17 by norm_num : (17 : ℝ) > 0)]
    linarith [h3, h14]