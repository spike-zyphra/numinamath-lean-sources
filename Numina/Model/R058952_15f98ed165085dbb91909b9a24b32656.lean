import Mathlib

open Real Set

theorem algebra_3297 {x : ℝ} (hx : x ∈ Ioo 0 (π / 2)) (h : tan x = 2) :
    (12 * sin x + 11 * cos x) / (8 * sin x + 5 * cos x) = 1 + 2 / 3 := by
  have h1 : 0 < x := hx.1
  have h2 : x < π / 2 := hx.2
  have h3 : cos x ≠ 0 := by
    by_contra h4
    have htan : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h4]
    rw [htan] at h
    norm_num at h
  -- Since $0^\circ < x < 90^\circ$, both $\sin x > 0$ and $\cos x > 0$.
  have h4 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h5 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h1, Real.pi_pos]
    · linarith [h2, Real.pi_pos]
  -- From $\tan x = 2$, we have $\sin x = 2 \cos x$.
  have h6 : sin x = 2 * cos x := by
    have htan : tan x = sin x / cos x := by
      rw [tan_eq_sin_div_cos]
    rw [htan] at h
    field_simp [h3] at h
    linarith
  -- Using Pythagorean identity $\sin^2 x + \cos^2 x = 1$, we can solve for $\cos x$ and $\sin x$.
  have h8 : cos x = Real.sqrt (1 / 5) := by
    have h9 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    rw [h6] at h9
    have h10 : 5 * cos x ^ 2 = 1 := by
      nlinarith
    have h11 : cos x > 0 := h5
    have h13 : cos x ^ 2 = 1 / 5 := by linarith
    have h14 : cos x = Real.sqrt (1 / 5) := by
      have hsq : cos x ^ 2 = 1 / 5 := by linarith
      have h15 : cos x > 0 := h11
      have h16 : cos x = Real.sqrt (cos x ^ 2) := by
        rw [Real.sqrt_sq (show 0 ≤ (cos x:ℝ) by linarith)]
      rw [h16]
      rw [hsq]
    exact h14
  -- $\sin x = 2 \cos x = 2 \cdot \sqrt{1/5}$
  have h9 : sin x = 2 * Real.sqrt (1 / 5) := by 
    rw [h6, h8]
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (1 / 5 : ℝ) by norm_num : (0 : ℝ) < (1 / 5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 5 : ℝ) by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))]
  -- Compute numerator: $12\sin x + 11\cos x = 35\sqrt{1/5}$
  have num_eq : 12 * sin x + 11 * cos x = 35 * Real.sqrt (1 / 5) := by
    rw [h9, h8]
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (1 / 5 : ℝ) by norm_num : (0 : ℝ) < (1 / 5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 5 : ℝ) by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))]
  -- Compute denominator: $8\sin x + 5\cos x = 21\sqrt{1/5}$
  have denom_eq : 8 * sin x + 5 * cos x = 21 * Real.sqrt (1 / 5) := by
    rw [h9, h8]
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (1 / 5 : ℝ) by norm_num : (0 : ℝ) < (1 / 5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 5 : ℝ) by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))]
  have denom_ne_zero : 8 * sin x + 5 * cos x ≠ 0 := by
    nlinarith [h4, h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (1 / 5 : ℝ) by norm_num : (0 : ℝ) < (1 / 5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 5 : ℝ) by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))]
  rw [num_eq, denom_eq]
  field_simp [denom_ne_zero, Real.sqrt_pos.mpr (show (0 : ℝ) < (1 / 5 : ℝ) by norm_num : (0 : ℝ) < (1 / 5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 5 : ℝ) by norm_num : (0 : ℝ) ≤ (1 / 5 : ℝ))]
  <;> nlinarith