import Mathlib

open intervalIntegral Real

theorem calculus_141957 : ∫ x in (0)..(π / 2), (cos x - sin x) / (1 + sin x) ^ 2 = 1 / 6 := by
  have aux : ∀ a ∈ Set.uIcc 0 (π / 2), ¬tan (a / 2) + 1 = 0 := by
    intro x hx; rcases hx with ⟨xge, xle⟩
    rw [min_eq_left] at xge; rw [max_eq_right] at xle
    have : 0 ≤ sin (x / 2) := by
      apply sin_nonneg_of_nonneg_of_le_pi
      linarith only [xge]; linarith only [xle, pi_pos]
    have : 0 < cos (x / 2) := by
      apply cos_pos_of_mem_Ioo; simp; constructor
      linarith only [xge, pi_pos]
      linarith only [xle, pi_pos]
    have : 0 ≤ tan (x / 2) := by
      rw [tan_eq_sin_div_cos]; positivity
    all_goals positivity
  simp_rw [← div_sub_div_same]; rw [integral_sub]
  have int1 : (∫ (x : ℝ) in (0)..π / 2, cos x / (1 + sin x) ^ 2) = 1 / 2 := by
    have : Set.EqOn (fun x => cos x / (1 + sin x) ^ 2) ((fun x =>
    ((fun t => 1 / t ^ 2) ∘ (fun s => 1 + sin s)) x * cos x)) (Set.uIcc 0 (π / 2)) := by
      intro x hx; simp; ring
    rw [integral_congr this, integral_comp_mul_deriv']
    · simp; norm_num [← one_div]
      replace this : Set.EqOn (fun x : ℝ => 1 / x ^ 2) (fun x =>
      deriv (fun x => -1/ x) x) (Set.uIcc 1 2) := by
        intro x hx; simp at hx; rcases hx with ⟨hx⟩
        simp; rw [deriv_div]; any_goals simp
        linarith only [hx]
      rw [integral_congr this, integral_deriv_eq_sub]; norm_num
      simp; intros; apply DifferentiableAt.div; any_goals simp
      linarith; apply ContinuousOn.intervalIntegrable
      rw [Set.eqOn_comm] at this; rw [continuousOn_congr this]
      apply ContinuousOn.div; any_goals apply Continuous.continuousOn
      exact continuous_const; exact continuous_pow 2
      simp; intros; linarith
    · intro x _; rw [show cos x = deriv (fun t => 1 + sin t) x by simp]
      apply DifferentiableAt.hasDerivAt; simp
    · apply Continuous.continuousOn; exact continuous_cos
    apply ContinuousOn.div; any_goals apply Continuous.continuousOn
    exact continuous_const; exact continuous_pow 2
    simp; intro x hx; rcases hx with ⟨xge, xle⟩
    rw [min_eq_left] at xge; rw [max_eq_right] at xle
    have : 0 ≤ sin x := by
      apply sin_nonneg_of_nonneg_of_le_pi
      exact xge; linarith only [xle, pi_pos]
    all_goals positivity
  have : Set.EqOn (fun x => sin x / (1 + sin x) ^ 2) (fun x =>
  2 * tan (x / 2) * (tan (x / 2) ^ 2 + 1) / (tan (x / 2) + 1) ^ 4) (Set.uIcc 0 (π / 2)) := by
    intro x hx; simp; rcases hx with ⟨xge, xle⟩
    rw [min_eq_left] at xge; rw [max_eq_right] at xle
    have : 0 ≤ sin (x / 2) := by
      apply sin_nonneg_of_nonneg_of_le_pi
      linarith only [xge]; linarith only [xle, pi_pos]
    have : 0 < cos (x / 2) := by
      apply cos_pos_of_mem_Ioo; simp; constructor
      linarith only [xge, pi_pos]
      linarith only [xle, pi_pos]
    have : 0 ≤ tan (x / 2) := by
      rw [tan_eq_sin_div_cos]; positivity
    nth_rw 1 2 [show x = 2*(x/2) by ring]; rw [sin_two_mul]
    rw [div_eq_div_iff, tan_eq_sin_div_cos]
    field_simp; rw [← sin_sq_add_cos_sq (x / 2)]
    rw [show sin (x / 2) ^ 2 + cos (x / 2) ^ 2 + 2 * sin (x / 2) * cos (x / 2) =
    (sin (x / 2) + cos (x / 2)) ^ 2 by ring]; ring
    · simp; positivity
    · positivity
    all_goals linarith only [pi_pos]
  suffices : ∫ (x : ℝ) in (0)..π / 2, sin x / (1 + sin x) ^ 2 = 1 / 3
  · norm_num [int1, this]
  rw [integral_congr this]
  replace this : Set.EqOn (fun x => 2 * tan (x / 2) * (tan (x / 2) ^ 2 + 1) /
  (tan (x / 2) + 1) ^ 4) (fun x => ((fun u : ℝ => 4 / u ^ 3 - 4 / u ^ 4) ∘
  (fun v => tan (v / 2) + 1)) x * ((tan (x / 2) ^ 2 + 1) / 2)) (Set.uIcc 0 (π / 2)) := by
    intro x hx; simp; rcases hx with ⟨xge, xle⟩
    rw [min_eq_left] at xge; rw [max_eq_right] at xle
    have : 0 ≤ sin (x / 2) := by
      apply sin_nonneg_of_nonneg_of_le_pi
      linarith only [xge]; linarith only [xle, pi_pos]
    have : 0 < cos (x / 2) := by
      apply cos_pos_of_mem_Ioo; simp; constructor
      linarith only [xge, pi_pos]
      linarith only [xle, pi_pos]
    have : 0 ≤ tan (x / 2) := by
      rw [tan_eq_sin_div_cos]; positivity
    field_simp; ring; all_goals positivity
  rw [integral_congr this, integral_comp_mul_deriv', div_div]
  norm_num; rw [integral_sub]
  replace this : Set.EqOn (fun x => 4 / x ^ 3) (fun x : ℝ => deriv (fun t =>
  -2 / t ^ 2) x) (Set.uIcc 1 2) := by
    intro x hx; simp at hx; rcases hx with ⟨xge, xle⟩
    simp; rw [deriv_div]; simp; field_simp; ring
    any_goals simp
    linarith only [xge]
  rw [integral_congr this, integral_deriv_eq_sub]
  have this' : Set.EqOn (fun x => 4 / x ^ 4) (fun x : ℝ => deriv (fun t =>
   -4 / (3 * t ^ 3)) x) (Set.uIcc 1 2) := by
    intro x hx; simp at hx; rcases hx with ⟨xge, xle⟩
    simp; rw [deriv_div]; simp; field_simp; ring
    any_goals simp
    linarith only [xge]
  rw [integral_congr this', integral_deriv_eq_sub]; norm_num
  · intro x hx; simp at hx
    apply DifferentiableAt.div; any_goals simp
    linarith only [hx.left]
  · apply ContinuousOn.intervalIntegrable
    rw [Set.eqOn_comm] at this'; rw [continuousOn_congr this']
    apply ContinuousOn.div; exact continuousOn_const
    exact continuousOn_pow 4
    intro x hx; simp at hx; simp
    linarith only [hx.left]
  · intro x hx; simp at hx
    apply DifferentiableAt.div; any_goals simp
    linarith only [hx.left]
  · apply ContinuousOn.intervalIntegrable
    rw [Set.eqOn_comm] at this; rw [continuousOn_congr this]
    apply ContinuousOn.div; exact continuousOn_const
    exact continuousOn_pow 3
    intro x hx; simp at hx; simp
    linarith only [hx.left]
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div; exact continuousOn_const
    exact continuousOn_pow 3
    intro x hx; simp at hx; simp
    linarith only [hx.left]
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div; exact continuousOn_const
    exact continuousOn_pow 4
    intro x hx; simp at hx; simp
    linarith only [hx.left]
  · intro x hx; rcases hx with ⟨xge, xle⟩
    rw [min_eq_left] at xge; rw [max_eq_right] at xle
    have h : 0 < cos (x / 2) := by
      apply cos_pos_of_mem_Ioo; simp
      constructor; linarith only [xge, pi_pos]
      linarith only [xle, pi_pos]
    have : deriv (fun v => tan (v / 2) + 1) x = (tan (x / 2) ^ 2 + 1) / 2 := by
      rw [deriv_add_const, show (fun v => tan (v / 2)) = (fun v => ((fun v => tan v) ∘ (fun t => t / 2)) v) by simp]
      rw [deriv_comp, deriv_tan]; simp; rw [tan_eq_sin_div_cos]
      field_simp; rw [differentiableAt_tan]; linarith only [h]
      simp
    rw [← this]; apply DifferentiableAt.hasDerivAt
    apply DifferentiableAt.add; apply DifferentiableAt.comp'
    rw [differentiableAt_tan]; linarith only [h]
    any_goals simp
    all_goals positivity
  · apply ContinuousOn.div_const; apply  ContinuousOn.add
    apply ContinuousOn.pow; intro x hx
    rcases hx with ⟨xge, xle⟩
    rw [min_eq_left] at xge; rw [max_eq_right] at xle
    have h : 0 < cos (x / 2) := by
      apply cos_pos_of_mem_Ioo; simp
      constructor; linarith only [xge, pi_pos]
      linarith only [xle, pi_pos]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp'; rw [continuousAt_tan]
    linarith only [h]; apply ContinuousAt.div_const
    exact fun ⦃U⦄ a => a
    any_goals linarith only [pi_pos]
    apply continuousOn_const
  · apply ContinuousOn.sub
    · apply ContinuousOn.div; apply continuousOn_const
      apply continuousOn_pow
      simp; exact aux
    apply ContinuousOn.div; apply continuousOn_const
    apply continuousOn_pow
    simp; exact aux
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply Continuous.continuousOn
      exact continuous_cos
    apply Continuous.continuousOn; apply Continuous.pow
    apply Continuous.add; exact continuous_const
    exact continuous_sin
    intro x hx; simp; rcases hx with ⟨xge, xle⟩
    rw [min_eq_left] at xge; rw [max_eq_right] at xle
    have : 0 ≤ sin x := by
      apply sin_nonneg_of_nonneg_of_le_pi
      exact xge; linarith only [xle, pi_pos]
    all_goals positivity
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    exact continuous_sin
  apply Continuous.continuousOn; apply Continuous.pow
  apply Continuous.add; exact continuous_const
  exact continuous_sin
  intro x hx; simp; rcases hx with ⟨xge, xle⟩
  rw [min_eq_left] at xge; rw [max_eq_right] at xle
  have : 0 ≤ sin x := by
    apply sin_nonneg_of_nonneg_of_le_pi
    exact xge; linarith only [xle, pi_pos]
  all_goals positivity