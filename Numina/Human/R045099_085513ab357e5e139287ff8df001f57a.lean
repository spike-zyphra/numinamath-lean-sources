import Mathlib

open Real

/-
  For any angle $0<\theta<\pi / 2$, show that

  $$
  0<\sin \theta+\cos \theta+\tan \theta+\cot \theta-\sec \theta-\csc \theta<1
  $$
-/
theorem inequalities_610036 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < sin θ + cos θ + tan θ + cot θ - 1 / cos θ - 1 / sin θ ∧
    sin θ + cos θ + tan θ + cot θ - 1 / cos θ - 1 / sin θ < 1 := by
  simp at hθ
  -- prove sin θ ∈ (0, 1)
  have h1 : sin θ > 0 ∧ sin θ < 1 := by
    constructor
    · apply sin_pos_of_pos_of_lt_pi hθ.1
      apply lt_trans hθ.2
      apply div_lt_self pi_pos
      norm_num
    · rw [←sin_pi_div_two]
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      · apply le_of_lt
        apply lt_trans ?_ hθ.1
        apply neg_lt_zero.mpr
        exact pi_div_two_pos
      · simp
      · exact hθ.2
  -- prove cos θ ∈ (0, 1)
  have h2 : cos θ > 0 ∧ cos θ < 1 := by
    constructor
    · apply cos_pos_of_mem_Ioo
      simp
      constructor
      · apply lt_trans ?_ hθ.1
        apply neg_lt_zero.mpr
        exact pi_div_two_pos
      · exact hθ.2
    · rw [←cos_zero]
      apply cos_lt_cos_of_nonneg_of_le_pi_div_two
      · simp
      · exact le_of_lt hθ.2
      · exact hθ.1
  -- prove sin θ * cos θ > 0
  have h3 : sin θ * cos θ > 0 := by exact mul_pos h1.1 h2.1
  -- prove x ^ 3 ≥ 2 * x ^ 2 - x for 0 < x < 1
  have h4 {x : ℝ} (h : x > 0 ∧ x < 1) : x ^ 3 ≥ 2 * x ^ 2 - x := by
    suffices h : x * (x - 1) ^ 2 ≥ 0
    · calc
        _ = 2 * x ^ 2 - x + x * (x - 1) ^ 2 := by ring
        _ ≥ 2 * x ^ 2 - x := by linarith [h]
    · apply mul_nonneg
      · apply le_of_lt h.1
      · exact sq_nonneg (x - 1)
  -- simplify sin θ + cos θ + tan θ + cot θ - 1 / cos θ - 1 / sin θ to (1 - sin θ ^ 3 - cos θ ^ 3) / (sin θ * cos θ)
  have heq : sin θ + cos θ + tan θ + cot θ - 1 / cos θ - 1 / sin θ = (1 - (sin θ) ^ 3 - (cos θ) ^ 3) / (sin θ * cos θ) := by
    have : sin θ ≠ 0 := by apply ne_of_gt; exact h1.1
    have : cos θ ≠ 0 := by apply ne_of_gt; exact h2.1
    calc
      _ = (sin θ ^ 2 + cos θ ^ 2 - cos θ * (1 - sin θ ^ 2) - sin θ * (1 - cos θ ^ 2)) / (sin θ * cos θ) := by
        rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin]
        field_simp only
        ring
      _ = _ := by
        field_simp
        nth_rw 1 1 [cos_sq', sin_sq]
        ring
  rw [heq]
  -- prove the result
  constructor
  · -- it suffices to prove 1 - sin θ ^ 3 - cos θ ^ 3 > 0
    apply div_pos ?_ h3
    -- note that sin θ ^ 3 ≤ sin θ ^ 2 and cos θ ^ 3 ≤ cos θ ^ 2
    calc
      (0 : ℝ) = 1 - 1 := by norm_num
      _ = 1 - (sin θ ^ 2) - cos θ ^ 2 := by nth_rw 2 [←cos_sq_add_sin_sq θ]; ring
      _ < _ := by
        apply sub_lt_sub
        · simp
          apply pow_lt_pow_iff_right_of_lt_one₀ h1.1 h1.2 |>.mpr
          norm_num
        · apply pow_lt_pow_iff_right_of_lt_one₀ h2.1 h2.2 |>.mpr
          norm_num
  · -- it suffices to prove 1 - sin θ ^ 3 - cos θ ^ 3 < cos θ * sin θ
    apply div_lt_iff₀ h3 |>.mpr
    simp
    -- Note that sin θ ^ 3 ≥ 2 * sin θ ^ 2 - sin θ and cos θ ^ 3 ≥ 2 * cos θ ^ 2 - cos θ
    -- Then we have that 1 - sin θ ^ 3 - cos θ ^ 3 < sin θ + cos θ - 1
    calc
      _ ≤ 1 - (2 * sin θ ^ 2 - sin θ) - (2 * cos θ ^ 2 - cos θ) := by rel [h4 h1, h4 h2]
      _ = 1 - 2 * (sin θ ^ 2 + cos θ ^ 2) + sin θ + cos θ := by ring
      _ = -1 + sin θ + cos θ := by
        simp
        norm_num
      _ < -1 + sin θ + cos θ + (sin θ - 1) * (cos θ - 1) := by
        -- Reduce to (sin θ - 1) * (cos θ - 1) > 0
        -- which is trivial
        simp
        apply mul_pos_of_neg_of_neg
        all_goals linarith
      _ = _ := by ring
