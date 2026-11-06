import Mathlib

open Real Set
open scoped Real

theorem algebra_163862 (α : ℝ) :
  (cos (α + 3/2 * π) + 2 * cos (11/6 * π - α)) /
  (2 * sin (π/3 + α) + sqrt 3 * sin (3/2 * π - α)) =
  sqrt 3 / tan α := by
  have h1 : cos (α + 3 / 2 * π) = sin α := by
    have h1 : cos (α + 3 / 2 * π) = cos (α + π / 2 + π) := by
      ring_nf
    rw [h1]
    have h2 : cos (α + π / 2 + π) = -cos (α + π / 2) := by
      rw [cos_add_pi]
    rw [h2]
    have h3 : cos (α + π / 2) = -sin α := by
      rw [cos_add_pi_div_two]
      <;> ring_nf
    rw [h3]
    all_goals ring
  have h2 : cos (11 / 6 * π - α) = Real.sqrt 3 / 2 * cos α - 1 / 2 * sin α := by
    have h3 : cos (11 / 6 * π - α) = cos (11 / 6 * π) * cos α + sin (11 / 6 * π) * sin α := by
      rw [cos_sub]
    have hcos : cos (11 / 6 * π) = Real.sqrt 3 / 2 := by
      have h1 : cos (11 / 6 * π) = cos (2 * π - (Real.pi / 6)) := by
        ring_nf
      rw [h1]
      rw [cos_two_pi_sub]
      have hcos_pi_6 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
        exact cos_pi_div_six
      linarith [hcos_pi_6]
    have hsin : sin (11 / 6 * π) = -1 / 2 := by
      have h1 : sin (11 / 6 * π) = sin (2 * π - (Real.pi / 6)) := by
        ring_nf
      rw [h1]
      rw [sin_two_pi_sub]
      have hsin_pi_6 : sin (Real.pi / 6) = 1 / 2 := by
        exact sin_pi_div_six
      linarith [hsin_pi_6]
    rw [h3, hcos, hsin]
    all_goals ring
  have h3 : sin (π / 3 + α) = Real.sqrt 3 / 2 * cos α + 1 / 2 * sin α := by
    rw [sin_add]
    have hsin : sin (π / 3) = Real.sqrt 3 / 2 := by
      rw [sin_pi_div_three]
    have hcos : cos (π / 3) = 1 / 2 := by
      rw [cos_pi_div_three]
    rw [hsin, hcos]
    all_goals ring
  have h4 : sin (3 / 2 * π - α) = - cos α := by
    have h1 : sin (3 / 2 * π - α) = sin (3 / 2 * π) * cos α - cos (3 / 2 * π) * sin α := by
      rw [sin_sub]
    rw [h1]
    have hsin : sin (3 / 2 * π) = -1 := by
      have h1 : sin (3 / 2 * π) = sin (π + π / 2) := by
        ring_nf
      rw [h1]
      rw [sin_add]
      have hsin_pi : sin (π) = 0 := by
        rw [sin_pi]
      have hcos_pi : cos (π) = -1 := by
        rw [cos_pi]
      have hsin_pi_2 : sin (π / 2) = 1 := by
        rw [sin_pi_div_two]
      have hcos_pi_2 : cos (π / 2) = 0 := by
        rw [cos_pi_div_two]
      simp [hsin_pi, hcos_pi, hsin_pi_2, hcos_pi_2]
      all_goals linarith
    have hcos : cos (3 / 2 * π) = 0 := by
      have h1 : cos (3 / 2 * π) = cos (π + π / 2) := by
        ring_nf
      rw [h1]
      rw [cos_add]
      have hsin_pi : sin (π) = 0 := by
        rw [sin_pi]
      have hcos_pi : cos (π) = -1 := by
        rw [cos_pi]
      have hsin_pi_2 : sin (π / 2) = 1 := by
        rw [sin_pi_div_two]
      have hcos_pi_2 : cos (π / 2) = 0 := by
        rw [cos_pi_div_two]
      simp [hsin_pi, hcos_pi, hsin_pi_2, hcos_pi_2]
      all_goals linarith
    rw [hsin, hcos]
    all_goals ring_nf
  have h_num : cos (α + 3/2 * π) + 2 * cos (11/6 * π - α) = Real.sqrt 3 * cos α := by
    rw [h1, h2]
    ring_nf
  have h_den : 2 * sin (π/3 + α) + Real.sqrt 3 * sin (3/2 * π - α) = sin α := by
    rw [h3, h4]
    ring_nf
  rw [h_num, h_den]
  by_cases h : sin α = 0
  · -- Case $\sin \alpha = 0$
    rw [h]
    norm_num [h, tan_eq_sin_div_cos]
    all_goals try { linarith }
    all_goals try { tauto }
  · -- Case $\sin \alpha \neq 0$
    have htan : tan α = sin α / cos α := by
      rw [tan_eq_sin_div_cos]
    rw [htan]
    have h5 : cos α ≠ 0 ∨ cos α = 0 := by
      by_cases hcos : cos α = 0
      · tauto
      · tauto
    cases h5 with
    | inl hcosne =>
      field_simp [h, hcosne]
      <;> ring_nf <;> field_simp [h, hcosne] <;> tauto
    | inr hcos =>
      have h6 : cos α = 0 := hcos
      rw [h6]
      norm_num
      <;> field_simp [h]
      <;> ring_nf <;> field_simp [h]
      <;> linarith
      all_goals try { tauto }