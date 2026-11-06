import Mathlib

open Real Set
open scoped Real

theorem calculus_14303 (θ φ : ℝ) (hθ : θ ∈ Ioo 0 (π / 2)) (hφ : φ ∈ Ioo 0 (π / 2))
    (htan : tan θ = 1 / 7) (hsin : sin φ = 1 / sqrt 10) :
    θ + 2 * φ = π / 4 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  rcases hφ with ⟨hφ1, hφ2⟩

  have htanφ : tan φ = 1 / 3 := by
    have hsinφ : sin φ = 1 / sqrt 10 := hsin
    have hcosφ : cos φ = 3 / sqrt 10 := by
      have hcos : cos φ ^ 2 + sin φ ^ 2 = 1 := Real.cos_sq_add_sin_sq φ
      rw [hsinφ] at hcos

      have hcos_pos : cos φ > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith [hφ1, Real.pi_pos]
        · linarith [hφ2, Real.pi_pos]
      have htan2 : cos φ > 0 := hcos_pos
      have htan2_pos : cos φ = 3 / sqrt 10 := by
        field_simp at hcos ⊢
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (10 : ℝ) > 0),
          Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by linarith : (10 : ℝ) ≥ 0),
          hcos_pos
        ]
      linarith [htan2_pos]

    have htanφ1 : tan φ = 1 / 3 := by
      rw [Real.tan_eq_sin_div_cos]
      have h1 : sin φ = 1 / sqrt 10 := hsinφ
      have h2 : cos φ = 3 / sqrt 10 := hcosφ
      rw [h1, h2]
      have h3 : sqrt 10 > 0 := by
        positivity
      field_simp
      all_goals nlinarith

    exact htanφ1

  have h_eq1 : θ = arctan (1 / 7) := by
    rw [← htan]
    rw [Real.arctan_tan]
    all_goals
      nlinarith [Real.pi_pos, hθ1, hθ2]

  have h_eq2 : φ = arctan (1 / 3) := by
    rw [← htanφ]
    rw [Real.arctan_tan]
    all_goals
      nlinarith [Real.pi_pos, hφ1, hφ2]

  rw [h_eq1, h_eq2]

  have h_eq3 : arctan (1 / 7) + 2 * arctan (1 / 3) = Real.pi / 4 := by

    have h1 : 2 * Real.arctan (1 / 3) = Real.arctan (3 / 4) := by
      have h3 : 2 * Real.arctan (1 / 3) = Real.arctan (1 / 3) + Real.arctan (1 / 3) := by ring
      rw [h3]
      rw [Real.arctan_add]
      all_goals norm_num

    rw [h1]
    have h2 : Real.arctan (1 / 7) + Real.arctan (3 / 4) = Real.pi / 4 := by
      have htan : Real.arctan (1 / 7) + Real.arctan (3 / 4) = Real.arctan (1) := by
        rw [Real.arctan_add]
        norm_num
        all_goals norm_num
      rw [htan]
      linarith [Real.arctan_one]
      all_goals linarith

    exact h2

  exact h_eq3