import Mathlib

open Real

theorem algebra_325486 (α : ℝ) (hα : α ∈ Set.Ioo 0 (π / 4)) (t1 t2 t3 t4 : ℝ)
    (ht1 : t1 = (tan α) ^ (tan α)) (ht2 : t2 = (tan α) ^ (cot α))
    (ht3 : t3 = (cot α) ^ (tan α)) (ht4 : t4 = (cot α) ^ (cot α)) :
    t2 < t1 ∧ t1 < t3 ∧ t3 < t4 := by
  rcases hα with ⟨hα1, hα2⟩
  have htan : 0 < tan α := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    all_goals linarith [hα1, hα2, Real.pi_pos]
  have htan_lt_one : tan α < 1 := by
    have h1 : tan (π / 4) = 1 := by
      rw [tan_pi_div_four]
    have h2 : tan α < tan (π / 4) := by
      apply Real.tan_lt_tan_of_lt_of_lt_pi_div_two
      all_goals linarith [hα1, hα2, Real.pi_pos]
    linarith [h1, h2]
  -- Show 1 < cot α
  have hcot : 1 < cot α := by
    have htan_pos : 0 < tan α := htan
    have htan_lt_one : tan α < 1 := htan_lt_one
    have : cot α = 1 / tan α := by
      rw [cot_eq_cos_div_sin]
      field_simp [tan_eq_sin_div_cos]
    rw [this]
    apply (one_lt_div htan_pos).mpr
    linarith
  have htan_lt_hcot : tan α < cot α := by
    linarith [hcot, htan_lt_one]
  have h1 : t2 < t1 := by
    rw [ht2, ht1]
    have h4 : (tan α) ^ (tan α) > (tan α) ^ (cot α) := by
      have h5 : tan α < 1 := htan_lt_one
      have h6 : tan α < (cot α : ℝ) := htan_lt_hcot
      have h7 : (tan α) ^ (tan α) > (tan α) ^ (cot α) := by
        apply Real.rpow_lt_rpow_of_exponent_gt
        all_goals
        nlinarith [htan, htan_lt_one, hcot, htan_lt_hcot]
      linarith
    linarith
  have h2 : t1 < t3 := by
    rw [ht1, ht3]
    have h6 : (tan α) ^ (tan α) < (cot α) ^ (tan α) := by
      have h8 : (tan α : ℝ) < (cot α : ℝ) := htan_lt_hcot
      have h7 : 0 < (tan α : ℝ) := htan
      have h9 : 0 < (cot α : ℝ) := by
        linarith [hcot]
      have h10 : (tan α : ℝ) < (cot α : ℝ) := htan_lt_hcot
      have h11 : (tan α) ^ (tan α) < (cot α) ^ (tan α) := by
        apply Real.rpow_lt_rpow
        all_goals
        nlinarith [htan, htan_lt_one, hcot, htan_lt_hcot]
      linarith
    linarith
  have h3 : t3 < t4 := by
    rw [ht3, ht4]
    have h6 : (cot α : ℝ) ^ (tan α) < (cot α : ℝ) ^ (cot α) := by
      have h7 : 1 < (cot α : ℝ) := hcot
      have h8 : (tan α : ℝ) < (cot α : ℝ) := htan_lt_hcot
      have h9 : (cot α : ℝ) ^ (tan α) < (cot α : ℝ) ^ (cot α) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals
        nlinarith [hcot, htan_lt_one, htan, hcot]
      linarith
    linarith
  constructor
  · exact h1
  constructor
  · exact h2
  · exact h3