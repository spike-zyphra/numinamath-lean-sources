import Mathlib

open Real Set
open scoped Real

theorem calculus_22482 :
  IsLeast {x : ℝ | 0 < x ∧ tan (π / 9) + 2 * tan (5 * π / 18) = tan (x * π / 180)} 70 := by
  constructor
  · -- Show 70 is in the set
    constructor
    · -- Show 70 > 0
      norm_num
    · -- Show the equality
      have h2 : tan (π / 9) + 2 * tan (5 * π / 18) = tan (70 * π / 180) := by
        have h3 : tan (70 * π / 180) = 1 / tan (π / 9) := by
          have h4 : 70 * π / 180 = π / 2 - π / 9 := by
            nlinarith [Real.pi_pos]
          rw [h4]
          rw [tan_pi_div_two_sub]
          <;> try { field_simp }
          <;> try { ring_nf }
          <;> try { field_simp }
          all_goals
            try { nlinarith }
        have h4 : tan (5 * π / 18) = (1 - tan (π / 9) ^ 2) / (2 * tan (π / 9)) := by
          have h5 : 5 * π / 18 = π / 2 - 2 * (π / 9) := by
            nlinarith [Real.pi_pos]
          rw [h5]
          have h6 : tan (π / 2 - 2 * (π / 9)) = 1 / tan (2 * (π / 9)) := by
            rw [tan_pi_div_two_sub]
            <;> try { field_simp }
          have h7 : tan (2 * (π / 9)) = 2 * tan (π / 9) / (1 - tan (π / 9) ^ 2) := by
            rw [tan_two_mul]
            <;> try { field_simp }
            all_goals try { ring_nf }
            all_goals try { nlinarith }
          rw [h6, h7]
          <;> try { field_simp }
          <;> try { ring_nf <;> field_simp [div_div_eq_div_mul] }
          all_goals
            try { nlinarith }
          all_goals try { ring }
          <;> try { field_simp }
          all_goals try { ring }
        rw [h3, h4]
        have h5 : tan (π / 9) ≠ 0 := by
          have h1_pos : 0 < π / 9 := by
            linarith [Real.pi_pos]
          have h2_pos : 0 < tan (π / 9) := by
            apply tan_pos_of_pos_of_lt_pi_div_two
            all_goals
              nlinarith [Real.pi_pos]
          linarith [h2_pos]
        field_simp at *
        <;> ring_nf <;> field_simp <;> nlinarith [Real.sin_pos_of_pos_of_lt_pi (show (0 : ℝ) < π / 9 by linarith [Real.pi_pos]), Real.sin_sq_add_cos_sq (π / 9), Real.sin_sq_add_cos_sq (2 * (π / 9)), Real.sin_sq_add_cos_sq (5 * (π / 18)), sq_nonneg (tan (π / 9)), sq_pos_of_ne_zero (show tan (π / 9) ≠ 0 by assumption), sq_nonneg (tan (π / 9) ^ 2), sq_nonneg (tan (π / 9) ^ 4)]
        all_goals try { assumption }
        all_goals try { positivity }
        all_goals try { nlinarith }
      linarith [h2]
  · -- Show that for all x in the set, x >= 70
    intro x ⟨hx_pos, hx_eq⟩
    by_contra h
    push_neg at h
    have h1 : x * π / 180 < 70 * π / 180 := by
      nlinarith [show (0 : ℝ) < π by linarith [Real.pi_pos], h]
    -- Show that tan is strictly increasing in (0, π/2)
    have h2 : tan (x * π / 180) < tan (70 * π / 180) := by
      apply Real.tan_lt_tan_of_lt_of_lt_pi_div_two
      all_goals
        nlinarith [show 0 < π by linarith [Real.pi_pos], hx_pos, show 0 < x * π / 180 by nlinarith [show 0 < π by linarith [Real.pi_pos], hx_pos], show 0 < 70 * π / 180 by nlinarith [show 0 < π by linarith [Real.pi_pos], show 0 < (70 : ℝ) by norm_num]]
    have h1_eq : tan (π / 9) + 2 * tan (5 * π / 18) = tan (70 * π / 180) := by
      have h2' : tan (π / 9) + 2 * tan (5 * π / 18) = tan (70 * π / 180) := by
        have h3 : tan (70 * π / 180) = 1 / tan (π / 9) := by
          have h4 : 70 * π / 180 = π / 2 - π / 9 := by
            nlinarith [Real.pi_pos]
          rw [h4]
          rw [tan_pi_div_two_sub]
          <;> try { field_simp }
          <;> try { ring_nf }
          <;> try { field_simp }
          all_goals
            try { nlinarith }
        have h4 : tan (5 * π / 18) = (1 - tan (π / 9) ^ 2) / (2 * tan (π / 9)) := by
          have h5 : 5 * π / 18 = π / 2 - 2 * (π / 9) := by
            nlinarith [Real.pi_pos]
          rw [h5]
          have h6 : tan (π / 2 - 2 * (π / 9)) = 1 / tan (2 * (π / 9)) := by
            rw [tan_pi_div_two_sub]
            <;> try { field_simp }
          have h7 : tan (2 * (π / 9)) = 2 * tan (π / 9) / (1 - tan (π / 9) ^ 2) := by
            rw [tan_two_mul]
            <;> try { field_simp }
            all_goals try { ring_nf }
            all_goals try { nlinarith }
          rw [h6, h7]
          <;> try { field_simp }
          <;> try { ring_nf <;> field_simp [div_div_eq_div_mul] }
          all_goals
            try { nlinarith }
          all_goals try { ring }
          <;> try { field_simp }
          all_goals try { ring }
        rw [h3, h4]
        have h5 : tan (π / 9) ≠ 0 := by
          have h1_pos : 0 < π / 9 := by
            nlinarith [Real.pi_pos]
          have h2_pos : 0 < tan (π / 9) := by
            apply tan_pos_of_pos_of_lt_pi_div_two
            all_goals
              nlinarith [Real.pi_pos]
          linarith [h2_pos]
        field_simp at *
        <;> ring_nf <;> field_simp <;> nlinarith [Real.sin_pos_of_pos_of_lt_pi (show (0 : ℝ) < π / 9 by linarith [Real.pi_pos]), Real.sin_sq_add_cos_sq (π / 9), Real.sin_sq_add_cos_sq (2 * (π / 9)), Real.sin_sq_add_cos_sq (5 * (π / 18)), sq_nonneg (tan (π / 9)), sq_pos_of_ne_zero (show tan (π / 9) ≠ 0 by assumption), sq_nonneg (tan (π / 9) ^ 2), sq_nonneg (tan (π / 9) ^ 4)]
      linarith [h2']
    have h3 : tan (x * π / 180) = tan (70 * π / 180) := by
      linarith [hx_eq, h1_eq]
    -- We get a contradiction
    have h4 : tan (x * π / 180) < tan (70 * π / 180) := by
      nlinarith
    nlinarith [h3, h4]