import Mathlib

open Real

theorem algebra_203940 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) :
    ((logb 2 (a^2)) + (logb 4 (1 / a^2))) * ((logb a 2) + (logb (a^2) (1 / 2))) = 1 / 2 := by

  have ha1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2
  have hab1 : 0 < a := by linarith
  have h1 : logb 2 (a^2) = 2 * logb 2 a := by
    simp [logb_pow]
    all_goals linarith
  have h2 : logb 4 (1 / a^2) = - logb 2 a := by
    have h3 : logb 4 (1 / a^2) = logb 2 (1 / a^2) / logb 2 (4 : ℝ) := by 
      field_simp [logb]
    have h4 : logb 2 (1 / a^2) = -2 * logb 2 a := by 
      have h5 : logb 2 (1 / a^2) = logb 2 (1 : ℝ) - logb 2 (a^2 : ℝ) := by
        rw [logb_div (by positivity) (by positivity)]
      have h6 : logb 2 (1 : ℝ) = 0 := by 
        simp [logb_one]
      have h7 : logb 2 (a^2 : ℝ) = 2 * logb 2 a := by
        simp [logb_pow]
      rw [h5, h6, h7]
      <;> ring_nf
      all_goals ring_nf
      <;> field_simp
    have h8 : logb 2 (4 : ℝ) = 2 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    rw [h3, h4, h8]
    all_goals field_simp
    <;> ring_nf
    all_goals field_simp
  have h5 : logb a 2 = 1 / logb 2 a := by
    field_simp [logb]
    all_goals linarith
  have h6 : logb (a ^ 2) (1 / 2) = -1 / (2 * logb 2 a) := by
    have h7 : logb (a ^ 2) (1 / 2) = logb 2 (1 / 2 : ℝ) / logb 2 (a ^ 2 : ℝ) := by
      field_simp [logb]
    have h8 : logb 2 (1 / 2 : ℝ) = -1 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    have h9 : logb 2 (a ^ 2 : ℝ) = 2 * logb 2 a := by
      simp [logb_pow]
      <;> try ring_nf
      <;> try field_simp
    rw [h7, h8, h9]
    all_goals field_simp
    all_goals ring_nf
    <;> try field_simp
    all_goals try ring_nf
    <;> try field_simp
  have h7 : (logb a 2 : ℝ) + (logb (a ^ 2) (1 / 2) : ℝ) = 1 / (2 * logb 2 a) := by
    rw [h5, h6]
    have h8 : logb 2 a ≠ 0 := by
      by_contra h
      have : a = 1 := by
        have : logb (2 : ℝ) (a) = 0 := by
          assumption
        rw [logb_eq_iff_rpow_eq] at this
        all_goals norm_num at this ⊢
        all_goals linarith
        all_goals try { linarith }
      contradiction
    field_simp at *
    <;> ring_nf
    <;> 
      try { assumption }
    <;> 
      try { nlinarith }
    all_goals try nlinarith
    all_goals try ring_nf
    all_goals try { tauto }
  have h8 : logb 2 (a^2) + logb 4 (1 / a ^ 2) = logb 2 a := by
    rw [h1, h2]
    linarith
  have h9 : logb 2 a ≠ 0 := by
    by_contra h
    have : a = 1 := by
      have : logb (2 : ℝ) a = 0 := by
        assumption
      rw [logb_eq_iff_rpow_eq] at this
      all_goals norm_num at this ⊢
      all_goals linarith
      all_goals try { linarith }
    contradiction
  rw [h8, h7]
  field_simp [h9]
  <;> ring_nf
  <;> try field_simp [h9]
  all_goals try nlinarith
  all_goals try ring_nf
  all_goals try { tauto }
  all_goals try assumption