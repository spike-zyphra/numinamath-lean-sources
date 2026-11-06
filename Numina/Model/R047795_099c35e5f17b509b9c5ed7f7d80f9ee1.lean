import Mathlib

open Real

lemma lemma_1 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hne : a ≠ 1 ∧ x ≠ 1) :
    x ^ ((1 : ℝ) / Real.logb a x) = a := by
  have h1 : a ≠ 1 := hne.1
  have h2 : x ≠ 1 := hne.2
  have h3 : Real.logb a x = Real.log x / Real.log a := by
    field_simp [Real.logb]
  have h4 : Real.log a ≠ 0 := by
    by_contra h
    have h5 : a = 1 := by
      rw [Real.log_eq_zero] at h
      rcases h with (r | r | r)
      .
        linarith
      .
        linarith
      .
        linarith
    tauto
  have h5 : Real.log x ≠ 0 := by
    by_contra h
    have h6 : x = 1 := by
      rw [Real.log_eq_zero] at h
      rcases h with (r | r | r)
      .
        linarith
      .
        linarith
      .
        linarith
    tauto
  have h6 : (1 : ℝ) / Real.logb a x = Real.log a / Real.log x := by
    rw [h3]
    field_simp [h4, h5]
  rw [h6]
  have h7 : x ^ (Real.log a / Real.log x) = a := by
    have h8 : x ^ (Real.log a / Real.log x) = Real.exp ( (Real.log a / Real.log x) * Real.log x ) := by
      rw [Real.rpow_def_of_pos hx]
      field_simp
      all_goals linarith
    have h9 : (Real.log a / Real.log x) * Real.log x = Real.log a := by
      field_simp [h5]
      all_goals linarith
    rw [h8]
    rw [h9]
    have h10 : Real.exp (Real.log a) = a := Real.exp_log (by linarith)
    rw [h10]
  exact h7


theorem algebra_212368 : ((2017 : ℝ) ^ ((1 : ℝ) / logb 2 2017) *
    (2017 ^ ((1 : ℝ) / logb 4 2017)) *
    (2017 ^ ((1 : ℝ) / logb 8 2017)) *
    (2017 ^ ((1 : ℝ) / logb 16 2017)) *
    (2017 ^ ((1 : ℝ) / logb 32 2017))) ^ ((1 : ℝ) / 5) = 8 := by

  have h1 : (2017 : ℝ) ^ ((1 : ℝ) / logb 2 2017) = (2 : ℝ) := by
    have hne1 : (2 : ℝ) ≠ 1 := by norm_num
    have hne2 : (2017 : ℝ) ≠ 1 := by norm_num
    have hpos1 : (2 : ℝ) > 0 := by norm_num
    have hpos2 : (2017 : ℝ) > 0 := by norm_num
    have h3 : (2017 : ℝ) ^ ((1 : ℝ) / logb 2 2017) = (2 : ℝ) := by
      rw [lemma_1 (2 : ℝ) (2017 : ℝ) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
    exact h3
  have h2 : (2017 : ℝ) ^ ((1 : ℝ) / logb 4 2017) = (4 : ℝ) := by
    have hne1 : (4 : ℝ) ≠ 1 := by norm_num
    have hne2 : (2017 : ℝ) ≠ 1 := by norm_num
    have hpos1 : (4 : ℝ) > 0 := by norm_num
    have hpos2 : (2017 : ℝ) > 0 := by norm_num
    have h4 : (2017 : ℝ) ^ ((1 : ℝ) / logb 4 2017) = (4 : ℝ) := by
      rw [lemma_1 (4 : ℝ) (2017 : ℝ) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
    exact h4
  have h3 : (2017 : ℝ) ^ ((1 : ℝ) / logb 8 2017) = (8 : ℝ) := by
    have hne1 : (8 : ℝ) ≠ 1 := by norm_num
    have hne2 : (2017 : ℝ) ≠ 1 := by norm_num
    have hpos1 : (8 : ℝ) > 0 := by norm_num
    have hpos2 : (2017 : ℝ) > 0 := by norm_num
    have h8 : (2017 : ℝ) ^ ((1 : ℝ) / logb 8 2017) = (8 : ℝ) := by
      rw [lemma_1 (8 : ℝ) (2017 : ℝ) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
    exact h8
  have h4 : (2017 : ℝ) ^ ((1 : ℝ) / logb 16 2017) = (16 : ℝ) := by
    have hne1 : (16 : ℝ) ≠ 1 := by norm_num
    have hne2 : (2017 : ℝ) ≠ 1 := by norm_num
    have hpos1 : (16 : ℝ) > 0 := by norm_num
    have hpos2 : (2017 : ℝ) > 0 := by norm_num
    have h16 : (2017 : ℝ) ^ ((1 : ℝ) / logb 16 2017) = (16 : ℝ) := by
      rw [lemma_1 (16 : ℝ) (2017 : ℝ) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
    exact h16
  have h5 : (2017 : ℝ) ^ ((1 : ℝ) / logb 32 2017) = (32 : ℝ) := by
    have hne1 : (32 : ℝ) ≠ 1 := by norm_num
    have hne2 : (2017 : ℝ) ≠ 1 := by norm_num
    have hpos1 : (32 : ℝ) > 0 := by norm_num
    have hpos2 : (2017 : ℝ) > 0 := by norm_num
    have h32 : (2017 : ℝ) ^ ((1 : ℝ) / logb 32 2017) = (32 : ℝ) := by
      rw [lemma_1 (32 : ℝ) (2017 : ℝ) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
    exact h32
  rw [h1, h2, h3, h4, h5]
  have h6 : ((2 * 4 * 8 * 16 * 32) : ℝ) = (32768 : ℝ) := by norm_num
  have h7 : ((32768 : ℝ) ) ^ ((1 : ℝ) / 5) = (8 : ℝ) := by
    have h9 : ((32768 : ℝ) ) = (8 : ℝ) ^ (5 : ℝ) := by norm_num
    rw [h9]
    have h10 : ((8 : ℝ) ^ (5 : ℝ) ) ^ ((1 : ℝ) / 5) = (8 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h10]
  rw [h6]
  rw [h7]