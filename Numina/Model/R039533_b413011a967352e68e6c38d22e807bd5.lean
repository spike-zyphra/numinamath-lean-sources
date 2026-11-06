import Mathlib

theorem algebra_98145 {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (n : ℝ)
(hn : n > 0)
(h₁ : Real.logb 10 (Real.sin x) + Real.logb 10 (Real.cos x) = -1)
(h₂ : Real.logb 10 (Real.sin x + Real.cos x) = (Real.logb 10 n - 1) / 2) :
n = 12 := by
  rcases hx with ⟨hx1, hx2⟩
  have hsin : 0 < Real.sin x := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have hcos : 0 < Real.cos x := by 
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith
  have h3 : Real.sin x * Real.cos x = 1 / 10 := by
    have h4 : Real.logb 10 (Real.sin x) + Real.logb 10 (Real.cos x) = Real.logb 10 (Real.sin x * Real.cos x) := by
      rw [← Real.logb_mul (by linarith) (by linarith)]
    rw [h4] at h₁
    have h5 : Real.sin x * Real.cos x = (10 : ℝ) ^ (-1 : ℝ) := by 
      have h6 : Real.logb 10 (Real.sin x * Real.cos x) = -1 := by linarith
      have h7 : Real.sin x * Real.cos x = (10 : ℝ) ^ (Real.logb 10 (Real.sin x * Real.cos x)) := by
        field_simp
      rw [h6] at h7
      linarith
    have h8 : (10 : ℝ) ^ (-1 : ℝ) = (1 / 10 : ℝ) := by
      norm_num
    rw [h8] at h5 
    linarith
  have h7 : (Real.sin x + Real.cos x) ^ 2 = 1 + 2 * (Real.sin x * Real.cos x) := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have h8 : (Real.sin x + Real.cos x) ^ 2 = 12 / 10 := by
    rw [h7, h3]
    norm_num
  have h254 : Real.logb 10 (Real.sin x + Real.cos x) = (Real.logb 10 (12 : ℝ) - 1) / 2 := by
    have hx10 : Real.logb 10 (Real.sin x + Real.cos x) = (1 / 2) * Real.logb 10 ((Real.sin x + Real.cos x) ^ 2) := by
      have h11 : Real.logb 10 ((Real.sin x + Real.cos x) ^ 2) = 2 * Real.logb 10 (Real.sin x + Real.cos x) := by 
        simp [Real.logb_pow]
      linarith
    have hx11 : (Real.sin x + Real.cos x) ^ 2 = 12 / 10 := by
      linarith [h8]
    have hx12 : Real.logb 10 ((Real.sin x + Real.cos x) ^ 2) = Real.logb 10 (12 / 10) := by 
      rw [hx11]
    have hx13 : Real.logb 10 (12 / 10) = Real.logb 10 (12 : ℝ) - Real.logb 10 (10 : ℝ) := by
      field_simp [Real.logb_div]
    have hx14 : Real.logb 10 (10 : ℝ) = 1 := by 
      simp [Real.logb_self_eq_one]
    have hx15 : Real.logb 10 ((Real.sin x + Real.cos x) ^ 2) = Real.logb 10 (12 : ℝ) - 1 := by
      rw [hx13] at hx12
      have hx15 : Real.logb 10 (10 : ℝ) = 1 := by
        simp [Real.logb_self_eq_one]
      linarith [hx12, hx14]
    rw [hx10]
    linarith [hx15]
  have h26 : (Real.logb 10 (12 : ℝ) - 1) / 2 = (Real.logb 10 n - 1) / 2 := by
    linarith [h₂, h254]
  have h27 : Real.logb 10 (12 : ℝ) = Real.logb 10 n := by
    linarith [h26]
  have h28 : (12 : ℝ) = n := by
    have h29 : Real.logb 10 (12 : ℝ) = Real.logb 10 n := by 
      linarith [h27]
    have h30 : (12 : ℝ) > 0 := by norm_num
    have h31 : n > 0 := by linarith
    have h32 : (12 : ℝ) = n := by 
      apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h30) (Set.mem_Ioi.mpr h31) h29 
      all_goals norm_num
    linarith
  linarith [h28]