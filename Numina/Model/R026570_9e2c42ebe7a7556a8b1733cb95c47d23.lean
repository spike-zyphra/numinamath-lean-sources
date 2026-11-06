import Mathlib

theorem algebra_287595 {x : ℝ} (hx : x^5 - ⌊x⌋ = 5) :
    x = (6 ^ ((1 : ℝ) / 5)) := by
  have h1 : ⌊x⌋ = 1 := by
    have h2 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
    have h3 : x < ((⌊x⌋ + 1) : ℝ) := by exact Int.lt_floor_add_one x
    have eq1 : x^5 - (⌊x⌋ : ℝ) = 5 := by linarith
    have eq2 : x^5 = 5 + (⌊x⌋ : ℝ) := by linarith
    have h4 : ⌊x⌋ ≤ 1 := by 
      by_contra h
      push_neg at h
      have h5 : ⌊x⌋ ≥ 2 := by omega
      have h6 : (⌊x⌋ : ℝ) ≥ 2 := by exact_mod_cast h5
      have h7 : x ≥ (⌊x⌋ : ℝ) := by exact_mod_cast h2
      nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (x^2 - 1), sq_nonneg (x - 2), sq_nonneg (x^2 - 2), sq_nonneg (x^2 - 3)]
    have h8 : ⌊x⌋ ≥ 1 := by 
      by_contra h
      push_neg at h
      have h9 : ⌊x⌋ ≤ 0 := by omega
      have h10 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h9
      have h11 : x < ((⌊x⌋ + 1) : ℝ) := by exact Int.lt_floor_add_one x
      nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 2), sq_nonneg (x^2 - 3)]
    omega
  have h2 : ⌊x⌋ = 1 := h1
  have h3 : (⌊x⌋ : ℝ) = 1 := by exact_mod_cast h2
  have eq3 : x^5 = 6 := by
    have eq2 : x^5 = 5 + (⌊x⌋ : ℝ) := by 
      have h2 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
      linarith
    rw [h3] at eq2
    linarith
  have hx_pos : 0 ≤ x := by
    have h_floor_le_x : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
    have h_floor_eq_1 : (⌊x⌋ : ℝ) = 1 := by exact_mod_cast h1
    linarith
  have h4 : x = ((6 : ℝ) ^ ((1 : ℝ) / 5)) := by
    have h5 : x^5 = (6 : ℝ) := eq3
    have h6 : x = ((x^5) ^ ((1 : ℝ) / 5)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith [show 0 ≤ x by linarith]
    rw [h5] at h6
    exact h6
  exact h4