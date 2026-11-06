import Mathlib

theorem algebra_288044 {x : ℝ} (hx : x > 0) (h : ∃ r, (x - ⌊x⌋) = r * ⌊x⌋ ∧ x = r * (x - ⌊x⌋)) :
    x = (Real.sqrt 5 + 1) / 2 := by
  rcases h with ⟨r, h1, h2⟩
  have h3 : (⌊x⌋ : ℝ) ≤ x := by
    exact Int.floor_le x
  have h4 : x < (⌊x⌋ + 1 : ℝ) := by
    exact Int.lt_floor_add_one x
  have h7 : ⌊x⌋ = 1 := by
    have h8 : ⌊x⌋ > 0 := by
      by_contra h8
      push_neg at h8
      have h9 : ⌊x⌋ ≤ 0 := by omega
      have h10 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h9
      nlinarith [h1, h3, h10, show x > 0 by linarith]
    have h11 : ⌊x⌋ < 2 := by
      by_contra h11
      push_neg at h11
      have h12 : ⌊x⌋ ≥ 2 := by omega
      have h13 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h12
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), h1, h2, h3, h4, sq_nonneg (r - (1 + Real.sqrt 5) / 2), sq_nonneg (x - (1 + Real.sqrt 5) / 2)]
    omega
  have h7' : (⌊x⌋ : ℝ) = 1 := by exact_mod_cast h7
  have h8 : x - 1 = r := by
    rw [show (⌊x⌋ : ℝ) = 1 by linarith [h7']] at h1
    linarith
  have h9 : x = r ^ 2 := by
    have h10 : x - 1 = r := h8
    have h11 : x = r * (x - 1) := by
      have h12 : x - 1 = r * 1 := by
        linarith [h8]
      rw [show (⌊x⌋ : ℝ) = 1 by linarith [h7']] at h2
      nlinarith [h12, h2]
    rw [show x - 1 = r by linarith [h8]] at h11
    nlinarith
  have h10 : r ^ 2 = r + 1 := by
    have h8' : x = r + 1 := by
      linarith [h8]
    have h9' : x = r ^ 2 := h9
    nlinarith [h9']
  have h11 : r > 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), h8, h3, h7']
  have h12 : r = (1 + Real.sqrt 5) / 2 := by
    have h12 : r ^ 2 - r - 1 = 0 := by linarith [h10]
    have h13 : r ^ 2 - r - 1 = (r - (1 + Real.sqrt 5) / 2) * (r - (1 - Real.sqrt 5) / 2) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [h13] at h12
    cases' (mul_eq_zero.1 h12) with h14 h15
    · -- Case r - (1 + Real.sqrt 5) / 2 = 0
      linarith
    · -- Case r - (1 - Real.sqrt 5) / 2 = 0
      have h16 : r = (1 - Real.sqrt 5) / 2 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h13 : x = (1 + Real.sqrt 5) / 2 := by
    have h8' : x = r + 1 := by
      linarith [h8]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]