import Mathlib

open Real

theorem algebra_201459 (x : ℤ) (hx : 2 * x + 1 > 0 ∧ x - 1 > 0) :
    logb (1 / 4) (2 * x + 1) < logb (1 / 2) (x - 1) ↔ x ≤ 3 := by
  rcases hx with ⟨hx1, hx2⟩
  have hx1' : (2 * x + 1 : ℝ) > 0 := by exact_mod_cast hx1
  have hx2' : (x - 1 : ℝ) > 0 := by exact_mod_cast hx2
  constructor
  · -- Forward direction: logarithm inequality implies x ≤ 3
    intro h
    have h1 : logb (1 / 4) (2 * x + 1) = logb 2 (2 * x + 1) / logb 2 (1 / 4) := by
      field_simp [logb]
      all_goals linarith
    have h2 : logb (1 / 2) (x - 1) = logb 2 (x - 1) / logb 2 (1 / 2) := by
      field_simp [logb]
      all_goals linarith
    have h3 : logb 2 (1 / 4) = -2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h4 : logb 2 (1 / 2) = -1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h1, h2, h3, h4] at h
    have h5 : logb (2 : ℝ) (2 * x + 1) / (-2 : ℝ) < logb (2 : ℝ) (x - 1) / (-1 : ℝ) := by
      simpa using h
    have h7 : (logb (2 : ℝ) (2 * x + 1) / (2 : ℝ)) > logb (2 : ℝ) (x - 1) := by
      linarith
    have h8 : logb (2 : ℝ) (2 * x + 1) > 2 * logb (2 : ℝ) (x - 1) := by
      linarith
    have h9 : 2 * logb (2 : ℝ) (x - 1) = logb (2 : ℝ) ((x - 1 : ℝ) ^ 2) := by
      simp [logb_pow]
      <;> ring_nf
    rw [h9] at h8
    have h10 : (2 * x + 1 : ℝ) > (x - 1 : ℝ) ^ 2 := by
      have h6 : (2 * x + 1 : ℝ) > 0 := by exact_mod_cast hx1
      have h7 : (x - 1 : ℝ) > 0 := by exact_mod_cast hx2
      have h8' : logb (2 : ℝ) (2 * x + 1) > logb (2 : ℝ) ((x - 1 : ℝ) ^ 2) := h8
      have h4 : (2 * x + 1 : ℝ) > (0 : ℝ) := by linarith
      have h5 : (x - 1 : ℝ) ^ 2 > 0 := by nlinarith
      have h6 : (2 * x + 1 : ℝ) > (x - 1 : ℝ) ^ 2 := by
        by_contra h'
        push_neg at h'
        have : logb (2 : ℝ) (2 * x + 1) ≤ logb (2 : ℝ) ((x - 1 : ℝ) ^ 2) := by
          have h7' : (2 * x + 1 : ℝ) ≤ (x - 1 : ℝ) ^ 2 := by linarith
          have h8' : (2 * x + 1 : ℝ) > 0 := by exact_mod_cast hx1
          have h9' : (x - 1 : ℝ) ^ 2 > 0 := by nlinarith
          have : logb (2 : ℝ) (2 * x + 1) ≤ logb (2 : ℝ) ((x - 1 : ℝ) ^ 2) := by
            apply Real.logb_le_logb_of_le
            all_goals nlinarith
          linarith
        linarith
      linarith
    have h10' : (x : ℝ) ^ 2 - 4 * (x : ℝ) < (0 : ℝ) := by
      nlinarith
    have h11 : x ^ 2 < 4 * x := by
      have h11' : (x : ℝ) ^ 2 - 4 * (x : ℝ) < 0 := by
        linarith
      have h12 : (x : ℝ) ^ 2 < 4 * (x : ℝ) := by nlinarith
      norm_cast at h12 ⊢
      all_goals linarith
      all_goals linarith
    have h12 : x ≤ 3 := by
      nlinarith
      all_goals linarith
    exact_mod_cast h12
  · -- Backward direction: x ≤ 3 implies logarithm inequality
    intro h
    have h1 : logb (1 / 4) (2 * x + 1) = logb 2 (2 * x + 1) / logb 2 (1 / 4) := by
      field_simp [logb]
      all_goals linarith
    have h2 : logb (1 / 2) (x - 1) = logb 2 (x - 1) / logb 2 (1 / 2) := by
      field_simp [logb]
      all_goals linarith
    have h3 : logb 2 (1 / 4) = -2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h4 : logb 2 (1 / 2) = -1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h1, h2, h3, h4]
    have h17 : x ≤ 3 := by linarith
    have hx8 : (x : ℝ) ≤ (3 : ℝ) := by exact_mod_cast h17
    have hx3 : (x - 1 : ℝ) > (0 : ℝ) := by
      have h12 : (x - 1 : ℝ) > (0 : ℝ) := by
        exact_mod_cast hx2
      assumption
    have h14 : (2 * x + 1 : ℝ) > (x - 1 : ℝ) ^ 2 := by
      have h10 : x ≤ 3 := by linarith
      have h11 : x > 1 := by omega
      have h12 : x ≤ 3 := by omega
      have hx3 : (x - 1 : ℝ) > 0 := by
        have h12 : (x - 1 : ℝ) > (0 : ℝ) := by
          exact_mod_cast hx2
        assumption
      have hx4 : (x : ℝ) ≤ (3 : ℝ) := by exact_mod_cast h12
      have hx5 : (x : ℝ) > (1 : ℝ) := by
        have : (x - 1 : ℝ) > (0 : ℝ) := hx3
        linarith
      nlinarith [sq_nonneg ((x : ℝ) - 2), sq_nonneg ((x : ℝ) - 3), sq_nonneg ((x : ℝ) - 1), sq_nonneg (x), sq_nonneg ((x : ℝ) - 2)]
    have h15 : logb (2 : ℝ) (2 * x + 1) > 2 * logb (2 : ℝ) (x - 1) := by
      have h15 : logb (2 : ℝ) (2 * x + 1) > logb (2 : ℝ) ((x - 1 : ℝ) ^ 2) := by
        have h6 : (2 * x + 1 : ℝ) > 0 := by positivity
        have h7 : (x - 1 : ℝ) ^ 2 > 0 := by nlinarith
        have h8 : (2 * x + 1 : ℝ) > (x - 1 : ℝ) ^ 2 := h14
        have h9 : logb (2 : ℝ) (2 * x + 1) > logb (2 : ℝ) ((x - 1 : ℝ) ^ 2) := by
          apply Real.logb_lt_logb
          all_goals nlinarith
        assumption
      have h9' : logb (2 : ℝ) ((x - 1 : ℝ) ^ 2) = 2 * logb (2 : ℝ) (x - 1 : ℝ) := by
        simp [logb_pow]
        <;> ring_nf
      linarith [h15, h9']
    have h18 : (logb (2 : ℝ) (2 * x + 1) : ℝ) / (-2 : ℝ) < (logb (2 : ℝ) (x - 1) : ℝ) / (-1 : ℝ) := by
      linarith
    simpa using h18
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith