import Mathlib

theorem algebra_110132 {x : ℝ}
  (x_pos : x > 0)
  (h_series : ∃ r, -- defined recursively with a factor of r
    ⌊x⌋ = r * (x - ⌊x⌋) ∧ -- n = r * t
    x = r * ⌊x⌋           -- x = r * n
  ) : x = (1 + Real.sqrt 5) / 2 := by
  rcases h_series with ⟨r, h1, h2⟩
  have h3 : ⌊x⌋ ≤ (x : ℝ) := by exact Int.floor_le x
  have h4 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h5 : (⌊x⌋ : ℝ) ≥ 0 := by 
    have h6 : ⌊x⌋ ≥ 0 := by 
      by_contra h
      push_neg at h
      have h7 : ⌊x⌋ ≤ -1 := by omega
      have h8 : (⌊x⌋ : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h7
      nlinarith
    exact_mod_cast h6
  have h6 : ⌊x⌋ ≥ 1 := by
    by_contra h
    push_neg at h
    have h7 : ⌊x⌋ ≤ 0 := by omega
    have h8 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h7
    have h9 : x = 0 := by
      nlinarith [h2, h8]
    linarith
  have h7 : (⌊x⌋ : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h6
  have h8 : x = r * (⌊x⌋ : ℝ) := by linarith [h2]
  have h9 : (⌊x⌋ : ℝ) > 0 := by
    have h10 : ⌊x⌋ ≥ 1 := by omega
    have h11 : (⌊x⌋ : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h10
    nlinarith
  have h10 : x - (⌊x⌋ : ℝ) > 0 := by
    nlinarith [h3, h4]
  have h11 : (⌊x⌋ : ℝ) ≠ 0 := by nlinarith
  have h12 : r ^ 2 - r - 1 = 0 := by
    have h_eq2 : ⌊x⌋ = r * (x - (⌊x⌋ : ℝ)) := by
      linarith [h1]
    rw [h8] at h_eq2
    have h_eq3 : r ^ 2 - r - 1 = 0 := by
      have h13 : (⌊x⌋ : ℝ) > 0 := by nlinarith
      have h_eq4 : r * (⌊x⌋ : ℝ) * (r - 1) = ⌊x⌋ := by nlinarith
      apply (mul_left_inj' (ne_of_gt h13)).mp
      nlinarith
    nlinarith
  have h13 : r > 0 := by 
    nlinarith [h10, h8, h9, x_pos]
  have hr : r = (1 + Real.sqrt 5) / 2 := by
    have h14 : r ^ 2 - r - 1 = 0 := h12
    have h15 : r ^ 2 - r - 1 = (r - (1 + Real.sqrt 5) / 2) * (r - (1 - Real.sqrt 5) / 2) := by
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      linarith
    rw [h15] at h14
    cases (mul_eq_zero.mp h14) with
    | inl h16 =>
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sqrt_nonneg 5]
    | inr h17 =>
      have h18 : r = (1 - Real.sqrt 5) / 2 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sqrt_nonneg 5]
  have hx : x = r * (⌊x⌋ : ℝ) := by linarith [h2]
  have hn : ⌊x⌋ = 1 := by
    by_contra h
    push_neg at h
    have h16 : ⌊x⌋ ≥ 2 := by 
      omega
    have h17 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h16
    have h18 : x = r * (⌊x⌋ : ℝ) := by linarith [h2]
    nlinarith [h18, hr, Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), h9, h3, h4]
  have h_floor1 : ⌊x⌋ = 1 := by omega
  have hx2 : x = r * (1 : ℝ) := by 
    rw [show (⌊x⌋ : ℝ) = 1 by exact_mod_cast h_floor1] at hx
    linarith
  rw [hr] at hx2
  linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]