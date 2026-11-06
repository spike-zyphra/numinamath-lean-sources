import Mathlib

theorem number_theory_181362 (x : ℝ) (hx : x > 0) (h : ⌊x⌋ = (1 - 43 / 100) * x) :
    x = 1 + 43 / 57 := by
  have h1 : ⌊x⌋ = (57 / 100) * x := by
    have h2 : (1 - 43 / 100 : ℝ) = (57 / 100 : ℝ) := by norm_num
    rw [h2] at h
    linarith
  have h2 : (⌊x⌋ : ℝ) = (57 / 100) * x := by
    linarith
  have h3 : ⌊x⌋ ≥ 0 := by
    have h4 : x > 0 := hx
    have h5 : ⌊x⌋ ≥ 0 := by
      apply Int.floor_nonneg.mpr
      all_goals linarith
    omega
  have h4 : (⌊x⌋ : ℝ) = (57 / 100) * x := by
    linarith
  have h5 : x > 0 := hx
  have h6 : (⌊x⌋ : ℝ) = (57 / 100) * x := h1
  have h7 : (⌊x⌋ : ℝ) ≤ x := by
    have h8 : (⌊x⌋ : ℝ) ≤ x := by
      exact Int.floor_le x
    linarith
  have h8 : x < (⌊x⌋ + 1 : ℝ) := by
    have h9 : x < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    linarith
  have h9 : (⌊x⌋ : ℝ) = (57 / 100) * x := h1
  have h11 : ⌊x⌋ = 1 := by
    have h10 : ⌊x⌋ > 0 := by
      by_contra h13
      push_neg at h13
      have h14 : ⌊x⌋ ≤ 0 := by
        omega
      have h15 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by
        exact_mod_cast h14
      nlinarith [h1, h15, hx]
    have h12 : ⌊x⌋ < 2 := by
      by_contra h11
      push_neg at h11
      have h12 : ⌊x⌋ ≥ 2 := by
        omega
      have h13 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by
        exact_mod_cast h12
      nlinarith [h8, h1, h13]
    have h13 : ⌊x⌋ = 1 := by
      omega
    exact h13
  have h15 : x = 100 / 57 := by
    have h16 : x = 100 / 57 := by
      rw [show ⌊x⌋ = 1 by omega] at h1
      linarith
    linarith
  have h16 : x = 1 + 43 / 57 := by
    linarith [h15]
  exact h16