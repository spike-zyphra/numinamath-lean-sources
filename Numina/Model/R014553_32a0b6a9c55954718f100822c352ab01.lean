import Mathlib

theorem algebra_273293 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h₁ : ⌊x⌋ * x = 36) (h₂ : ⌊y⌋ * y = 71) :
    x + y = 119 / 8 := by

  have h3 : ⌊x⌋ ≤ (x : ℝ) := by
    exact Int.floor_le x

  have h4 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
    exact Int.lt_floor_add_one x

  have h5 : ⌊x⌋ = 6 := by
    have h6 : ⌊x⌋ ≤ 6 := by
      by_contra h
      push_neg at h
      have h7 : ⌊x⌋ ≥ 7 := by omega
      have h8 : (⌊x⌋ : ℝ) ≥ 7 := by exact_mod_cast h7
      nlinarith
    have h7 : ⌊x⌋ ≥ 6 := by
      by_contra h
      push_neg at h
      have h8 : ⌊x⌋ ≤ 5 := by omega
      have h9 : (⌊x⌋ : ℝ) ≤ 5 := by exact_mod_cast h8
      nlinarith
    omega

  have hx6 : x = 6 := by
    have h7 : (⌊x⌋ : ℝ) = 6 := by exact_mod_cast h5
    rw [h7] at h₁
    nlinarith

  have h7 : ⌊y⌋ = 8 := by
    have h8 : ⌊y⌋ ≤ (y : ℝ) := by
      exact Int.floor_le y
    have h9 : (y : ℝ) < (⌊y⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one y
    have h10 : ⌊y⌋ ≤ 8 := by
      by_contra h
      push_neg at h
      have h7 : ⌊y⌋ ≥ 9 := by omega
      have h8 : (⌊y⌋ : ℝ) ≥ 9 := by exact_mod_cast h7
      nlinarith
    have h11 : ⌊y⌋ ≥ 8 := by
      by_contra h
      push_neg at h
      have h12 : ⌊y⌋ ≤ 7 := by omega
      have h13 : (⌊y⌋ : ℝ) ≤ 7 := by exact_mod_cast h12
      nlinarith
    omega

  have hy718 : y = 71 / 8 := by
    have h7 : (⌊y⌋ : ℝ) = 8 := by exact_mod_cast h7
    rw [h7] at h₂
    nlinarith

  rw [hx6, hy718]
  all_goals norm_num