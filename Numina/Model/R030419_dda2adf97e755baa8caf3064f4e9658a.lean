import Mathlib

theorem algebra_145997 (x : ℝ) : 3 * x ^ 3 - ⌊x⌋ = 3 ↔
    x = (4 / 3) ^ ((1 : ℝ) / 3) := by
  constructor
  · -- Assume 3 * x ^ 3 - ⌊x⌋ = 3, prove x = (4 / 3) ^ ((1 : ℝ) / 3)
    intro h
    set n := ⌊x⌋ with hn
    have hn1 : n ≤ (x : ℝ) := by exact_mod_cast Int.floor_le x
    have hn2 : x < (n + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one x
    have hn3 : (n : ℝ) ≤ x := by exact_mod_cast hn1
    have h_eq : (3 * x ^ 3 : ℝ) - (n : ℝ) = 3 := by
      simpa using h
    have h_eq1 : (3 * x ^ 3 : ℝ) = (n + 3 : ℝ) := by linarith
    have h1 : n = 1 := by
      by_contra h1
      push_neg at h1
      have : n < 1 ∨ n > 1 := by omega
      rcases this with (h1 | h1)
      · -- n < 1, so n ≤ 0
        have hn3 : n ≤ 0 := by omega
        have hn4 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn3
        nlinarith [sq_nonneg ((x - 1 : ℝ) ^ 2), sq_nonneg (x ^ 2), sq_nonneg ((x - 1.5) ^ 2), sq_nonneg (x ^ 2 - 1.3333), sq_nonneg (x - 1)]
      · -- n > 1, so n ≥ 2
        have hn4 : n ≥ 2 := by omega
        have hn5 : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hn4
        nlinarith [sq_nonneg ((x - 1 : ℝ) ^ 2), sq_nonneg (x ^ 2), sq_nonneg ((x - 1.5) ^ 2), sq_nonneg (x ^ 2 - 1.3333), sq_nonneg (x - 2)]
    have h2 : (3 * x ^ 3 : ℝ) = 4 := by
      have hn4 : (n : ℝ) = 1 := by exact_mod_cast h1
      linarith [h_eq1, hn4]
    have h3 : x ^ 3 = (4 / 3 : ℝ) := by
      linarith
    have h4 : x = (4 / 3 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h5 : x ^ 3 = (4 / 3 : ℝ) := h3
      have h6 : x = ((x ^ 3) : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        field_simp
        all_goals linarith
      rw [h3] at h6
      linarith
    exact h4
  · -- Assume x = (4 / 3) ^ ((1 : ℝ) / 3), prove 3 * x ^ 3 - ⌊x⌋ = 3
    intro h
    have h1 : x ^ 3 = (4 / 3 : ℝ) := by
      rw [h]
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h2 : ⌊x⌋ = 1 := by
      have h3 : 1 < x := by
        nlinarith [sq_nonneg ((x - 1 : ℝ) ^ 2), sq_nonneg (x ^ 2), sq_nonneg ((x - 1.5) ^ 2), sq_nonneg (x ^ 2 - 1.3333)]
      have h4 : x < (2 : ℝ) := by
        nlinarith [sq_nonneg ((x - 2 : ℝ) ^ 2), sq_nonneg (x ^ 2), sq_nonneg ((x - 1.5) ^ 2), sq_nonneg (x ^ 2 - 1.3333)]
      have hn1 : ⌊x⌋ = 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      exact_mod_cast hn1
    have h3 : (3 * x ^ 3 : ℝ) - (⌊x⌋ : ℝ) = 3 := by
      have hn1 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h2
      have h4 : (3 * x ^ 3 : ℝ) = (4 : ℝ) := by linarith [h1]
      rw [hn1]
      linarith [h4]
    simpa using h3