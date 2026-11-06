import Mathlib

theorem algebra_197905 (x : ℝ) (hx : x ≠ 0) : 3 * x ^ 3 - ⌊x⌋ = 3 ↔
    x = (4 / 3) ^ ((1 : ℝ) / 3) := by
  constructor
  · -- Assume 3 * x ^ 3 - ⌊x⌋ = 3, prove x = (4 / 3) ^ ((1 : ℝ) / 3).
    intro h
    let n := ⌊x⌋
    have hn1 : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast (Int.floor_le x)
    have hn2 : (x : ℝ) < (↑n + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one x)
    have h_eq : (3 * x ^ 3 : ℝ) - (↑n : ℝ) = 3 := by
      simpa using h
    have eq1 : 3 * x ^ 3 = 3 + (↑n : ℝ) := by linarith
    have eq2 : x ^ 3 = 1 + (↑n / (3 : ℝ) : ℝ) := by
      nlinarith
    have hn3 : n = 1 := by
      have hn31 : n ≤ 1 := by
        by_contra h
        push_neg at h
        have h4 : n ≥ 2 := by omega
        have h5 : (↑n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h4
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1), sq_nonneg (x - (2 : ℝ)), sq_nonneg (x - (1.5 : ℝ)), sq_nonneg (x ^ 2 - (4 / 9)), sq_nonneg (x * x * x - (1 + (2/3 : ℝ)) ), sq_nonneg (x ^ 2 - 2) ]
      have hn32 : n ≥ 1 := by
        by_contra h
        push_neg at h
        have h4 : n ≤ 0 := by omega
        have h5 : (↑n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h4
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1), sq_nonneg (x + (0.5 : ℝ)), sq_nonneg (x - (0.5 : ℝ)), sq_nonneg (x * x * x - (1 : ℝ)), sq_nonneg (x ^ 2 - 1) ]
      have hn33 : n = 1 := by omega
      exact_mod_cast hn33
    have h7 : (↑n : ℝ) = (1 : ℝ) := by exact_mod_cast hn3
    have h_eq2 : x ^ 3 = (4 / 3 : ℝ) := by
      rw [h7] at eq2
      linarith
    have h_eq3 : x = ( (4 / 3 : ℝ ) ) ^ ((1 : ℝ) / 3) := by
      have h_eq4 : x ^ 3 = (4 / 3 : ℝ) := h_eq2
      have h_eq5 : x = (x ^ 3) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      rw [h_eq4] at h_eq5
      rw [h_eq5]
      all_goals norm_num
    exact_mod_cast h_eq3
  · -- The converse.
    intro h_eq
    have h1 : x = ( (4 / 3 : ℝ ) ) ^ ((1 : ℝ) / 3) := h_eq
    have h2 : x ^ 3 = (4 / 3 : ℝ) := by
      rw [h1]
      have h3 : (( (4 / 3 : ℝ ) ) ^ ((1 : ℝ) / 3) ) ^ 3 = (4 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      linarith
    have h3 : ⌊x⌋ = 1 := by
      have h4 : 1 ≤ (x : ℝ) := by
        by_contra h
        push_neg at h
        have h11 : x < (1 : ℝ) := by nlinarith
        nlinarith [sq_nonneg (x ^ 2 - (1 : ℝ)), sq_nonneg (x - (1 : ℝ)), sq_nonneg (x^3 - (4 / 3 : ℝ)), sq_nonneg (x * x * x - (4 / 3 : ℝ)), sq_nonneg (x ^ 2 - (1 : ℝ)), sq_nonneg (x * 1), sq_nonneg (x -0) ]
      have h5 : (x : ℝ) < (2 : ℝ) := by
        by_contra h
        push_neg at h
        have h11 : x ≥ (2 : ℝ) := by nlinarith
        nlinarith [sq_nonneg (x ^ 2 - (4 : ℝ)), sq_nonneg (x - (1.5 : ℝ)), sq_nonneg (x ^ 3 - (8 : ℝ)), sq_nonneg (x * x * x * x * x - 0), sq_nonneg (x - 2), sq_nonneg (x ^ 2 - 4), sq_nonneg (x * 4 - 4) ]
      have hn4 : ⌊x⌋ = 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      exact_mod_cast hn4
    have hn1 : (↑⌊x⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h3
    rw [hn1]
    linarith [h2]