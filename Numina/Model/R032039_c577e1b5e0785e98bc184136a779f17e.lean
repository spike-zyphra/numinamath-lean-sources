import Mathlib

theorem algebra_3952 (x : ℝ) : x^2 = abs x + ⌊x⌋ ↔ x = 0 ∨ x = 2 ∨ x = (1 + Real.sqrt 5) / 2 := by
  constructor
  · -- Assume x^2 = abs x + ⌊x⌋, prove x = 0 ∨ x = 2 ∨ x = (1 + Real.sqrt 5) / 2
    intro h_eq
    let n := ⌊x⌋
    have h1 : (n : ℝ) ≤ x := by exact Int.floor_le x
    have h2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have hn1 : n ≤ (x : ℝ) := by exact_mod_cast h1
    have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact_mod_cast h2
    by_cases h3 : x ≥ 0
    · -- Case x ≥ 0
      have h4 : abs x = x := abs_of_nonneg h3
      rw [h4] at h_eq
      have h5 : (x : ℝ) ^ 2 - (x : ℝ) - (n : ℝ) = 0 := by
        linarith
      have h6 : n ≥ 0 := by
        by_contra h7
        push_neg at h7
        have hn7 : n ≤ (-1 : ℤ) := by omega
        have hn8 : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hn7
        nlinarith
      have h7 : (n : ℝ) ≥ (0 : ℝ) := by exact_mod_cast (show (n : ℤ) ≥ (0 : ℤ) by omega)
      have h8 : x ≥ (n : ℝ) := by linarith
      have h9 : x < (n + 1 : ℝ) := hn2
      have h10 : n ≤ 3 := by
        by_contra h11
        push_neg at h11
        have hn4 : n ≥ 4 := by omega
        have hn5 : (n : ℝ) ≥ (4 : ℝ) := by exact_mod_cast hn4
        nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg (x - 2), sq_nonneg (x - ( (1 : ℝ) + Real.sqrt 5) / 2 ) ]
      have hn0123 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hn0123 with (r | r | r | r)
      · -- Case n = 0
        have hn0 : (n : ℝ) = (0 : ℝ) := by exact_mod_cast r
        rw [hn0] at h5
        have hy : x = (0 : ℝ) := by
          nlinarith [ sq_nonneg (x), h5 ]
        left
        linarith
      · -- Case n = 1
        have hn1' : (n : ℝ) = (1 : ℝ) := by exact_mod_cast r
        rw [hn1'] at h5
        have hy : x = (1 + Real.sqrt 5) / 2 := by
          nlinarith [ Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5 ]
        right
        right
        linarith
      · -- Case n = 2
        have hn2' : (n : ℝ) = (2 : ℝ) := by exact_mod_cast r
        rw [hn2'] at h5
        have hy : x = (2 : ℝ) := by
          nlinarith [ sq_nonneg (x - (2 : ℝ)), h5
          ]
        right
        left
        linarith
      · -- Case n = 3
        have hn3' : (n : ℝ) = (3 : ℝ) := by exact_mod_cast r
        rw [hn3'] at h5
        nlinarith [ sq_nonneg (x - (3 : ℝ)), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num) ]
    · -- Case x < 0
      have h4 : abs x = -x := abs_of_neg (by linarith)
      rw [h4] at h_eq
      have h5 : x ^ 2 + x - (n : ℝ) = 0 := by
        linarith
      have h6 : n < 0 := by
        by_contra h7
        push_neg at h7
        have hn7 : n ≥ 0 := by omega
        have hn8 : (n : ℝ) ≥ (0 : ℝ) := by exact_mod_cast hn7
        nlinarith [ sq_nonneg (x) ]
      have hn7 : n < 0 := h6
      have hn8 : (n : ℝ) < (0 : ℝ) := by exact_mod_cast hn7
      have h12 : (1 : ℝ) + 4 * (n : ℝ) < 0 := by
        nlinarith [ sq_nonneg (x) ]
      nlinarith [ sq_nonneg (x + 1 / 2) ]
  · -- Assume x = 0 ∨ x = 2 ∨ x = (1 + Real.sqrt 5) / 2, prove x^2 = abs x + ⌊x⌋
    rintro (h | h | h)
    · -- x = 0
      rw [h]
      norm_num [abs_zero]
    · -- x = 2
      rw [h]
      norm_num [abs_of_nonneg]
    · -- x = (1 + Real.sqrt 5) / 2
      rw [h]
      have h0 : ( (1 + Real.sqrt 5) / 2 : ℝ) ≥ 0 := by
        nlinarith [ Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
      have h1 : ( (1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = ( (1 + Real.sqrt 5) / 2 : ℝ) + 1 := by
        nlinarith [ Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
      have h2 : ⌊( (1 + Real.sqrt 5) / 2 : ℝ)⌋ = (1 : ℤ) := by
        have h3 : ( (1 + Real.sqrt 5) / 2 : ℝ) > (1 : ℝ) := by
          nlinarith [ Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
        have h4 : ( (1 + Real.sqrt 5) / 2 : ℝ) < (2 : ℝ) := by
          nlinarith [ Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      rw [h2]
      rw [abs_of_nonneg h0]
      nlinarith [ h1, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]