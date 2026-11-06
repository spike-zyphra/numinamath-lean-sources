import Mathlib

theorem algebra_13774 : IsLeast {x : ℝ | ⌊x^2⌋ - ⌊x⌋^2 = 17} (7 * Real.sqrt 2) := by
  constructor
  · -- Show that 7 * Real.sqrt 2 is in the set.
    have h1 : ⌊(7 * Real.sqrt 2 : ℝ) ^ 2⌋ - ⌊(7 * Real.sqrt 2 : ℝ)⌋ ^ 2 = 17 := by
      have h2 : (7 * Real.sqrt 2 : ℝ) ^ 2 = 98 := by
        calc
          (7 * Real.sqrt 2 : ℝ) ^ 2 = 7 ^ 2 * (Real.sqrt 2) ^ 2 := by ring
          _ = 49 * 2 := by norm_num [Real.sq_sqrt]
          _ = 98 := by norm_num

      have h3 : ⌊(7 * Real.sqrt 2 : ℝ)⌋ = 9 := by
        have h4 : 9 ≤ (7 * Real.sqrt 2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 - 14 / 10)]
        have h5 : (7 * Real.sqrt 2 : ℝ) < 10 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 - 10 / 7)]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith

      have h6 : ⌊(7 * Real.sqrt 2 : ℝ) ^ 2⌋ = 98 := by
        rw [h2]
        norm_num [Int.floor_eq_iff]

      rw [h6, h3]
      all_goals norm_num
    exact h1
  · -- Show that 7 * Real.sqrt 2 is the least in the set.
    intro x hx
    have h7 : ⌊x ^ 2⌋ - ⌊x⌋^2 = 17 := by
      simpa using hx
    set n := ⌊x⌋ with hn
    have eq1 : ⌊x ^ 2⌋ = n^2 + 17 := by
      linarith
    have h1 : (n : ℝ) ≤ x := by
      exact Int.floor_le x
    have h2 : x < (n + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have h3 : (n : ℝ) ^ 2 + 17 ≤ x^2 := by
      have h8 : (⌊x ^ 2⌋ : ℝ) ≤ x^2 := by
        exact Int.floor_le (x^2)
      have h9 : (⌊x ^ 2⌋ : ℝ) = (n^2 + 17 : ℝ) := by
        exact_mod_cast eq1
      nlinarith [h8, h9]
    have h4 : n ≥ 9 := by
      by_contra h
      push_neg at h
      have h5 : n ≤ 8 := by
        omega
      have h6 : (n : ℝ) ≤ (8 : ℝ) := by
        exact_mod_cast h5
      have h7 : (n : ℝ) ^ 2 + 17 ≤ x ^ 2 := h3
      have h8 : x < (n + 1 : ℝ) := h2
      have h9 : (n + 1 : ℝ) ≤ (9 : ℝ) := by
        nlinarith [show (n : ℝ) ≤ (8 : ℝ) from by exact_mod_cast h5]
      nlinarith [sq_nonneg (x - (9 : ℝ)), sq_nonneg ((n : ℝ) - (8 : ℝ))]
    have h10 : (n : ℝ) ≥ (9 : ℝ) := by
      have hn9 : n ≥ 9 := h4
      exact_mod_cast hn9
    have h11 : x^2 ≥ (98 : ℝ) := by
      nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg ((n : ℝ) - (9 : ℝ)), h10, h3]
    have h12 : x ≥ (0 : ℝ) := by
      nlinarith [h10, h1, show (n : ℝ) ≥ (0 : ℝ) by nlinarith]
    have h13 : Real.sqrt 98 = 7 * Real.sqrt 2 := by
      calc
        Real.sqrt 98 = Real.sqrt (7^2 * 2) := by norm_num
        _ = (7 : ℝ) * Real.sqrt 2 := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
        _ = 7 * Real.sqrt 2 := by ring
    have h14 : x ≥ Real.sqrt 98 := by
      have h15 : Real.sqrt 98 ≥ 0 := Real.sqrt_nonneg 98
      have h16 : x ^ 2 ≥ (98 : ℝ) := h11
      have h17 : x ≥ 0 := h12
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (98 : ℝ) by norm_num), Real.sqrt_nonneg 98]
    rw [h13] at h14
    linarith