import Mathlib


theorem algebra_204804 (x : ℝ) :
    x^2 - 8 * ⌊x⌋ + 7 = 0 ↔ x = 1 ∨ x = Real.sqrt 33 ∨ x = Real.sqrt 41 ∨ x = 7 := by
  constructor
  · -- Forward implications: if x^2 - 8[x] + 7 = 0, then x is in the set
    intro h_eq
    let n := ⌊x⌋
    have h1 : (n : ℝ) ≤ x := by exact Int.floor_le x
    have h2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have h3 : x ^ 2 = 8 * (n : ℝ) - 7 := by
      nlinarith
    have h4 : n ≥ 1 := by
      by_contra h
      push_neg at h
      have hn0 : n ≤ 0 := by omega
      have hn0' : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn0
      nlinarith [sq_nonneg (x), sq_nonneg ((n : ℝ) - (0 : ℝ)), sq_nonneg (x), sq_nonneg ((n : ℝ) - (0 : ℝ)), sq_nonneg (x - 0), sq_nonneg ((n : ℝ) - (0 : ℝ)), sq_nonneg (x), sq_nonneg ((n : ℝ) - (0 : ℝ)), sq_nonneg (x - 0), sq_nonneg ((n : ℝ) - (0 : ℝ)), sq_nonneg (x), sq_nonneg ((n : ℝ) - (0 : ℝ)), sq_nonneg (x - 0), sq_nonneg ((n : ℝ) - (0 : ℝ))]
    have h5 : n ≤ 7 := by
      by_contra h
      push_neg at h
      have hn8 : n ≥ 8 := by omega
      have hn8' : (n : ℝ) ≥ (8 : ℝ) := by exact_mod_cast hn8
      nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg ((n : ℝ) - (8 : ℝ)), Real.sqrt_nonneg (8 * (n : ℝ) - 7), Real.sq_sqrt (show (0 : ℝ) ≤ 8 * (n : ℝ) - 7 by nlinarith)]
    have hn1 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hn1 with (r | r | r | r | r | r | r)
    · -- n = 1
      have h11 : (n : ℝ) = (1 : ℝ) := by exact_mod_cast r
      have h_eq1 : x ^ 2 = 8 * (1 : ℝ) - 7 := by
        rw [h11] at h3
        linarith
      have hx1 : x = (1 : ℝ) := by
        nlinarith
      left
      linarith
    · -- n = 2
      have h11 : (n : ℝ) = (2 : ℝ) := by exact_mod_cast r
      have h_eq1 : x ^ 2 = 8 * (2 : ℝ) - 7 := by
        rw [h11] at h3
        linarith
      have hx2 : x^2 = 9 := by
        nlinarith
      have h8 : x ≥ (2 : ℝ) := by
        have h9 : (n : ℝ) ≤ x := h1
        rw [h11] at h9
        nlinarith
      have h9 : x < (3 : ℝ) := by
        have h10 : x < (n + 1 : ℝ) := h2
        rw [h11] at h10
        nlinarith
      nlinarith [sq_nonneg (x - 3)]
    · -- n = 3
      have h11 : (n : ℝ) = (3 : ℝ) := by exact_mod_cast r
      have h_eq1 : x ^ 2 = 8 * (3 : ℝ) - 7 := by
        rw [h11] at h3
        linarith
      have hx2 : x^2 = 17 := by
        nlinarith
      have h8 : x ≥ (3 : ℝ) := by
        have h9 : (n : ℝ) ≤ x := h1
        rw [h11] at h9
        nlinarith
      have h9 : x < (4 : ℝ) := by
        have h10 : x < (n + 1 : ℝ) := h2
        rw [h11] at h10
        nlinarith
      nlinarith [Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), sq_nonneg (x), sq_nonneg ((n : ℝ) - (3 : ℝ)), sq_nonneg (x - (4 : ℝ)), sq_nonneg ((n : ℝ) - (3 : ℝ)), sq_nonneg (x - (4 : ℝ)), sq_nonneg (x ^ 2 - 17)]
    · -- n = 4
      have h11 : (n : ℝ) = (4 : ℝ) := by exact_mod_cast r
      have h_eq1 : x ^ 2 = 8 * (4 : ℝ) - 7 := by
        rw [h11] at h3
        linarith
      have hx2 : x^2 = 25 := by
        nlinarith
      have h8 : x ≥ (4 : ℝ) := by
        have h9 : (n : ℝ) ≤ x := h1
        rw [h11] at h9
        nlinarith
      have h9 : x < (5 : ℝ) := by
        have h10 : x < (n + 1 : ℝ) := h2
        rw [h11] at h10
        nlinarith
      nlinarith [sq_nonneg (x - 5)]
    · -- n = 5
      have h11 : (n : ℝ) = (5 : ℝ) := by exact_mod_cast r
      have h_eq1 : x ^ 2 = 8 * (5 : ℝ) - 7 := by
        rw [h11] at h3
        linarith
      have hx2 : x^2 = (33 : ℝ) := by
        nlinarith
      have h8 : x ≥ (5 : ℝ) := by
        have h9 : (n : ℝ) ≤ x := h1
        rw [h11] at h9
        nlinarith
      have h9 : x < (6 : ℝ) := by
        have h10 : x < (n + 1 : ℝ) := h2
        rw [h11] at h10
        nlinarith
      have h70 : x = Real.sqrt 33 := by
        have h21 : x ≥ 0 := by nlinarith
        have h22 : x ^ 2 = (33 : ℝ) := hx2
        have h33 : x = Real.sqrt (x ^ 2) := by
          rw [Real.sqrt_sq (by linarith)]
        rw [h22] at h33
        linarith
      right
      left
      exact h70
    · -- n = 6
      have h11 : (n : ℝ) = (6 : ℝ) := by exact_mod_cast r
      have h_eq1 : x ^ 2 = 8 * (6 : ℝ) - 7 := by
        rw [h11] at h3
        linarith
      have hx2 : x^2 = (41 : ℝ) := by
        nlinarith
      have h8 : x ≥ (6 : ℝ) := by
        have h9 : (n : ℝ) ≤ x := h1
        rw [h11] at h9
        nlinarith
      have h9 : x < (7 : ℝ) := by
        have h10 : x < (n + 1 : ℝ) := h2
        rw [h11] at h10
        nlinarith
      have h70 : x = Real.sqrt 41 := by
        have h21 : x ≥ 0 := by nlinarith
        have h22 : x ^ 2 = (41 : ℝ) := hx2
        have h33 : x = Real.sqrt (x ^ 2) := by
          rw [Real.sqrt_sq (by linarith)]
        rw [h22] at h33
        linarith
      right
      right
      left
      exact h70
    · -- n = 7
      have h11 : (n : ℝ) = (7 : ℝ) := by exact_mod_cast r
      have h_eq1 : x ^ 2 = 8 * (7 : ℝ) - 7 := by
        rw [h11] at h3
        linarith
      have hx1 : x = (7 : ℝ) := by
        nlinarith
      right
      right
      right
      linarith
  · -- Backward implication: each element in the set satisfies the equation
    rintro (r | r | r | r)
    · -- x = 1
      rw [r]
      norm_num
    · -- x = Real.sqrt 33
      rw [r]
      have h2 : ⌊Real.sqrt 33⌋ = 5 := by
        have h1 : 5 < Real.sqrt 33 := by
          nlinarith [Real.sqrt_nonneg (33 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by linarith)]
        have h2 : Real.sqrt 33 < (6 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (33 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by linarith)]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg (33 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by linarith)]
      norm_num [h2, Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by linarith)]
    · -- x = Real.sqrt 41
      rw [r]
      have h2 : ⌊Real.sqrt 41⌋ = 6 := by
        have h1 : 6 < Real.sqrt 41 := by
          nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by linarith)]
        have h2 : Real.sqrt 41 < (7 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by linarith)]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by linarith)]
      norm_num [h2, Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by linarith)]
    · -- x = 7
      rw [r]
      norm_num