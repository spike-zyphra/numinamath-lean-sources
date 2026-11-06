import Mathlib

theorem algebra_216536 (x : ℝ) :
    x^2 - 6 * ⌊x⌋ + 5 = 0 ↔ x = 1 ∨ x = Real.sqrt 7 ∨ x = Real.sqrt 13 ∨ x = Real.sqrt 19 ∨ x = 5 := by
  constructor
  · -- Assume x^2 - 6*⌊x⌋ + 5 = 0, prove x = 1 ∨ x = Real.sqrt 7 ∨ x = Real.sqrt 13 ∨ x = Real.sqrt 19 ∨ x = 5
    intro h
    let n := ⌊x⌋
    have hn1 : (n : ℝ) ≤ x := by
      exact Int.floor_le x
    have hn2 : x < (n + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have h_eq : x^2 = 6 * (n : ℝ) - 5 := by
      have h1 : (x^2 - 6 * (n : ℝ) + 5 : ℝ) = 0 := by
        simpa using h
      linarith
    have hn3 : n ≥ 1 := by
      by_contra h4
      push_neg at h4
      have hn4 : n ≤ 0 := by omega
      have hn5 : (n : ℝ) ≤ (0 : ℝ) := by
        exact_mod_cast hn4
      nlinarith [sq_nonneg (x), h_eq, hn5, hn1, hn2]
    have h11 : n ≤ 5 := by
      by_contra h4
      push_neg at h4
      have h5 : n ≥ 6 := by
        omega
      have hn6 : (n : ℝ) ≥ (6 : ℝ) := by
        exact_mod_cast h5
      nlinarith [sq_nonneg (x - (n : ℝ)), Real.sqrt_nonneg (6 * (n : ℝ) - 5), Real.sq_sqrt (show (0 : ℝ) ≤ 6 * (n : ℝ) - 5 by nlinarith), sq_nonneg (x - Real.sqrt (6 * (n : ℝ) - 5)), Real.sqrt_nonneg (6 * (n : ℝ) - 5)]
    have eq1 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
      omega
    rcases eq1 with (hn | hn | hn | hn | hn)
    · -- n = 1
      have hn11 : (n : ℝ) = (1 : ℝ) := by
        exact_mod_cast hn
      rw [hn11] at h_eq
      have h11 : x^2 = 1 := by
        nlinarith
      have h12 : x = 1 := by
        nlinarith [sq_nonneg (x - 1), hn1, hn2, h11]
      left
      exact_mod_cast h12
    · -- n = 2
      have hn11 : (n : ℝ) = (2 : ℝ) := by
        exact_mod_cast hn
      rw [hn11] at h_eq
      have h22 : x^2 = 7 := by
        nlinarith
      have hx1 : x = Real.sqrt 7 := by
        have hx11 : x ≥ 0 := by
          nlinarith [hn1, hn2, h22, Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
        have hx22 : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)
        nlinarith [sq_nonneg (x - Real.sqrt 7), Real.sqrt_nonneg 7, hn1, hn2, h22, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      right
      left
      assumption
    · -- n = 3
      have hn11 : (n : ℝ) = (3 : ℝ) := by
        exact_mod_cast hn
      rw [hn11] at h_eq
      have h33 : x^2 = 13 := by
        nlinarith
      have hx1 : x = Real.sqrt 13 := by
        have hx11 : x ≥ 0 := by
          nlinarith [hn1, hn2, h33, Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
        have hx22 : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)
        nlinarith [sq_nonneg (x - Real.sqrt 13), Real.sqrt_nonneg 13, hn1, hn2, h33, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
      right
      right
      left
      assumption
    · -- n = 4
      have hn11 : (n : ℝ) = (4 : ℝ) := by
        exact_mod_cast hn
      rw [hn11] at h_eq
      have h44 : x^2 = 19 := by
        nlinarith
      have hx1 : x = Real.sqrt 19 := by
        have hx11 : x ≥ 0 := by
          nlinarith [hn1, hn2, h44, Real.sqrt_nonneg 19, Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num)]
        have hx22 : (Real.sqrt 19) ^ 2 = 19 := Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num)
        nlinarith [sq_nonneg (x - Real.sqrt 19), Real.sqrt_nonneg 19, hn1, hn2, h44, Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num)]
      right
      right
      right
      left
      assumption
    · -- n = 5
      have hn11 : (n : ℝ) = (5 : ℝ) := by
        exact_mod_cast hn
      rw [hn11] at h_eq
      have h55 : x^2 = 25 := by
        nlinarith
      have h555 : x = 5 := by
        nlinarith [sq_nonneg (x - 5), hn1, hn2, Real.sqrt_nonneg 25, Real.sq_sqrt (show (0 : ℝ) ≤ (25 : ℝ) by norm_num)]
      right
      right
      right
      right
      assumption
  · -- Assume x = 1 ∨ x = Real.sqrt 7 ∨ x = Real.sqrt 13 ∨ x = Real.sqrt 19 ∨ x = 5, prove x^2 -6*⌊x⌋ +5=0.
    rintro (h | h | h | h | h)
    · -- x = 1
      rw [h]
      norm_num [Int.floor_eq_iff]
    · -- x = Real.sqrt 7
      rw [h]
      have hn1 : ⌊Real.sqrt 7⌋ = 2 := by
        have h11 : 2 < Real.sqrt 7 := by
          rw [Real.lt_sqrt] <;> norm_num
        have h12 : Real.sqrt 7 < (3 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        have h13 : ⌊Real.sqrt 7⌋ = 2 := by
          simp [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
        exact_mod_cast h13
      norm_num [hn1, Real.sq_sqrt]
    · -- x = Real.sqrt 13
      rw [h]
      have hn1 : ⌊Real.sqrt 13⌋ = 3 := by
        have h11 : 3 < Real.sqrt 13 := by
          rw [Real.lt_sqrt] <;> norm_num
        have h12 : Real.sqrt 13 < (4 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        have h13 : ⌊Real.sqrt 13⌋ = 3 := by
          simp [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
        exact_mod_cast h13
      norm_num [hn1, Real.sq_sqrt]
    · -- x = Real.sqrt 19
      rw [h]
      have hn1 : ⌊Real.sqrt 19⌋ = 4 := by
        have h11 : 4 < Real.sqrt 19 := by
          rw [Real.lt_sqrt] <;> norm_num
        have h12 : Real.sqrt 19 < (5 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        have h13 : ⌊Real.sqrt 19⌋ = 4 := by
          simp [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg 19, Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num)]
        exact_mod_cast h13
      norm_num [hn1, Real.sq_sqrt]
    · -- x = 5
      rw [h]
      norm_num [Int.floor_eq_iff]