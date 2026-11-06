import Mathlib

theorem algebra_168625 (x : ℝ) (hx : ⌊2 * x⌋ + ⌊3 * x⌋ = 8 * x - 7 / 2) :
    x = 13 / 16 ∨ x = 17 / 16 := by
  let n := ⌊2 * x⌋
  let m := ⌊3 * x⌋
  have h1 : (n : ℝ) ≤ 2 * x := by exact Int.floor_le (2 * x)
  have h2 : 2 * x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one (2 * x)
  have h3 : (m : ℝ) ≤ 3 * x := by exact Int.floor_le (3 * x)
  have h4 : 3 * x < (m + 1 : ℝ) := by exact Int.lt_floor_add_one (3 * x)
  have h5 : (n : ℝ) + (m : ℝ) = 8 * x - 7 / 2 := by
    exact_mod_cast (show (n + m : ℝ) = (8 * x - 7 / 2 : ℝ) by exact_mod_cast hx)
  have h6 : x = ( (n : ℝ) + (m : ℝ) ) / 8 + 7 / 16 := by
    linarith
  have h7' : 6 * n ≤ 2 * m + 7 := by
    have h7 : 6 * (n : ℝ) ≤ 2 * (m : ℝ) + 7 := by
      have h8 : (n : ℝ) ≤ 2 * x := h1
      rw [h6] at h8
      nlinarith
    exact_mod_cast h7
  have h8' : 2 * m + 7 < 6 * n + 8 := by
    have h8 : 2 * (m : ℝ) + 7 < 6 * (n : ℝ) + 8 := by
      have h9 : 2 * x < (n + 1 : ℝ) := h2
      rw [h6] at h9
      nlinarith
    exact_mod_cast h8
  have h9' : 10 * m ≤ 6 * n + 21 := by
    have h9 : 10 * (m : ℝ) ≤ 6 * (n : ℝ) + 21 := by
      have h10 : (m : ℝ) ≤ 3 * x := h3
      rw [h6] at h10
      nlinarith
    exact_mod_cast h9
  have h10' : 6 * n + 21 < 10 * m + 16 := by
    have h10 : 6 * (n : ℝ) + 21 < 10 * (m : ℝ) + 16 := by
      have h11 : 3 * x < (m + 1 : ℝ) := h4
      rw [h6] at h11
      nlinarith
    exact_mod_cast h10
  have hn1 : n = 1 ∨ n = 2 := by
    omega
  rcases hn1 with hn1 | hn1
  · -- n = 1
    have hm1 : m = 2 := by
      rw [show n = 1 by omega] at h7' h8' h9' h10'
      omega
    have hx13 : x = (13 / 16 : ℝ) := by
      have hm10 : (m : ℝ) = (2 : ℝ) := by
        exact_mod_cast show m = 2 by omega
      have hn10 : (n : ℝ) = (1 : ℝ) := by
        exact_mod_cast show n = 1 by omega
      nlinarith [h6, hn10, hm10]
    left
    linarith
  · -- n = 2
    have hm2 : m = 3 := by
      rw [show n = 2 by omega] at h7' h8' h9' h10'
      omega
    have hx17 : x = (17 / 16 : ℝ) := by
      have hm20 : (m : ℝ) = (3 : ℝ) := by
        exact_mod_cast show m = 3 by omega
      have hn20 : (n : ℝ) = (2 : ℝ) := by
        exact_mod_cast show n = 2 by omega
      nlinarith [h6, hn20, hm20]
    right
    linarith