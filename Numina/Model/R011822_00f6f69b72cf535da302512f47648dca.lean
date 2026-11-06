import Mathlib
open Real Complex  
noncomputable section

lemma sqrt_floor_eq {x : ℝ} {z : ℤ} (hx : x ≥ 0) (hz : z ≥ 0)
    (h_bounds : z^2 ≤ x ∧ x < (z + 1)^2) :
    (Int.floor (sqrt x) : ℝ) = z := by
  
  have h_sqrt_bounds : sqrt (z^2) ≤ sqrt x ∧ sqrt x < sqrt ((z + 1)^2) := by
    split_ands
    · exact Real.sqrt_le_sqrt (by nlinarith : z^2 ≤ x)
    · exact Real.sqrt_lt_sqrt hx (by nlinarith : x < (z + 1)^2)
  have h_z_sqrt : sqrt (z^2) = z := by
    rw [sqrt_sq]
    exact_mod_cast hz
  have h_z_plus_one_sqrt : sqrt ((z + 1)^2) = z + 1 := by
    rw [sqrt_sq]
    exact_mod_cast add_nonneg hz zero_le_one
  have h_z_plus_one_cast : (z + 1 : ℝ) = z + 1 := by norm_num
  rw [h_z_sqrt, h_z_plus_one_sqrt, h_z_plus_one_cast] at h_sqrt_bounds
  
  exact_mod_cast Int.floor_eq_iff.mpr h_sqrt_bounds

theorem algebra_212345 :
  ∀ x : ℝ, x^2 - 8 * (Int.floor x : ℝ) + 7 = 0 ↔ x = 1 ∨ x = Real.sqrt 33 ∨ x = Real.sqrt 41 ∨ x = 7 := by
  intro x 
  constructor
  · -- Assume x^2 - 8 * floor(x) + 7 = 0.
    intro h_eq
    have h_eq2 : (x)^2 = 8 * (Int.floor x : ℝ) - 7 := by
      nlinarith 
    have h1 : Int.floor x ≤ x := by
      exact Int.floor_le x 
    have h2 : x < (Int.floor x + 1 : ℝ) := by
      exact Int.lt_floor_add_one x 
    let n := Int.floor x
    have hn1 : n ≥ 1 := by
      by_contra h
      push_neg at h
      have hn0 : n ≤ 0 := by omega 
      have hn0' : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn0
      nlinarith [show (x) ^ 2 ≥ 0 by nlinarith, h_eq2, Real.sqrt_nonneg (x ^ 2)]
    have hn2 : n ≤ 7 := by
      by_contra h
      push_neg at h 
      have hn8 : n ≥ 8 := by omega
      have hn8' : (n : ℝ) ≥ (8 : ℝ) := by exact_mod_cast hn8
      nlinarith [show (x) ^ 2 ≥ 0 by nlinarith, h_eq2, Real.sqrt_nonneg (x ^ 2)]
    have h5 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega 
    rcases h5 with h5 | h5 | h5 | h5 | h5 | h5 | h5 
    · -- Case 1: n = 1 
      have hn1' : n = 1 := by
        omega 
      have hn6 : (n : ℝ) = (1 : ℝ) := by 
        exact_mod_cast h5
      have hx2 : (x)^2 = 1 := by 
        nlinarith
      have hx1 : x = 1 := by
        nlinarith
      left 
      exact hx1
    · -- Case 2: n = 2 
      have hn1' : n = 2 := by
        omega 
      have hn6 : (n : ℝ) = (2 : ℝ) := by 
        exact_mod_cast h5 
      have hx3 : (x)^2 = 9 := by 
        nlinarith 
      have hx1 : x = 3 := by 
        nlinarith 
      exfalso 
      nlinarith 
    · -- Case 3: n = 3 
      have hn1' : n = 3 := by
        omega 
      have hn6 : (n : ℝ) = (3 : ℝ) := by 
        exact_mod_cast h5 
      have hx3 : (x)^2 = 17 := by 
        nlinarith 
      have h6 : x = Real.sqrt 17 ∨ x = -Real.sqrt 17 := by 
        have h7 : (x - Real.sqrt 17) * (x + Real.sqrt 17) = 0 := by 
          nlinarith [Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h7) with h8 h9 
        · -- Case 1: x - sqrt 17 = 0 
          left 
          linarith 
        · --  x + sqrt 17 = 0 
          right 
          nlinarith 
      cases h6 with 
      | inl hx4 =>
        exfalso 
        nlinarith [Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num)]
      | inr hx4 =>
        exfalso 
        nlinarith [Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num)]
    · -- Case 4: n = 4 
      have hn1' : n = 4 := by
        omega 
      have hn6 : (n : ℝ) = (4 : ℝ) := by 
        exact_mod_cast h5 
      have hx3 : (x)^2 = 25 := by 
        nlinarith 
      have h6 : x = 5 ∨ x = -5 := by 
        have h7 : (x - 5) * (x + 5) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h7) with h8 h9 
        · -- Case 1: x - 5 = 0 
          left
          linarith 
        · -- Case 2: x + 5 = 0 
          right 
          nlinarith 
      cases h6 with 
      | inl hx4 =>
        exfalso 
        nlinarith [Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num)]
      | inr hx4 =>
        exfalso 
        nlinarith [Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num)]
    · -- Case 5: n = 5 
      have hn1' : n = 5 := by
        omega 
      have hn6 : (n : ℝ) = (5 : ℝ) := by 
        exact_mod_cast h5 
      have hx3 : (x)^2 = 33 := by 
        nlinarith 
      have h6 : x = Real.sqrt 33 ∨ x = -Real.sqrt 33 := by 
        have h7 : (x - Real.sqrt 33) * (x + Real.sqrt 33) = 0 := by 
          nlinarith [Real.sqrt_nonneg (33 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h7) with h8 h9 
        · -- Case 1: x - sqrt 33 = 0 
          left 
          linarith 
        · -- Case 2: x + sqrt 33 = 0 
          right 
          nlinarith 
      cases h6 with 
      | inl hx4 =>
        right 
        left 
        exact hx4 
      | inr hx4 =>
        exfalso 
        nlinarith [Real.sqrt_nonneg (33 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num)]
    · -- Case 6: n = 6 
      have hn1' : n = 6 := by
        omega 
      have hn6 : (n : ℝ) = (6 : ℝ) := by 
        exact_mod_cast h5 
      have hx3 : (x)^2 = 41 := by 
        nlinarith 
      have h6 : x = Real.sqrt 41 ∨ x = -Real.sqrt 41 := by 
        have h7 : (x - Real.sqrt 41) * (x + Real.sqrt 41) = 0 := by 
          nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h7) with h8 h9 
        · -- Case 1: x - sqrt 41 = 0 
          left 
          linarith 
        · -- Case 2: x + sqrt 41 = 0 
          right 
          nlinarith 
      cases h6 with 
      | inl hx4 =>
        right 
        right 
        left 
        exact hx4 
      | inr hx4 =>
        exfalso 
        nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (41 : ℝ) by norm_num)]
    · -- Case 7: n = 7 
      have hn1' : n = 7 := by
        omega 
      have hn6 : (n : ℝ) = (7 : ℝ) := by 
        exact_mod_cast h5 
      have hx3 : (x)^2 = 49 := by 
        nlinarith 
      have h6 : x = 7 ∨ x = -7 := by 
        have h7 : (x - 7) * (x + 7) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h7) with h8 h9 
        · -- Case 1: x - 7 = 0 
          left 
          linarith 
        · --  x + 7 = 0 
          right 
          nlinarith 
      cases h6 with 
      | inl hx4 =>
        right 
        right 
        right 
        exact hx4 
      | inr hx4 =>
        exfalso 
        nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (41 : ℝ) by norm_num)]
  · -- Show that the right side implies the left side
    intro h 
    rcases h with (r | r | r | r)
    · -- Case 1: x = 1 
      rw [show x = (1 : ℝ) by exact r]
      norm_num 
    · -- Case 2: x = Real.sqrt 33
      rw [show x = Real.sqrt 33 by exact r]
      have h5 : Int.floor (Real.sqrt 33) = 5 := by 
        have h1 : 5 < Real.sqrt 33 := by 
          nlinarith [Real.sqrt_nonneg (33 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
        have h2 : Real.sqrt 33 < (6 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg (33 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith 
      norm_num [h5] at *
      all_goals nlinarith [Real.sqrt_nonneg (33 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
    · -- Case 3: x = Real.sqrt 41
      rw [show x = Real.sqrt 41 by exact r]
      have h5 : Int.floor (Real.sqrt 41) = 6 := by 
        have h1 : 6 < Real.sqrt 41 := by 
          nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by norm_num)]
        have h2 : Real.sqrt 41 < (7 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by norm_num)]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith 
      norm_num [h5] at *
      all_goals nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (41 : ℝ) by norm_num)]
    · -- Case 4: x = 7 
      rw [show x = (7 : ℝ) by exact r]
      norm_num