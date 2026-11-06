import Mathlib

open Real


theorem algebra_296357 {x y z : ℕ} (hx : 2 ^ x > 1) (hy : 3 ^ y > 1) (hz : 5 ^ z > 1)
    (h : 2 ^ x = 3 ^ y ∧ 3 ^ y = 5 ^ z) :
    3 * y < 2 * x ∧ 2 * x < 5 * z := by
  rcases h with ⟨h1, h2⟩
  have h3 : 2 ^ x = 3 ^ y := h1
  have h4 : 3 ^ y = 5 ^ z := h2
  have h5 : x > 0 := by
    by_contra h
    push_neg at h
    have h6 : x = 0 := by
      omega
    rw [h6] at h3
    have h7 : 2 ^ (0 : ℕ) = 1 := by
      norm_num
    rw [h7] at h3
    omega
  have h6 : y > 0 := by
    by_contra h
    push_neg at h
    have h7 : y = 0 := by
      omega
    rw [h7] at h3
    have h8 : 3 ^ (0 : ℕ) = 1 := by
      norm_num
    rw [h8] at h3
    omega
  have h7 : z > 0 := by
    by_contra h
    push_neg at h
    have h8 : z = 0 := by
      omega
    rw [h8] at h4
    have h9 : 5 ^ (0 : ℕ) = 1 := by
      norm_num
    rw [h9] at h4
    omega

  have h8 : (2 : ℝ) ^ (x : ℝ) = (3 : ℝ) ^ (y : ℝ) := by
    have h9 : (2 ^ x : ℝ) = (3 ^ y : ℝ) := by
      exact_mod_cast h3
    have h10 : (2 ^ x : ℝ) = (2 : ℝ) ^ (x : ℝ) := by
      simp
    have h11 : (3 ^ y : ℝ) = (3 : ℝ) ^ (y : ℝ) := by
      simp
    rw [h10, h11] at h9
    linarith

  have h9 : (3 : ℝ) ^ (y : ℝ) = (5 : ℝ) ^ (z : ℝ) := by
    have h10 : (3 ^ y : ℝ) = (5 ^ z : ℝ) := by
      exact_mod_cast h4
    have h11 : (3 ^ y : ℝ) = (3 : ℝ) ^ (y : ℝ) := by
      simp
    have h12 : (5 ^ z : ℝ) = (5 : ℝ) ^ (z : ℝ) := by
      simp
    rw [h11, h12] at h10
    linarith

  have h12 : (x : ℝ) * (Real.log (2 : ℝ)) = (y : ℝ) * (Real.log (3 : ℝ)) := by
    have h13 : Real.log ((2 : ℝ) ^ (x : ℝ)) = Real.log ((3 : ℝ) ^ (y : ℝ)) := by
      rw [h8]
    have h14 : Real.log ((2 : ℝ) ^ (x : ℝ)) = (x : ℝ) * Real.log (2 : ℝ) := by
      rw [Real.log_rpow]
      all_goals
        linarith
    have h15 : Real.log ((3 : ℝ) ^ (y : ℝ)) = (y : ℝ) * Real.log (3 : ℝ) := by
      rw [Real.log_rpow]
      all_goals
        linarith
    linarith [h13, h14, h15]

  have h13 : (y : ℝ) * (Real.log (3 : ℝ)) = (z : ℝ) * (Real.log (5 : ℝ)) := by
    have h14 : Real.log ((3 : ℝ) ^ (y : ℝ)) = Real.log ((5 : ℝ) ^ (z : ℝ)) := by
      rw [h9]
    have h15 : Real.log ((3 : ℝ) ^ (y : ℝ)) = (y : ℝ) * Real.log (3 : ℝ) := by
      rw [Real.log_rpow]
      all_goals
        linarith
    have h16 : Real.log ((5 : ℝ) ^ (z : ℝ)) = (z : ℝ) * Real.log (5 : ℝ) := by
      rw [Real.log_rpow]
      all_goals
        linarith
    linarith [h14, h15, h16]

  have h14 : 0 < (2 : ℝ) := by norm_num
  have h15 : 0 < (3 : ℝ) := by norm_num
  have h16 : 0 < (5 : ℝ) := by norm_num
  have h17 : Real.log (2 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals
      norm_num
  have h18 : Real.log (3 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals
      norm_num
  have h19 : Real.log (5 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals
      norm_num

  have h20 : (3 : ℝ) * (y : ℝ) < (2 : ℝ) * (x : ℝ) := by
    have h21 : 3 * (Real.log (2 : ℝ)) < 2 * (Real.log (3 : ℝ)) := by
      have h32 : Real.log (8 : ℝ) < Real.log (9 : ℝ) := by
        apply Real.log_lt_log
        all_goals
          norm_num
      have h33 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
        calc
          Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ 3) := by norm_num
          _ = 3 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      have h34 : Real.log (9 : ℝ) = 2 * Real.log (3 : ℝ) := by
        calc
          Real.log (9 : ℝ) = Real.log ((3 : ℝ) ^ 2) := by norm_num
          _ = 2 * Real.log (3 : ℝ) := by simp [Real.log_pow]
      linarith [h32, h33, h34]
    have h23 : (x : ℝ) * (Real.log (2 : ℝ)) = (y : ℝ) * (Real.log (3 : ℝ)) := h12
    nlinarith [h21, h23, show (y : ℝ) > 0 by exact_mod_cast show y > 0 by omega, show (x : ℝ) > 0 by exact_mod_cast show x > 0 by omega]

  have h21 : (2 : ℝ) * (x : ℝ) < (5 : ℝ) * (z : ℝ) := by
    have h22 : 2 * (Real.log (5 : ℝ)) < 5 * (Real.log (2 : ℝ)) := by
      have h32 : Real.log (25 : ℝ) < Real.log (32 : ℝ) := by
        apply Real.log_lt_log
        all_goals
          norm_num
      have h33 : Real.log (25 : ℝ) = 2 * Real.log (5 : ℝ) := by
        calc
          Real.log (25 : ℝ) = Real.log ((5 : ℝ) ^ 2) := by norm_num
          _ = 2 * Real.log (5 : ℝ) := by simp [Real.log_pow]
      have h34 : Real.log (32 : ℝ) = 5 * Real.log (2 : ℝ) := by
        calc
          Real.log (32 : ℝ) = Real.log ((2 : ℝ) ^ 5) := by norm_num
          _ = 5 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      linarith [h32, h33, h34]
    have h23 : (y : ℝ) * (Real.log (3 : ℝ)) = (z : ℝ) * (Real.log (5 : ℝ)) := h13
    nlinarith [h22, h23, show (z : ℝ) > 0 by exact_mod_cast show z > 0 by omega, show (x : ℝ) > 0 by exact_mod_cast show x > 0 by omega, show (y : ℝ) > 0 by exact_mod_cast show y > 0 by omega]

  have h22 : 3 * y < 2 * x := by
    have h23 : (3 * (y : ℝ) : ℝ) < (2 * (x : ℝ) : ℝ) := by
      linarith [h20]
    exact_mod_cast h23

  have h23 : 2 * x < 5 * z := by
    have h24 : (2 * (x : ℝ) : ℝ) < (5 * (z : ℝ) : ℝ) := by
      linarith [h21]
    exact_mod_cast h24

  constructor
  · exact h22
  · exact h23