import Mathlib

open Real

theorem algebra_113930 {x : ℤ} (hx : x ≠ 7) :
    ∃ n : ℤ, (sqrt ((1 - sqrt 3)^2) + sqrt ((sqrt 3 - sqrt 5)^2) +
      sqrt ((1 - sqrt 2)^2) + sqrt (14 - 6 * sqrt 5) + sqrt (6 - 4 * sqrt 2)) / (x - 7) = n ↔
    x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 10 := by
  have h1 : sqrt ((1 - sqrt 3) ^ 2) = sqrt 3 - 1 := by
    have h2 : sqrt ((1 - sqrt 3) ^ 2) = |1 - sqrt 3| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h2]
    have h3 : 1 < sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
    have h4 : (1 : ℝ) - sqrt 3 < 0 := by linarith
    rw [abs_of_neg h4]
    all_goals linarith
  have h2 : sqrt ((sqrt 3 - sqrt 5) ^ 2) = sqrt 5 - sqrt 3 := by
    have h2 : sqrt ((sqrt 3 - sqrt 5) ^ 2) = |sqrt 3 - sqrt 5| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h2]
    have h3 : sqrt 3 < sqrt 5 := by
      apply Real.sqrt_lt_sqrt
      all_goals linarith
    have h4 : sqrt 3 - sqrt 5 < 0 := by linarith
    rw [abs_of_neg h4]
    all_goals linarith
  have h3 : sqrt ((1 - sqrt 2) ^ 2) = sqrt 2 - 1 := by
    have h2 : sqrt ((1 - sqrt 2) ^ 2) = |1 - sqrt 2| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h2]
    have h3 : 1 < sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
    have h4 : (1 : ℝ) - sqrt 2 < 0 := by linarith
    rw [abs_of_neg h4]
    all_goals linarith
  have h4 : sqrt (14 - 6 * sqrt 5) = 3 - sqrt 5 := by
    have h8 : sqrt (14 - 6 * sqrt 5) = sqrt ((3 - sqrt 5) ^ 2) := by
      rw [show (14 - 6 * sqrt 5 : ℝ) = (3 - sqrt 5) ^ 2 by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
      ]
    rw [h8]
    have h9 : sqrt ((3 - sqrt 5) ^ 2) = |3 - sqrt 5| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h9]
    have h6 : sqrt 5 < (3 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith), Real.sqrt_nonneg 5]
    have h11 : (3 : ℝ) - sqrt 5 > 0 := by linarith
    rw [abs_of_pos h11]
    all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
  have h5 : sqrt (6 - 4 * sqrt 2) = 2 - sqrt 2 := by
    have h8 : sqrt (6 - 4 * sqrt 2) = sqrt ((2 - sqrt 2) ^ 2) := by
      rw [show (6 - 4 * sqrt 2 : ℝ) = (2 - sqrt 2) ^ 2 by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
      ]
    rw [h8]
    have h9 : sqrt ((2 - sqrt 2) ^ 2) = |2 - sqrt 2| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h9]
    have h6 : sqrt 2 < (2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith), Real.sqrt_nonneg 2]
    have h11 : (2 : ℝ) - sqrt 2 > 0 := by linarith
    rw [abs_of_pos h11]
    all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
  have h6 : sqrt ((1 - sqrt 3)^2) + sqrt ((sqrt 3 - sqrt 5)^2) +
      sqrt ((1 - sqrt 2)^2) + sqrt (14 - 6 * sqrt 5) + sqrt (6 - 4 * sqrt 2) = (3 : ℝ) := by
    rw [h1, h2, h3, h4, h5]
    all_goals
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
  use 3 / (x - 7)
  constructor
  · -- Assume that E(x) = n, prove that x ∈ {4, 6, 8, 10}
    intro h
    have hx8 : x - 7 ≠ 0 := by
      omega
    have hx4 : (x : ℝ) - 7 ≠ 0 := by
      exact_mod_cast show (x : ℝ) - 7 ≠ 0 by
        exact_mod_cast hx8
    have hx0 : (sqrt ((1 - sqrt 3)^2) + sqrt ((sqrt 3 - sqrt 5)^2) +
        sqrt ((1 - sqrt 2)^2) + sqrt (14 - 6 * sqrt 5) + sqrt (6 - 4 * sqrt 2)) / (x - 7) = (3 / (x - 7) : ℝ) := by
      rw [h6]
      <;> field_simp [show (x - 7 : ℝ) ≠ 0 by exact_mod_cast hx8]
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
    rw [hx0] at h
    have h7 : (x - 7 : ℤ) ∣ 3 := by
      have eq1 : (3 / (x - 7 : ℝ)) * ((x - 7 : ℝ)) = (3 : ℝ) := by
        have h7 : (x - 7 : ℝ) ≠ 0 := by
          exact_mod_cast show (x - 7 : ℤ) ≠ 0 by omega
        field_simp [h7]
        all_goals nlinarith
      have eq2 : (3 / (x - 7 : ℝ)) * ((x - 7 : ℝ)) = (↑(3 / (x - 7 : ℤ)) ) * ((x - 7 : ℝ) ) := by
        have eq3 : (3 / (x - 7 : ℝ) ) = (↑(3 / (x - 7 : ℤ)) : ℝ ) := by
          linarith [h]
        rw [eq3]
        all_goals nlinarith
      have eq3 : (3 : ℝ) = (↑(3 / (x - 7 : ℤ)) ) * ((x - 7 : ℝ) ) := by
        linarith [eq1, eq2]
      have eq4 : (3 : ℤ) = (3 / (x - 7 : ℤ) ) * (x - 7 : ℤ) := by
        have h11 : (3 : ℝ) = (↑(3 / (x - 7 : ℤ)) ) * ((x - 7 : ℝ) ) := eq3
        norm_cast at h11 ⊢
        all_goals nlinarith
      use (3 / (x - 7 : ℤ) )
      all_goals
        linarith [eq4]
    have hx11 : (x - 7) = 1 ∨ (x - 7) = 3 ∨ (x - 7) = -1 ∨ (x - 7) = -3 := by
      have h8 : (x - 7 : ℤ) ∣ 3 := h7
      have h9 : (x - 7 : ℤ) ≤ 3 := by
        apply Int.le_of_dvd (by norm_num) h8
      have h10 : (x - 7 : ℤ) ≥ -3 := by
        have h11 : -(x - 7 : ℤ) ∣ 3 := by
          exact Int.neg_dvd.2 h8
        have h12 : -(x - 7 : ℤ) ≤ 3 := by
          apply Int.le_of_dvd (by norm_num) h11
        omega
      interval_cases (x - 7 : ℤ) <;> try { tauto }
    rcases hx11 with (h | h | h | h)
    · -- x - 7 = 1 → x = 8
      have hx8 : x = 8 := by
        omega
      simp [hx8]
      all_goals tauto
    · -- x - 7 = 3 → x = 10
      have hx8 : x = 10 := by
        omega
      simp [hx8]
      all_goals tauto
    · -- x - 7 = -1 → x = 6
      have hx8 : x = 6 := by
        omega
      simp [hx8]
      all_goals tauto
    · -- x - 7 = -3 → x = 4
      have hx8 : x = 4 := by
        omega
      simp [hx8]
      all_goals tauto
  · -- Assume x ∈ {4, 6, 8, 10}, prove E(x) = n
    intro h
    rcases h with (r | r | r | r)
    · -- x = 4
      rw [r]
      norm_num [h6]
      all_goals norm_num
    · -- x = 6
      rw [r]
      norm_num [h6]
      all_goals norm_num
    · -- x = 8
      rw [r]
      norm_num [h6]
      all_goals norm_num
    · -- x = 10
      rw [r]
      norm_num [h6]
      all_goals norm_num