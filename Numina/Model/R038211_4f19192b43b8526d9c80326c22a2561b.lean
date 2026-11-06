import Mathlib

theorem algebra_179616 {a q : ℝ} (hq : |q| < 1) (hsum : ∑' n : ℕ, a * q ^ n = 4)
    (hsumcub : ∑' n : ℕ, (a * q ^ n) ^ 3 = 192) :
    a = 6 ∧ q = -0.5 := by

  have h1 : ∑' n : ℕ, a * q ^ n = a / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · -- Show that |q| < 1
      simpa using hq

  rw [h1] at hsum
  have eq1 : a / (1 - q) = 4 := by
    simpa using hsum

  have h2 : ∑' n : ℕ, (a * q ^ n) ^ 3 = a ^ 3 / (1 - q ^ 3) := by
    have h3 : ∑' n : ℕ, (a * q ^ n) ^ 3 = ∑' n : ℕ, a^ 3 * (q^ 3) ^ n := by
      congr
      funext n
      ring_nf

    rw [h3]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · -- Show that |q ^ 3| < 1
      have h4 : |q ^ 3| < 1 := by
        have h5 : |q ^ 3| = |q| ^ 3 := by
          simp [abs_pow]

        rw [h5]
        have h6 : |q| ^ 3 < (1 : ℝ) := by
          have h7 : |q| < 1 := by
            simpa using hq

          have h8 : |q| ^ 3 < (1 : ℝ) ^ 3 := by
            apply pow_lt_pow_left
            all_goals linarith [abs_nonneg q, h7]
          have h9 : (1 : ℝ) ^ 3 = 1 := by
            norm_num
          linarith

        linarith

      simpa using h4

  rw [h2] at hsumcub
  have eq2 : a^3 / (1 - q^3) = 192 := by
    simpa using hsumcub

  have h3 : a = 4 * (1 - q) := by
    have h4 : 1 - q ≠ 0 := by
      by_contra h
      have eq1' : a / (1 - q) = 0 := by
        rw [h]
        norm_num
      linarith

    field_simp [h4] at eq1 
    nlinarith

  have h4 : 1 - q^3 ≠ 0 := by
    by_contra h
    have eq2' : a^3 / (1 - q^3) = 0 := by
      rw [h]
      norm_num

    linarith

  have eq3 : a^3 = 192 * (1 - q^3) := by 
    field_simp [h4] at eq2 
    nlinarith

  rw [show a = 4 * (1 - q) by linarith [h3] ] at eq3
  have eq4 : (4 * (1 - q) )^3 = 192 * (1 - q^3) := by
    linarith

  have h5 : (q + 0.5) * (q + 2) = 0 := by 
    nlinarith [sq_nonneg (q + 0.5), sq_nonneg (q + 2), sq_nonneg (q - 1), abs_lt.mp hq]

  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- q + 0.5 = 0 
    have hq1 : q = -0.5 := by
      nlinarith

    have h11 : a = 6 := by
      rw [hq1] at h3
      nlinarith

    constructor
    · exact h11
    · exact hq1

  · -- q + 2 = 0 
    have hq2 : q = -2 := by
      nlinarith

    have h8 : |q| ≥ 1 := by 
      rw [hq2]
      norm_num [abs]

    linarith [abs_lt.mp hq, h8]