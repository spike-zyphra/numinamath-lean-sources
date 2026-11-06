import Mathlib

theorem algebra_179556 {a q : ℝ} (hq : |q| < 1) (hsum : ∑' n : ℕ, a * q ^ n = 16)
    (hsumsq : ∑' n : ℕ, (a * q ^ n) ^ 2 = 153.6) :
    a * q ^ 3 = 3 / 16 := by

  have h1 : ∑' n : ℕ, a * q ^ n = a / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring_nf
      <;> field_simp [(show (1 - q) ≠ 0 by
        by_contra h
        have : q = 1 := by linarith
        rw [this] at hq
        norm_num [abs_lt] at hq
      )]
      <;> ring
    · exact hq
  rw [h1] at hsum

  have h2 : ∑' n : ℕ, (a * q ^ n) ^ 2 = (a ^ 2) / (1 - q ^ 2) := by
    have h3 : ∀ n : ℕ, (a * q ^ n) ^ 2 = (a ^ 2) * (q ^ 2) ^ n := by
      intro n
      ring_nf
    rw [tsum_congr h3]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring_nf
      <;> field_simp [(show (1 - q ^ 2) ≠ 0 by
        by_contra h
        have h11 : q ^ 2 = 1 := by linarith
        have h12 : q = 1 ∨ q = -1 := by
          rw [sq_eq_one_iff] at h11
          tauto
        cases h12 with
        | inl h13 =>
          rw [h13] at hq
          norm_num [abs_lt] at hq
        | inr h14 =>
          rw [h14] at hq
          norm_num [abs_lt] at hq
      )]
      <;> ring
    · have hq2 : |q ^ 2| < 1 := by
        have h19 : |q ^ 2| = |q| ^ 2 := by
          simp [abs_pow]
        rw [h19]
        nlinarith [abs_nonneg q, hq]
      simpa using hq2
  rw [h2] at hsumsq

  have eq1 : a / (1 - q) = 16 := by 
    simpa using hsum

  have eq2 : (a ^ 2) / (1 - q ^ 2) = (153.6 : ℝ) := by 
    simpa using hsumsq

  have eq3 : a = 16 * (1 - q) := by
    have h6 : (1 - q) ≠ 0 := by
      by_contra h
      have h7 : q = 1 := by linarith
      rw [h7] at hq
      norm_num [abs_lt] at hq
    field_simp [h6] at eq1 ⊢
    linarith

  rw [eq3] at eq2

  have h6 : (1 - q ^ 2 : ℝ) ≠ 0 := by
    by_contra h
    have h7 : q ^ 2 = 1 := by linarith
    have h8 : q = 1 ∨ q = -1 := by
      rw [sq_eq_one_iff] at h7
      tauto
    cases h8 with
    | inl h9 =>
      rw [h9] at hq
      norm_num [abs_lt] at hq
    | inr h10 =>
      rw [h10] at hq
      norm_num [abs_lt] at hq

  have h2 : (1 - q) * (1 + q) ≠ 0 := by
    by_contra h
    cases' (mul_eq_zero.mp h) with h6 h7
    · 
      have h7 : q = 1 := by linarith
      rw [h7] at hq
      norm_num [abs_lt] at hq
    · 
      have h8 : q = -1 := by linarith
      rw [h8] at hq
      norm_num [abs_lt] at hq

  field_simp [h6, show (1 - q ^ 2) ≠ 0 by exact h6] at eq2

  have h1226341 : q = 1 / 4 := by
    ring_nf at eq2
    nlinarith [abs_lt.mp hq]

  rw [h1226341] at eq3
  have ha1 : a = 12 := by
    linarith
  rw [ha1, h1226341]
  norm_num