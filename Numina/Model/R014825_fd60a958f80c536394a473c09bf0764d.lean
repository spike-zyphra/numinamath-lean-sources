import Mathlib

theorem algebra_186500 {a q : ℝ} (hq : |q| < 1) (hsum : a / (1 - q) = 16)
    (hsumsq : ∑' n : ℕ, (a * q ^ n) ^ 2 = 153.6) :
    a * q ^ 3 = 3 / 16 ∧ q = 1 / 4 := by

  have h1 : q ≠ 1 := by
    by_contra h
    have hq1 : |q| = 1 := by
      rw [h]
      norm_num
    linarith -- since |q| < 1

  have h2 : ∑' n : ℕ, (a * q ^ n) ^ 2 = a^2 / (1 - q ^ 2) := by
    have h3 : ∑' n : ℕ, (a * q ^ n) ^ 2 = ∑' n : ℕ, (a^2 * (q^2) ^ n) := by
      congr
      funext n
      ring_nf
    rw [h3]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · -- Show that |q^2| < 1
      have hq2 : |q^2| < 1 := by
        have hq1 : |q| < 1 := hq
        have hq2 : |q^2| = |q| ^ 2 := by
          simp [abs_pow]
        rw [hq2]
        nlinarith [abs_nonneg q, hq1]
      simpa using hq2

  rw [h2] at hsumsq

  have h3 : a = 16 * (1 - q) := by
    have h1' : 1 - q ≠ 0 := by
      intro h
      apply h1
      linarith
    field_simp [h1'] at hsum
    linarith

  have h4 : a^2 / (1 - q^2) = (153.6 : ℝ) := by linarith [hsumsq]

  have h5 : 1 - q ^ 2 ≠ 0 := by
    have hq1 : |q| < 1 := hq
    have hq2 : q^2 < 1 := by
      cases abs_lt.mp hq1 with
      | intro h1 h2 =>
        nlinarith [sq_nonneg q]
    have hq3 : 1 - q^2 > 0 := by
      nlinarith [sq_nonneg q, hq2]
    nlinarith

  rw [show a = 16 * (1 - q) by linarith [h3]] at h4

  have eq2 : (16 * (1 - q))^2 = (153.6 : ℝ) * (1 - q^2) := by
    field_simp [h5] at h4 ⊢
    nlinarith

  have eq5 : (4 * (q) ^ 2 - 5 * q + 1) = 0 := by
    ring_nf at eq2 ⊢
    nlinarith [sq_nonneg (q - 1 / 4) ]

  have hq2 : (q - 1) * (4 * q - 1) = 0 := by
    nlinarith [eq5]

  cases' (mul_eq_zero.mp hq2) with hq3 hq4

  · -- Case where q - 1 = 0, so q = 1
    exfalso
    apply h1
    linarith

  · -- Case where 4q - 1 = 0, so q = 1/4
    have hq1 : q = 1 / 4 := by linarith

    have ha1 : a = 12 := by
      rw [hq1] at h3
      linarith

    have haq3 : a * q ^ 3 = 3 / 16 := by
      rw [ha1, hq1]
      norm_num

    exact ⟨haq3, hq1⟩