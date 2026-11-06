import Mathlib

theorem algebra_98320 {a r : ℝ} (hsum : ∑' n : ℕ, a * r ^ n = 7)
(hodd : ∑' n : ℕ, a * r ^ (2 * n + 1) = 3) : a + r = 5 / 2 := by
  have st1 := tsum_geometric_of_norm_lt_one (ξ := r)
  rw [← summable_geometric_iff_norm_lt_one] at st1
  have st2 : Summable fun n => r ^ n := by
    by_cases hd : (Summable fun n => r ^ n)
    · exact hd
    rw [tsum_mul_left, tsum_def] at hsum
    rw [dif_neg hd] at hsum
    norm_num at hsum
  rw [tsum_mul_left, st1 st2] at hsum
  -- Rewrite terms in hodd so we can apply the geometric series formula.
  have st3 (n : ℕ) : a * r ^ (2 * n + 1) = (a * r) * (r ^ 2) ^ n := by ring
  simp_rw [st3, tsum_mul_left] at hodd
  -- Prove that the series with ratio r^2 is summable.
  have st4 : Summable fun n => (r ^ 2) ^ n := by
    by_cases hd : (Summable fun n => (r ^ 2) ^ n)
    · exact hd
    rw [tsum_def] at hodd
    rw [dif_neg hd] at hodd
    norm_num at hodd
  -- Apply the geometric series formula to the second sum.
  have st5 := tsum_geometric_of_norm_lt_one (ξ := r ^ 2)
  rw [← summable_geometric_iff_norm_lt_one] at st5
  rw [st5 st4] at hodd
  -- Now we have two equations: a * (1 - r)⁻¹ = 7 and a * r * (1 - r^2)⁻¹ = 3
  have h_eq1 : a = 7 * (1 - r) := by
    have h1 : (1 - r) ≠ 0 := by
      by_contra h
      rw [h] at hsum
      norm_num at hsum
    field_simp [h1] at hsum
    linarith
  -- Second equation: a * r / (1 - r^2) = 3
  have h_eq2 : a * r = 3 * (1 - r^2) := by
    have h2 : (1 - r^2) ≠ 0 := by
      by_contra h
      rw [h] at hodd
      norm_num at hodd
    field_simp [h2] at hodd
    nlinarith
  -- Substitute a from the first equation into the second
  rw [show a = 7 * (1 - r) by linarith [h_eq1]] at h_eq2
  -- Solving the equation
  have hr : r = 3 / 4 := by
    have h2 : (1 - r) ≠ 0 := by
      by_contra h
      rw [h] at hsum
      norm_num at hsum
    have h4 : 7 * r * (1 - r) = 3 * (1 - r^2) := by
      nlinarith [h_eq2]
    have h5 : 7 * r = 3 * (1 + r) := by
      apply (mul_left_inj' h2).mp
      nlinarith [h4]
    nlinarith
  -- Compute a from r
  have ha : a = 7 / 4 := by
    rw [hr] at h_eq1
    nlinarith
  -- Therefore a + r = 5/2
  linarith [ha, hr]