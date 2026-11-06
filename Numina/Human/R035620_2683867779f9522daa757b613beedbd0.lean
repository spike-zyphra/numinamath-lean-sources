import Mathlib

theorem algebra_98320 {a r : ℝ} (hsum : ∑' n : ℕ, a * r ^ n = 7)
(hodd : ∑' n : ℕ, a * r ^ (2 * n + 1) = 3) : a + r = 5 / 2 := by
  /- The sum of an infinite geometric series is given by $\frac{a}{1-r}$ where $a$ is the first term and $r$ is the common ratio.
  In this series, $\frac{a}{1-r} = 7$ -/
  have st1 := tsum_geometric_of_norm_lt_one (ξ := r)
  rw [← summable_geometric_iff_norm_lt_one] at st1
  -- Get a Summable instance by doing proof by contradiction
  have st2 : Summable fun n => r ^ n := by
    by_cases hd : (Summable fun n => r ^ n)
    · exact hd
    rw [tsum_mul_left, tsum_def] at hsum
    rw [dif_neg hd] at hsum
    norm_num at hsum
  -- Transform hsum into a * (1 - r)⁻¹ = 7
  rw [tsum_mul_left, st1 st2] at hsum
  /- The series with odd powers of $r$ is given as\[ar + ar^3 + ar^5 ...\]
  Its sum can be given by $\frac{ar}{1-r^2} = 3$ -/
  -- Rewrite a litle so we can apply tsum_geometric_of_norm_lt_one
  have st3 (n : ℕ) : a * r ^ (2 * n + 1) = (a * r) * (r ^ 2) ^ n := by ring
  simp_rw [st3, tsum_mul_left] at hodd
  -- Get a Summable instance by doing proof by contradiction
  have st4 : Summable fun n => (r ^ 2) ^ n := by
    by_cases hd : (Summable fun n => (r ^ 2) ^ n)
    · exact hd
    rw [tsum_def] at hodd
    rw [dif_neg hd] at hodd
    norm_num at hodd
  have st5 := tsum_geometric_of_norm_lt_one (ξ := r ^ 2)
  rw [← summable_geometric_iff_norm_lt_one] at st5
  -- Transform hodd into a * r * (1 - r ^ 2)⁻¹ = 3
  rw [st5 st4] at hodd
  -- ⇒ a * r * ((1 - r)⁻¹ * (1 + r)⁻¹) = 3
  rw [(by ring : (1 - r ^ 2) = (1 - r) * (1 + r)), mul_inv] at hodd
  -- ⇒ 7 * (r * (1 + r)⁻¹) = 3
  rw [(by ring : a * r * ((1 - r)⁻¹ * (1 + r)⁻¹) = (a * (1 - r)⁻¹) * (r * (1 + r)⁻¹)), hsum] at hodd
  -- Now we prove r ≠ 1 and r ≠ -1
  rw [summable_geometric_iff_norm_lt_one] at st2
  have st6 : r ≠ 1 := by aesop
  have st9 : r ≠ -1 := by aesop
  have st7 : 7 * (r * (1 + r)⁻¹) * (1 + r) = 3 * (1 + r) := by rw [hodd]
  -- Now we have 7 * r * 1 = 3 * (1 + r)
  rw [(by ring : 7 * (r * (1 + r)⁻¹) * (1 + r) = 7 * r * ((1 + r)⁻¹ * (1 + r))), inv_mul_cancel₀ (by aesop)] at st7
  -- Conclude r = 3 / 4
  have rI : r = 3 / 4 := by linarith
  rw [rI] at hsum
  -- Conclude a + r = 5 / 2
  linarith