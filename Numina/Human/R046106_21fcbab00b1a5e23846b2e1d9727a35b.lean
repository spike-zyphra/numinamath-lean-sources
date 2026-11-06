import Mathlib

open Real

/- Example 4 Find the size of the angle $\theta=4 \arctan \frac{1}{5}-\arctan \frac{1}{239}$. -/
theorem algebra_107373 : 4 * arctan (1 / 5) - arctan (1 / 239) = π / 4 := by
  -- It is John Machin's 1706 formula:
  -- simp; exact four_mul_arctan_inv_5_sub_arctan_inv_239
  -- Consider an alternative proofs with complex numbers.
  -- First of all, rewrite the goal as an equality between angles.
  suffices h : ((4 : ℝ) * arctan (1 / 5) : Angle) - arctan (1 / 239) = ((π / 4 : ℝ) : Angle) by
    rw [← Real.Angle.coe_sub] at h
    -- We need to show 4 * arctan (1 / 5) - arctan (1 / 239) = 2 * π * k implies that k = 0.
    rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
    have ⟨k, hk⟩ := h
    suffices k = 0 by subst k; linarith
    -- We have arctan (1 / 5) < arctan 1 = π / 4
    have ineq1 : arctan (1 / 5) < π / 4 := by
      rw [← arctan_one]
      apply arctan_strictMono (by norm_num)
    -- We have arctan (1 / 5) < arctan 1 = π / 4
    have ineq2 : arctan (1 / 239) < π / 4 := by
      rw [← arctan_one]
      apply arctan_strictMono (by norm_num)
    -- We have 0 < arctan (1 / 5)
    have ineq3 : 0 < arctan (1 / 5) := by
      rw [← arctan_zero]
      apply arctan_strictMono (by norm_num)
    -- We have 0 < arctan (1 / 239)
    have ineq4 : 0 < arctan (1 / 239) := by
      rw [← arctan_zero]
      apply arctan_strictMono (by norm_num)
    -- We have arctan (1 / 239) < arctan (1 / 5)
    have ineq5 : arctan (1 / 239) < arctan (1 / 5) := by
      apply arctan_strictMono (by norm_num)
    -- We get 0 < 4 * arctan (1 / 5) - arctan (1 / 239) < π.
    have h1 : 4 * arctan (1 / 5) - arctan (1 / 239) < π := by linarith
    have h2 : 0 < 4 * arctan (1 / 5) - arctan (1 / 239) := by linarith
    -- Consider the following cases: k ≤ -1, k = 0, 1 ≤ k.
    rcases show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega with h | h | h
    -- If k ≤ -1 then 4 * arctan (1 / 5) - arctan (1 / 239) ≤ 0, a contradiction.
    · rify at h
      nlinarith
    · exact h
    -- If 1 ≤ k then 2 * π ≤ 4 * arctan (1 / 5) - arctan (1 / 239), a contradiction.
    · rify at h
      nlinarith
  -- The argument of the complex number 5 + I is arctan (1 / 5).
  have h1 : (5 + Complex.I).arg = arctan (1 / 5) := by
    simp [Complex.arg, arctan_eq_arcsin, Complex.abs, Complex.normSq]
    field_simp
    norm_num
  -- The argument of the complex number 239 + I is arctan (1 / 239).
  have h2 : (239 + Complex.I).arg = arctan (1 / 239) := by
    simp [Complex.arg, arctan_eq_arcsin, Complex.abs, Complex.normSq]
    field_simp
    norm_num
  rw [←h1, ←h2, show (4 : ℝ) = (4 : ℕ) by simp, Angle.natCast_mul_eq_nsmul]
  -- The following lemma is missing in Mathlib 4.15. Copy this lemma from the most recent version of Mathlib:
  -- (z ^ n).arg = n • z.arg.
  have arg_pow_coe_angle (x : ℂ) (n : ℕ) :
    (Complex.arg (x ^ n) : Real.Angle) = n • (Complex.arg x : Real.Angle) := by
      obtain rfl | x0 := eq_or_ne x 0
      · by_cases n0 : n = 0 <;> simp [n0]
      · induction n with
        | zero => simp [x0]
        | succ n ih => rw [pow_succ, Complex.arg_mul_coe_angle (pow_ne_zero n x0) x0, ih, succ_nsmul]
  have hineq (x : ℝ) : x + Complex.I ≠ 0 := by
    intro h
    simp [Complex.ext_iff] at h
  -- Rewrite the goal as follows:
  -- ((5 + I)^4 / (239 + I)).arg = π / 4.
  rw [← arg_pow_coe_angle, ← Complex.arg_div_coe_angle _ (by exact hineq 239)]
  -- It is enough to show that (5 + I)^4 / (239 + I) = 2 + 2I.
  · suffices (5 + Complex.I) ^ 4 / (239 + Complex.I) = 2 + 2 * Complex.I by
      simp [this, Complex.arg, Complex.abs, Complex.normSq]
      -- Compute the argument of 2 + 2I and show that it equals to π / 4 = arctan 1.
      rw [← Real.arctan_one, arctan_eq_arcsin]
      congr 2
      field_simp
      rw [show (2 * 2 : ℝ) + 2 * 2 = 2 ^ 2 * 2 by norm_num, sqrt_mul (by norm_num), sqrt_sq (by norm_num)]
      norm_num
    -- Show that (5 + I)^4 / (239 + I) = 2 + 2I by simplifying this expression.
    field_simp [show 239 + Complex.I ≠ 0 by exact hineq 239]
    ring_nf
    rw [show 3 = 2 + 1 by norm_num, show 4 = 2 + 2 by norm_num, pow_add, pow_add, Complex.I_sq]
    ring
  · apply pow_ne_zero
    exact hineq 5