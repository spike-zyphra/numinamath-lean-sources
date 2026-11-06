import Mathlib

/- \section*{Problem 2 - 141212}

Prove:

If the sum of two natural numbers $m$ and $n$ is divisible by 7, then the sum $m^{7}+n^{7}$ is divisible by 49. -/
theorem number_theory_197322 (m n : ℕ) (h : 7 ∣ (m + n)) : 49 ∣ (m^7 + n^7) := by
  -- We can use the standard "lifting the exponent" lemmas here. Note
  -- that this requires ¬(7 ∣ m) so we split into two cases.
  rw [show 49 = 7^2 by norm_num]
  by_cases hm : 7 ∣ m
  . have hn : 7 ∣ n := by
      rw [← Nat.dvd_add_iff_right hm] at h
      exact h
    apply Nat.dvd_add
    . rw [show m^7 = m^2 * m^5 by ring]
      apply dvd_mul_of_dvd_left
      exact pow_dvd_pow_of_dvd hm _
    . rw [show n^7 = n^2 * n^5 by ring]
      apply dvd_mul_of_dvd_left
      exact pow_dvd_pow_of_dvd hn _
  . rw [pow_dvd_iff_le_emultiplicity]
    rw [Nat.emultiplicity_pow_add_pow (by norm_num) (by decide) h hm (by decide)]
    rw [show ((2 : ℕ) : ℕ∞) = ((1 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞) by norm_num]
    apply add_le_add
    . rw [← pow_dvd_iff_le_emultiplicity]
      simp
      exact h
    . rw [← pow_dvd_iff_le_emultiplicity]
      simp