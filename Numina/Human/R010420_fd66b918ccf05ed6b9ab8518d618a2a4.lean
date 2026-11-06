import Mathlib

/- Prove that for any odd positive integer $n, n^{12}-n^{8}-n^{4}+1$ is divisible by $2^{9}$. -/
theorem number_theory_240527 (n : ℤ) (hn : Odd n ∧ n > 0) :
    2^9 ∣ n^12 - n^8 - n^4 + 1 := by
  -- Factorize the expression.
  rw [show n ^ 12 - n ^ 8 - n ^ 4 + 1 = (n ^ 4 + 1) * (n ^ 2 + 1) ^ 2 * ((n - 1) * (n + 1)) ^ 2 by ring]
  -- Show that one of n - 1 or n + 1 is divisible by 4.
  have h₀ : (n - 1) % 4 = 0 ∨ (n + 1) % 4 = 0 := by
    rw [Int.odd_iff] at hn
    omega
  iterate 2 rw [<-Int.dvd_iff_emod_eq_zero] at h₀
  -- Show that (n - 1)(n + 1) is divisible by 8.
  have h₁ : 8 ∣ (n - 1) * (n + 1) := by
    cases h₀ with
    | inl h₀ =>
      rw [show (8 : ℤ) = 4 * 2 by norm_num]
      apply mul_dvd_mul h₀
      rw [<-even_iff_two_dvd]
      apply Odd.add_odd hn.1 (by norm_num)
    | inr h₀ =>
      rw [mul_comm, show (8 : ℤ) = 4 * 2 by norm_num]
      apply mul_dvd_mul h₀
      rw [<-even_iff_two_dvd]
      apply Odd.sub_odd hn.1 (by norm_num)
  -- Show that n⁴ + 1 and n² + 1 are even and hence divisible by 2.
  have h₂ : 2 ∣ n ^ 4 + 1 ∧ 2 ∣ n ^ 2 + 1 := by
    refine ⟨?_, ?_⟩
    all_goals
      rw [<-even_iff_two_dvd]
      apply Odd.add_odd
      apply Odd.pow hn.1
      norm_num
  calc
    2 ^ 9 = 2 * 2 ^ 2 * 8 ^ 2 := by
      norm_num
    _ ∣ (n ^ 4 + 1) * (n ^ 2 + 1) ^ 2 * ((n - 1) * (n + 1)) ^ 2 := by
      iterate 2 apply mul_dvd_mul
      . exact h₂.1
      . apply pow_dvd_pow_of_dvd
        exact h₂.2
      . apply pow_dvd_pow_of_dvd
        exact h₁
