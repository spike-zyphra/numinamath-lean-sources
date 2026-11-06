import Mathlib

/- Show that if \( a \) and \( n \) are positive integers such that \( a^n - 1 \) is prime, then \( a = 2 \) and \( n \) is prime.
  (Hint: Use the identity \( a^{k\ell} - 1 = (a^k - 1)(a^{k(\ell-1)} + a^{k(\ell-2)} + \cdots + a^k + 1) \)). -/
theorem number_theory_4489 {a n : ℕ} (a_pos : a > 0) (n_pos : n > 1)
    (prime : (a ^ n - 1).Prime) : a = 2 ∧ n.Prime := by
  have ha : a = 1 ∨ a ≥ 3 ∨ a = 2 := by omega
  rcases ha with ha | ha | ha
  -- Case 1 : a = 1
  · rw [ha] at prime
    simp only [one_pow, le_refl, tsub_eq_zero_of_le] at prime
    absurd prime
    decide
  -- Case 2 : a ≥ 3
  · absurd prime
    rw [show n = 1 * n by simp]
    refine Nat.not_prime_of_dvd_of_ne
      (nat_pow_one_sub_dvd_pow_mul_sub_one a 1 n) ?_ ?_
    · simp; omega
    · simp only [pow_one, one_mul, ne_eq]
      intro hn
      replace hn := Nat.sub_one_cancel (by omega) (by omega) hn
      nth_rw 1 [← pow_one a] at hn
      suffices a ^ 1 < a ^ n by linarith
      apply Nat.pow_lt_pow_iff_right (by linarith) |>.2 n_pos
  -- Case 3 : a = 2
  · refine ⟨ha, ?_⟩
    by_contra hn
    rw [Nat.not_prime_iff_exists_dvd_ne (by linarith)] at hn
    obtain ⟨m, ⟨k, hn⟩, hm, hm'⟩ := hn
    absurd prime
    rw [hn]
    refine Nat.not_prime_of_dvd_of_ne
      (nat_pow_one_sub_dvd_pow_mul_sub_one a m k) (fun h => ?_) (fun h => ?_)
    · rw [ha] at h
      replace h : 2 ^ m = 2 ^ 1 := by simpa using h
      by_cases hm₀ : m = 0
      · rw [hm₀] at h
        linarith
      · suffices 2 ^ 1 < 2 ^ m by linarith
        apply  Nat.pow_lt_pow_iff_right (by linarith) |>.2 (by omega)
    · replace h := Nat.sub_one_cancel (by positivity) (by positivity) h
      rw [← hn] at h
      by_cases hmn : m < n
      · suffices a ^ m < a ^ n by linarith
        apply  Nat.pow_lt_pow_iff_right (by linarith) |>.2 hmn
      · suffices a ^ n < a ^ m by linarith
        apply  Nat.pow_lt_pow_iff_right (by linarith) |>.2 (by omega)
