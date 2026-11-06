import Mathlib

/- Show that if the smallest prime factor \( p \) of the positive integer \( n \)
  exceeds \( \sqrt[3]{n} \), then \( n / p \) must be prime or 1. -/
theorem number_theory_4493 {n p : ℕ}
    (pos_n : 0 < n) (hp : p = n.minFac) (hn : p > (n : ℝ) ^ (1 / 3 : ℝ)) :
    (n / p).Prime ∨ n / p = 1 := by
  obtain ⟨k, hk⟩ := Nat.minFac_dvd n
  rw [← hp] at hk
  rw [hk] at hn
  simp only [gt_iff_lt] at hn
  -- Prove that `k < p ^ 2`.
  replace hn : k < p ^ 2 := by
    have := Real.rpow_lt_rpow (by positivity) hn (show 0 < 3 by simp)
    rw [← Real.rpow_mul (by positivity)] at this
    apply Nat.lt_of_mul_lt_mul_left (a := p)
    rify
    conv_rhs => rw [mul_comm, ← pow_succ, ← Real.rpow_natCast]
    simpa using this
  have pos_p : 0 < p := by
    by_contra h
    simp only [not_lt, nonpos_iff_eq_zero] at h
    simp [h] at hk
    omega
  rw [show n / p = k from Nat.div_eq_of_eq_mul_right pos_p hk]
  -- Now we can show that `k` is prime or 1, using proof by contradiction.
  by_contra h
  simp only [not_or] at h
  have : k.minFac < p := by
    rw [← Nat.pow_lt_pow_iff_left (show 2 ≠ 0 by simp)]
    calc
      _ ≤ k := by
        refine Nat.minFac_sq_le_self ?_ h.1
        by_contra h'
        simp only [not_lt, nonpos_iff_eq_zero] at h'
        simp [h'] at hk
        omega
      _ < _ := hn
  -- Split a special case for `n = 1`.
  by_cases n_1 : n = 1
  · rw [n_1] at hp hk
    rw [hp] at hk
    simp only [Nat.minFac_one, one_mul] at hk
    exact h.2 hk.symm
  · refine Nat.le_lt_asymm (Nat.minFac_le_of_dvd ?_ ?_) (hp ▸ this)
    · exact Nat.Prime.two_le (Nat.minFac_prime (by omega))
    · exact Nat.dvd_trans (Nat.minFac_dvd _) ⟨p, Nat.mul_comm _ _ ▸ hk⟩
