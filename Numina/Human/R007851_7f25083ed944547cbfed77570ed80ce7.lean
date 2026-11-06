import Mathlib

/- Show that if \( p \) is a prime number and \( 1 \leq k < p \),
  then the binomial coefficient \( \binom{p}{k} \) is divisible by \( p \). -/
theorem number_theory_4502 {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k ∧ k < p) : p ∣ p.choose k := by
  -- \binom{p}{k} * k = \binom{p}{1} * \binom{p-1}{k-1}
  have := Nat.choose_mul (show k ≤ p by linarith) hk.1
  simp only [Nat.choose_one_right] at this
  -- From above result, we have `p | \binom{p}{k} * k`.
  replace : p ∣ p.choose k * k := ⟨_, this⟩
  -- As `1≤k<p` we know that p,k are coprime,
  -- hence we can deduce `p | \binom{p}{k}`.
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_of_lt_prime (by omega) hk.2 hp) this
