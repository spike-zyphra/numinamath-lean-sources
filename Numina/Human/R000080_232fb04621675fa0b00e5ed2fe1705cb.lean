import Mathlib

/- Show that if \( n \) is a composite integer, then there exists at least one prime factor of \( n \) that does not exceed \( \sqrt{n} \).-/
theorem number_theory_4481 {n : ℕ} (hcom : ∃ m, 1 < m ∧ m < n ∧ m ∣ n) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p^2 ≤ n := by
  rcases hcom with ⟨m, hm1, hm2, hmn⟩
  have hn_eq_nmm : n = (n / m) * m := Eq.symm (Nat.div_mul_cancel hmn)
  by_cases hm : m^2 ≤ n
  --  Now, according to Lemma 1.1, every integer greater than 1 has at least one prime divisor. Since \( a \) is an integer greater than 1 and \( a \leq \sqrt{n} \), it follows that \( a \) has a prime divisor. By Proposition 1.3, this prime divisor is also a divisor of \( n \) (since \( n = a \cdot b \)).
  . obtain ⟨p, ⟨hp, hpm⟩⟩ := Nat.exists_prime_and_dvd hm1.ne'
    use p
    have : p ≤ m := Nat.le_of_dvd (by linarith) hpm
    exact ⟨hp, Nat.dvd_trans hpm hmn, by nlinarith⟩
  --  Next, we analyze the relationship between \( a \) and \( \sqrt{n} \). If we assume that \( a > \sqrt{n} \), then it follows that \( b \) must also be greater than or equal to \( a \), which implies \( b \geq a > \sqrt{n} \). Consequently, this would lead to the product \( a \cdot b > \sqrt{n} \cdot \sqrt{n} = n \), which is a contradiction since \( n = a \cdot b \).
  push_neg at hm
  rcases lt_or_ge ((n / m)^2) n with h1 | h1
  . have hn_div_m_ne_one : n / m ≠ 1 := fun h => by linarith [h ▸ hn_eq_nmm]
    obtain ⟨p, ⟨hp, hpm⟩⟩ := Nat.exists_prime_and_dvd hn_div_m_ne_one
    use p
    have hn_pos : 0 < n := by linarith
    have hn_div_m_pos : 0 < n / m := by
      rw [hn_eq_nmm] at hn_pos
      apply Nat.pos_of_mul_pos_right hn_pos
    have : p ≤ n / m := Nat.le_of_dvd hn_div_m_pos hpm
    have hn_div_m_dvd : n / m ∣ n := by nth_rw 2 [hn_eq_nmm]; apply Nat.dvd_mul_right
    exact ⟨hp, Nat.dvd_trans hpm hn_div_m_dvd, by nlinarith⟩
  have : m^2 * (n/m)^2 > n^2 := by nlinarith
  have : m^2 * (n/m)^2 = n^2 := by nth_rw 2 [hn_eq_nmm]; ring
  linarith
