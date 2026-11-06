import Mathlib

theorem number_theory_184736 (x : ℕ) (hx : x.Prime) (h : ∃ n, n.Prime ∧ n = x + 2) (h' : ∃ m, m.Prime ∧ m = x + 6) (h'' : ∃ p, p.Prime ∧ p = x + 8) (h''' : ∃ q, q.Prime ∧ q = x + 12) (h'''' : ∃ r, r.Prime ∧ r = x + 14) :
    x = 5 := by
  rcases h with ⟨n, hn, hn_eq⟩
  rcases h' with ⟨m, hm, hm_eq⟩
  rcases h'' with ⟨p, hp, hp_eq⟩
  rcases h''' with ⟨q, hq, hq_eq⟩
  rcases h'''' with ⟨r, hr, hr_eq⟩
  have h1 : (x + 2).Prime := by
    rw [hn_eq] at hn
    exact hn
  have h2 : (x + 6).Prime := by
    rw [hm_eq] at hm
    exact hm
  have h3 : (x + 8).Prime := by
    rw [hp_eq] at hp
    exact hp
  have h4 : (x + 12).Prime := by
    rw [hq_eq] at hq
    exact hq
  have h5 : (x + 14).Prime := by
    rw [hr_eq] at hr
    exact hr

  by_cases h5' : x ≤ 23
  · -- In case, x <= 23, manually check primes
    interval_cases x <;> norm_num at hx h1 h2 h3 h4 h5 <;> omega
  · -- In case x > 23, prove contradiction
    have h6 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    rcases h6 with (h | h | h | h | h)
    · -- x % 5 = 0
      have h7 : x % 5 = 0 := h
      have h8 : ¬ x.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ x by omega)
        all_goals omega
      contradiction
    · -- x % 5 = 1
      have h7 : (x + 14) % 5 = 0 := by
        omega
      have h8 : ¬ (x + 14).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (x + 14) by omega)
        all_goals omega
      contradiction
    · -- x % 5 = 2
      have h8 : (x + 8) % 5 = 0 := by
        omega
      have h9 : ¬ (x + 8).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (x + 8) by omega)
        all_goals omega
      contradiction
    · -- x % 5 = 3
      have h10 : (x + 12) % 5 = 0 := by
        omega
      have h11 : ¬ (x + 12).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (x + 12) by omega)
        all_goals omega
      contradiction
    · -- x % 5 = 4
      have h12 : (x + 6) % 5 = 0 := by
        omega
      have h13 : ¬ (x + 6).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (x + 6) by omega)
        all_goals omega
      contradiction