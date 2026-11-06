import Mathlib

theorem number_theory_157502 (a b c d : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hd : d.Prime) (h1 : a + b = c) (h2 : 2 * a + b = d) :
    a = 2 ∧ b = 3 ∧ c = 5 ∧ d = 7 := by
  by_cases h3 : a % 2 = 1
  · -- Assume a is odd
    by_cases h4 : b % 2 = 1
    · -- Assume b is odd
      have h5 : c % 2 = 0 := by
        omega
      have h6 : c > 2 := by
        have ha2 : a ≥ 2 := Nat.Prime.two_le ha
        have hb2 : b ≥ 2 := Nat.Prime.two_le hb
        omega
      have h7 : ¬c.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ c by omega)
        all_goals omega
      contradiction
    · -- Assume b is even
      have h8 : b = 2 := by
        by_cases h9 : b > 2
        · -- Assume b > 2
          have h10 : ¬b.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ b by omega)
            all_goals omega
          contradiction
        · -- Assume b ≤ 2
          interval_cases b <;> try tauto
      rw [h8] at h1 h2
      have h9 : a + 2 = c := by
        omega
      have h11 : d = 2 * (a + 1) := by
        nlinarith
      by_cases h12 : d > 2
      · -- Assume d > 2
        have h14 : ¬d.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ d by 
            omega
          )
          all_goals omega
        contradiction
      · -- Assume d ≤ 2
        have h13 : d = 2 := by
          interval_cases d <;> norm_num at hd hd ⊢
          all_goals omega
        rw [h13] at h11
        have h14 : a = 0 := by
          omega
        rw [h14] at ha
        norm_num at ha
  · -- Assume a is even
    have h9 : a % 2 = 0 := by
      omega
    have h10 : a = 2 := by
      by_cases h11 : a > 2
      · -- Assume a > 2
        have h12 : ¬a.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by omega)
          all_goals omega
        contradiction
      · -- Assume a ≤ 2
        interval_cases a <;> try tauto
    have h9' : b % 2 = 1 := by
      by_contra h
      push_neg at h
      have h9 : b % 2 = 0 := by
        omega
      have h11 : b = 2 := by
        by_cases h12 : b > 2
        · -- Assume b > 2
          have h13 : ¬b.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ b by omega)
            all_goals omega
          contradiction
        · -- Assume b ≤ 2
          interval_cases b <;> try tauto
      rw [h11] at h1
      have h9 : c = 4 := by
        omega
      rw [h9] at hc
      norm_num at hc
    have h15 : c = 2 + b := by
      rw [h10] at h1
      omega
    have h16 : d = 4 + b := by
      rw [h10] at h2
      omega
    by_cases h18 : b > 3
    · -- Assume b > 3
      by_cases h21 : b % 3 = 0
      · -- Assume b % 3 = 0
        have h22 : b > 3 := h18
        have h23 : ¬b.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ b by omega)
          all_goals omega
        contradiction
      by_cases h23 : b % 3 = 1
      · -- Assume b % 3 = 1
        have h24 : c % 3 = 0 := by 
          omega
        have h25 : c > 3 := by
          omega
        have h26 : ¬c.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ c by omega)
          all_goals omega
        contradiction
      · -- Assume b % 3 = 2
        have h27 : d % 3 = 0 := by 
          omega
        have h28 : d > 3 := by
          omega
        have h29 : ¬d.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ d by omega)
          all_goals omega
        contradiction
    · -- Assume b ≤ 3
      have h10' : b = 3 := by
        interval_cases b <;> try { 
          norm_num at hb h9' ⊢
          <;> tauto
        }
      have h11' : c = 5 := by
        rw [h10', h10] at h1
        omega
      have h12' : d = 7 := by
        rw [h10', h10] at h2
        omega
      exact ⟨by omega, by omega, by omega, by omega⟩