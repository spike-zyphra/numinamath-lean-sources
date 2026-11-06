import Mathlib

theorem number_theory_104620 (p q r s : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime)
    (h : 6*p+7*p*q+8*p*q*r+9*p*q*r*s=2018) :
    (p=2 ∧ q=17 ∧ r=2 ∧ s=2) := by
  rcases hpqr with ⟨hp, hq, hr, hs⟩
  have h1 : p ∣ 2018 := by
    use 6 + 7 * q + 8 * q * r + 9 * q * r * s
    linarith
  have h2 : p = 2 ∨ p = 1009 := by 
    have h3 : p ∣ 2018 := h1
    have h4 : p ≤ 2018 := by
      exact Nat.le_of_dvd (by norm_num) h3
    interval_cases p <;> norm_num at hp h3 <;> tauto
  cases h2 with
  | inl hp2 =>
    have eq1 : 6 * p + 7 * p * q + 8 * p * q * r + 9 * p * q * r * s = 2018 := h
    rw [hp2] at eq1
    have eq2 : 14 * q + 16 * q * r + 18 * q * r * s = 2006 := by 
      linarith
    have h6 : q * (7 + 8 * r + 9 * r * s) = 1003 := by
      nlinarith
    have h7 : q ∣ 1003 := by 
      use 7 + 8 * r + 9 * r * s
      linarith
    have h8 : q ≤ 1003 := by 
      apply Nat.le_of_dvd (by norm_num) h7
    have h5 : q = 17 ∨ q = 59 := by 
      interval_cases q <;> norm_num at hq h7 h6 <;> try {
        omega
      }
    cases h5 with
    | inl hq17 =>
      have eq3 : 14 * q + 16 * q * r + 18 * q * r * s = 2006 := eq2
      rw [hq17] at eq3
      have h6 : 8 * r + 9 * r * s = 52 := by 
        nlinarith
      have eq8 : r = 2 := by
        have h7 : r ∣ 52 := by
          use 8 + 9 * s
          linarith
        have h8 : r ≤ 52 := by 
          apply Nat.le_of_dvd (by norm_num) h7
        interval_cases r <;> norm_num at hr h7 h6 <;> try { 
          omega
        } <;> norm_num
      rw [eq8] at h6
      have eq4 : 8 + 9 * s = 26 := by 
        linarith
      have eq5 : s = 2 := by 
        nlinarith
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    | inr hq59 =>
      have eq3 : 14 * q + 16 * q * r + 18 * q * r * s = 2006 := eq2
      rw [hq59] at eq3
      have h8 : 8 * r + 9 * r * s = 10 := by 
        nlinarith
      exfalso
      have h7 : r ∣ 10 := by
        use 8 + 9 * s
        linarith
      have h8 : r ≤ 10 := by 
        apply Nat.le_of_dvd (by norm_num) h7
      interval_cases r <;> norm_num at hr h7 h8 h8 <;> omega
  | inr hp1009 =>
    have eq1 : 6 * p + 7 * p * q + 8 * p * q * r + 9 * p * q * r * s = 2018 := h
    rw [hp1009] at eq1
    exfalso
    omega