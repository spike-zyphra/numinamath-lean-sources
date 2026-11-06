import Mathlib

theorem number_theory_169383 {p q r A : ℕ} (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (hqr : p ≠ q) (hpr : p ≠ r) (hqr' : q ≠ r) (hA : A > 0)
    (h1 : 2 * p * q * r + 50 * p * q = A) (h2 : 7 * p * q * r + 55 * p * r = A)
    (h3 : 8 * p * q * r + 12 * q * r = A) :
    A = 1980 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have eq1 : 2 * p * q * r + 50 * p * q = 7 * p * q * r + 55 * p * r := by
    nlinarith
  have eq2 : 7 * p * q * r + 55 * p * r = 8 * p * q * r + 12 * q * r := by
    nlinarith
  have eq3 : 10 * p * q = p * q * r + 11 * p * r := by
    nlinarith [eq1]
  have eq4 : 10 * q = q * r + 11 * r := by
    have hpne : p ≠ 0 := by
      exact Nat.Prime.ne_zero hp
    have h1 : p ≠ 0 := by
      exact hpne
    apply (mul_left_inj' h1).mp
    nlinarith [eq3]
  have eq5 : q = 11 := by
    have h3 : r ∣ 10 * q := by
      use (q + 11)
      nlinarith [eq4]
    have h4 : r = 2 ∨ r = 5 ∨ r ∣ q := by
      have h1 : r ∣ 10 * q := h3
      have h5 : r ∣ 10 ∨ r ∣ q := by
        have h1 : r ∣ 10 * q := h3
        have h2 : r.Prime := hr
        have h1' : r ∣ 10 ∨ r ∣ q := by
          apply (Nat.Prime.dvd_mul h2).mp at h1
          tauto
        tauto
      rcases h5 with (h5 | h5)
      · -- r divides 10
        have h6 : r = 2 ∨ r = 5 := by 
          have h1 : r ∣ 10 := by
            exact h5
          have h2 : r ≤ 10 := by 
            exact Nat.le_of_dvd (by norm_num) h1
          interval_cases r <;> norm_num at h1 ⊢ <;> try { tauto }
        tauto
      · -- r divides q
        tauto
    rcases h4 with (hr2 | hr5 | hrdv)
    · -- r = 2
      have h2 : r = 2 := hr2
      rw [h2] at eq4
      have h5 : q * 8 = 22 := by
        nlinarith [eq4]
      omega
    · -- r = 5
      have h5 : r = 5 := hr5
      rw [h5] at eq4
      have h7 : q = 11 := by
        nlinarith [eq4]
      exact_mod_cast h7
    · -- r divides q
      have h8 : r ∣ q := hrdv
      have h9 : r = 1 ∨ r = q := by 
        apply (Nat.dvd_prime hq).mp at h8 
        tauto
      rcases h9 with (h1 | h1)
      · -- r = 1
        have h4 : r = 1 := h1
        have h5 : r > 1 := by
          exact Nat.Prime.two_le hr
        nlinarith [h4, h5]
      · -- r = q
        have h5 : r = q := h1
        rw [h5] at eq4
        nlinarith [show q > 1 from Nat.Prime.two_le hq]
  have eq6 : r = 5 := by
    rw [eq5] at eq4
    nlinarith [eq4]
  have eq7 : p = 3 := by
    rw [eq5, eq6] at eq1
    nlinarith [eq1, Nat.Prime.two_le hp]
  have eq8 : A = 1980 := by
    rw [eq5, eq6, eq7] at h1
    linarith
  exact_mod_cast eq8