import Mathlib

theorem number_theory_7723 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h₁ : (7 * p + q).Prime) (h₂ : (p * q + 11).Prime) :
    (p ^ 2 + q ^ p) * (q ^ 2 + p ^ q) = 221 := by
  have h : ¬ (Odd p ∧ Odd q) := by
    intro ⟨hp₂, hq₂⟩
    have h₃ : Even (p * q + 11) := Odd.add_odd (Odd.mul hp₂ hq₂) (Nat.odd_iff.mpr rfl)
    have h₄ : p * q + 11 = 2 := (Nat.Prime.even_iff h₂).mp h₃
    omega
  obtain hp₂ | hq₂ : Even p ∨ Even q := by
    rw [← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even]
    exact Decidable.not_and_iff_or_not.mp h
  . obtain rfl : p = 2 := (Nat.Prime.even_iff hp).mp hp₂
    mod_cases q % 3
    . simp [Nat.modEq_zero_iff_dvd] at H
      obtain rfl : 3 = q := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp H
      simp
    . simp [Nat.ModEq] at H
      have h₃ : 3 ∣ 7 * 2 + q := by omega
      have h₄ : 3 = 7 * 2 + q := (Nat.prime_dvd_prime_iff_eq (by norm_num) h₁).mp h₃
      omega
    . simp [Nat.ModEq] at H
      have h₃ : 3 ∣ 2 * q + 11 := by omega
      have h₄ : 3 = 2 * q + 11 := (Nat.prime_dvd_prime_iff_eq (by norm_num) h₂).mp h₃
      omega
  . obtain rfl : q = 2 := (Nat.Prime.even_iff hq).mp hq₂
    mod_cases p % 3
    . simp [Nat.modEq_zero_iff_dvd] at H
      obtain rfl : 3 = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp H
      simp
    . simp [Nat.ModEq] at H
      have h₃ : 3 ∣ 7 * p + 2 := by omega
      have h₄ : 3 = 7 * p + 2 := (Nat.prime_dvd_prime_iff_eq (by norm_num) h₁).mp h₃
      omega
    . simp [Nat.ModEq] at H
      have h₃ : 3 ∣ p * 2 + 11 := by omega
      have h₄ : 3 = p * 2 + 11 := (Nat.prime_dvd_prime_iff_eq (by norm_num) h₂).mp h₃
      omega
