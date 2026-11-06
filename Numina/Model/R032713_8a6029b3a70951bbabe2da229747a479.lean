import Mathlib

theorem number_theory_110991 (x y : ℕ) : x^2 ∣ x^2 + x * y + x + y → x^2 ∣ x + y := by 
  intro h
  have eq1 : x ^ 2 + x * y + x + y = (x + 1) * (x + y) := by
    ring_nf
    <;> omega
  rw [eq1] at h
  have h1 : Nat.Coprime (x ^ 2) (x + 1) := by
    have h2 : Nat.Coprime x (x + 1) := by
      simp [Nat.coprime_iff_gcd_eq_one]
      <;> omega
    have h3 : Nat.Coprime (x ^ 2) (x + 1) := by
      apply Nat.Coprime.pow_left
      exact h2
    exact h3
  have h2 : x ^ 2 ∣ x + y := by
    apply Nat.Coprime.dvd_of_dvd_mul_left h1
    simpa using h
  exact h2