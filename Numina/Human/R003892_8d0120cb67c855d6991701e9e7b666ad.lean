import Mathlib

theorem number_theory_219619 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : 100^2 + 1^2 = p * q ∧ 65^2 + 76^2 = p * q) :
    p + q = 210 := by
  have h₁ : p * q = 137 * 73 := by linarith only [h.1]
  have h₂ : 137 ∣ p * q := by rw [h₁]; exact Nat.dvd_mul_right _ _
  obtain h₃ | h₃ := (Nat.Prime.dvd_mul (by norm_num)).1 h₂
  . rw [Nat.prime_dvd_prime_iff_eq (by norm_num) hp] at h₃
    subst h₃
    omega
  . rw [Nat.prime_dvd_prime_iff_eq (by norm_num) hq] at h₃
    subst h₃
    omega
