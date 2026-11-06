import Mathlib

theorem number_theory_229755 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    24 ∣ (p - 1) * (p + 1) := by
  have h1 : p % 2 = 1 := by
    by_contra h2
    push_neg at h2
    have h4 : p % 2 = 0 := by
      omega
    have h5 : p > 2 := by linarith
    have h6 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h3
    push_neg at h3
    have h4 : p % 3 = 0 := by
      omega
    have h5 : p > 3 := by linarith
    have h6 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h3 : (p - 1) * (p + 1) % 3 = 0 := by
    rcases h2 with (h | h)
    · -- p ≡ 1 (mod 3)
      have h4 : p % 3 = 1 := by
        omega
      have h5 : (p - 1) % 3 = 0 := by
        omega
      simp [Nat.mul_mod, h5]
    · -- p ≡ 2 (mod 3)
      have h6 : p % 3 = 2 := by
        omega
      have h7 : (p + 1) % 3 = 0 := by
        omega
      simp [Nat.mul_mod, h7]
  have h4 : (p - 1) * (p + 1) % 8 = 0 := by
    have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      have h9 : p % 2 = 1 := h1
      omega
    rcases h8 with (h8 | h8 | h8 | h8)
    · -- p ≡ 1 (mod 8)
      have h9 : p % 8 = 1 := by
        omega
      have h10 : (p - 1) % 8 = 0 := by 
        omega
      simp [Nat.mul_mod, h10]
    · -- p ≡ 3 (mod 8)
      have h9 : p % 8 = 3 := by
        omega
      have h11 : (p - 1) % 8 = 2 := by
        omega
      have h12 : (p + 1) % 8 = 4 := by
        omega
      simp [Nat.mul_mod, h11, h12]
    · -- p ≡ 5 (mod 8)
      have h9 : p % 8 = 5 := by
        omega
      have h13 : (p - 1) % 8 = 4 := by
        omega
      have h14 : (p + 1) % 8 = 6 := by
        omega
      simp [Nat.mul_mod, h13, h14]
    · -- p ≡ 7 (mod 8)
      have h9 : p % 8 = 7 := by
        omega
      have h15 : (p + 1) % 8 = 0 := by
        omega
      simp [Nat.mul_mod, h15]
  omega