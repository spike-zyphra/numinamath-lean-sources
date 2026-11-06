import Mathlib

theorem number_theory_167175 (a b : ℤ) :
    a^3 + 5 * b^3 ≠ 2016 := by
  rintro h
  have h1 : a^3 + 5 * b^3 = 2016 := by linarith
  have h2 : a^3 % 9 = 0 ∨ a^3 % 9 = 1 ∨ a^3 % 9 = 8 := by
    have h3 : a % 9 = 0 ∨ a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 3 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 6 ∨ a % 9 = 7 ∨ a % 9 = 8 := by
      omega
    rcases h3 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have h3 : b^3 % 9 = 0 ∨ b^3 % 9 = 1 ∨ b^3 % 9 = 8 := by
    have h4 : b % 9 = 0 ∨ b % 9 = 1 ∨ b % 9 = 2 ∨ b % 9 = 3 ∨ b % 9 = 4 ∨ b % 9 = 5 ∨ b % 9 = 6 ∨ b % 9 = 7 ∨ b % 9 = 8 := by
      omega
    rcases h4 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have h4 : (a^3 : ℤ) % 9 = 0 := by
    omega
  have h5 : (b^3 : ℤ) % 9 = 0 := by
    omega
  have h6 : 9 ∣ a^3 := by
    omega
  have h7 : 9 ∣ b^3 := by
    omega
  have h8 : 3 ∣ a := by
    have h90 : a^3 % 3 = 0 := by
      omega
    have h30 : a % 3 = 0 := by
      have h31 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
        omega
      rcases h31 with (h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod] at h90 <;> try { omega }
    have : 3 ∣ a := by
      omega
    assumption
  have h9 : 3 ∣ b := by
    have h90 : b^3 % 3 = 0 := by
      omega
    have h30 : b % 3 = 0 := by
      have h31 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
        omega
      rcases h31 with (h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod] at h90 <;> try { omega }
    have : 3 ∣ b := by
      omega
    assumption
  rcases h8 with ⟨k, hk⟩
  rcases h9 with ⟨m, hm⟩
  rw [show a = 3 * k by linarith, show b = 3 * m by linarith] at h1
  ring_nf at h1
  omega