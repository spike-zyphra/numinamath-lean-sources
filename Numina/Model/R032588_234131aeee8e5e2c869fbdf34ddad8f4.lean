import Mathlib

theorem number_theory_4844 (a k : ℕ) (h₀ : Odd k) (h₁ : a = 1183 * k) :
    Nat.gcd (2 * a ^ 2 + 29 * a + 65) (a + 13) = 26 := by
  rw [h₁]
  have h2 : (2 * (1183 * k) ^ 2 + 29 * (1183 * k) + 65 : ℕ) = (1183 * k + 13 : ℕ) * (2 * (1183 * k) + 3) + 26 := by
    ring_nf
  rw [h2]
  have h3 : Nat.gcd ((1183 * k + 13 : ℕ) * (2 * (1183 * k) + 3) + 26) (1183 * k + 13) = Nat.gcd 26 (1183 * k + 13) := by
    simp [Nat.gcd_comm, Nat.gcd_add_mul_left_right, Nat.gcd_add_mul_right_left]
  rw [h3]
  have h4 : (1183 * k + 13 : ℕ) % 2 = 0 := by
    have h5 : k % 2 = 1 := by
      obtain ⟨m, hm⟩ := h₀
      omega
    have h6 : (1183 * k : ℕ) % 2 = 1 := by
      simp [Nat.mul_mod, h5]
    omega
  have h7 : (1183 * k + 13 : ℕ) % 13 = 0 := by
    have h8 : 1183 % 13 = 0 := by norm_num
    have h9 : (1183 * k) % 13 = 0 := by
      simp [Nat.mul_mod, h8]
    omega
  have h10 : 26 ∣ (1183 * k + 13 : ℕ) := by
    omega
  have h11 : Nat.gcd 26 (1183 * k + 13) = 26 := by
    have h12 : 26 ∣ (1183 * k + 13 : ℕ) := h10
    have h14 : Nat.gcd 26 (1183 * k + 13) = 26 := by
      apply Nat.gcd_eq_left
      all_goals
        omega
    exact h14
  exact h11