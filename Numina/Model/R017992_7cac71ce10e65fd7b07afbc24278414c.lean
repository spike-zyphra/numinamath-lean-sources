import Mathlib

theorem number_theory_60654 (p q r s : ℤ) (h₀ : ¬ 5 ∣ s)
    (h₁ : ∃ a, 5 ∣ p * a ^ 3 + q * a ^ 2 + r * a + s) :
    ∃ b, 5 ∣ s * b ^ 3 + r * b ^ 2 + q * b + p := by

  rcases h₁ with ⟨a, h⟩
  have h2 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
    omega
  rcases h2 with (h2 | h2 | h2 | h2 | h2)
  · -- a ≡ 0 (mod 5)
    exfalso
    have h3 : a % 5 = 0 := h2
    have h4 : (p * a ^ 3 + q * a ^ 2 + r * a + s) % 5 = 0 := by
      omega
    have h5 : s % 5 = 0 := by
      simp [pow_two, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h3] at h4 ⊢
      omega
    have h7 : 5 ∣ s := by
      omega
    contradiction
  · -- a ≡ 1 (mod 5)
    use 1
    have h4 : (p * a ^ 3 + q * a ^ 2 + r * a + s) % 5 = 0 := by
      omega
    simp [h2, pow_two, pow_succ, Int.add_emod, Int.mul_emod] at h4 ⊢
    all_goals omega
  · -- a ≡ 2 (mod 5)
    use 3
    have h4 : (p * a ^ 3 + q * a ^ 2 + r * a + s) % 5 = 0 := by
      omega
    simp [h2, pow_two, pow_succ, Int.add_emod, Int.mul_emod] at h4 ⊢
    all_goals omega
  · -- a ≡ 3 (mod 5)
    use 2
    have h4 : (p * a ^ 3 + q * a ^ 2 + r * a + s) % 5 = 0 := by
      omega
    simp [h2, pow_two, pow_succ, Int.add_emod, Int.mul_emod] at h4 ⊢
    all_goals omega
  · -- a ≡ 4 (mod 5)
    use 4
    have h4 : (p * a ^ 3 + q * a ^ 2 + r * a + s) % 5 = 0 := by
      omega
    simp [h2, pow_two, pow_succ, Int.add_emod, Int.mul_emod] at h4 ⊢
    all_goals omega