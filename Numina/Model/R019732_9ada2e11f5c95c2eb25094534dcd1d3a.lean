import Mathlib

theorem algebra_175172 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a + b < 100 ∧ a + 1 / (b : ℚ) = 13 * (b + 1 / (a : ℚ))}.ncard = 7 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a + b < 100 ∧ a + 1 / (b : ℚ) = 13 * (b + 1 / (a : ℚ))} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 < 100 ∧ (p.1 : ℚ) + 1 / (p.2 : ℚ) = 13 * (p.2 + 1 / (p.1 : ℚ))) (Finset.Icc (0 : ℕ) 99 ×ˢ Finset.Icc (0 : ℕ) 99) := by
    ext ⟨a, b⟩
    simp
    intro h1 h2 h3 h4
    have h5 : a ≤ 99 := by
      omega
    have h6 : b ≤ 99 := by
      omega
    tauto

  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide