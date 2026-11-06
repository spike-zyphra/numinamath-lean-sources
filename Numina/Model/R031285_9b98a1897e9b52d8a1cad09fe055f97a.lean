import Mathlib

theorem algebra_97297 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a + b ≤ 100 ∧
    ((a:ℚ) + 1 / b) / (1 / a + (b:ℚ)) = 13}.ncard = 7 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a + b ≤ 100 ∧
      ((a:ℚ) + 1 / b) / (1 / a + (b:ℚ)) = 13} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ p.1 + p.2 ≤ 100 ∧
      ((p.1:ℚ) + 1 / p.2) / (1 / p.1 + (p.2:ℚ)) = 13) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide