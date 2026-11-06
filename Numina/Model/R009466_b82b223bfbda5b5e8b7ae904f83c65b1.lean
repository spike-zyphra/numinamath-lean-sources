import Mathlib

theorem algebra_96742 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x + 2 * y = 100}.ncard = 49 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x + 2 * y = 100} = Finset.filter (fun p => (p.1 > 0 ∧ p.2 > 0 ∧ p.1 + 2 * p.2 = 100)) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 50) := by
    ext ⟨x, y⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide