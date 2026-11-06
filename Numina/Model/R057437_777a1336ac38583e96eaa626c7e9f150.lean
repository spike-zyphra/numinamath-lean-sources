import Mathlib

theorem algebra_13567 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 3 * x + 6 * y = 66}.ncard = 10 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 3 * x + 6 * y = 66} = Finset.filter (fun p => (p.1 > 0 ∧ p.2 > 0 ∧ 3 * p.1 + 6 * p.2 = 66)) (Finset.Icc (0 : ℕ) 22 ×ˢ Finset.Icc (0 : ℕ) 11) := by
    ext ⟨x, y⟩
    simp
    omega
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide