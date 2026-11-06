import Mathlib

theorem algebra_287612 :
    {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * 10 + y * 5 + z = 120}.ncard = 121 := by 
  have h1 : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x * 10 + y * 5 + z = 120} = Finset.filter (fun s => 
    s.1 > 0 ∧ s.2.1 > 0 ∧ s.2.2 > 0 ∧ s.1 * 10 + s.2.1 * 5 + s.2.2 = 120
  ) (Finset.Icc (0 : ℕ) 12 ×ˢ (Finset.Icc (0 : ℕ) 24 ×ˢ Finset.Icc (0 : ℕ) 120)) := by
    ext ⟨x, y, z⟩
    simp 
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide