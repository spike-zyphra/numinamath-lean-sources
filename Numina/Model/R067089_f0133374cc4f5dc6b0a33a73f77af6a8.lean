import Mathlib

theorem number_theory_200904 :
    {(x, y, z) : ℕ × ℕ × ℕ | x ∈ Finset.Icc 1 10 ∧ y ∈ Finset.Icc 1 10 ∧ z ∈ Finset.Icc 1 10 ∧ 9 ∣ (x ^ 3 + y ^ 3 + z ^ 3)}.ncard = 243 := by 
  have : {(x, y, z) : ℕ × ℕ × ℕ | x ∈ Finset.Icc 1 10 ∧ y ∈ Finset.Icc 1 10 ∧ z ∈ Finset.Icc 1 10 ∧ 9 ∣ (x ^ 3 + y ^ 3 + z ^ 3)} = Finset.filter (fun s => 9 ∣ (s.1 ^ 3 + s.2.1 ^ 3 + s.2.2 ^ 3)) (Finset.Icc (1 : ℕ) 10 ×ˢ Finset.Icc (1 : ℕ) 10 ×ˢ Finset.Icc (1 : ℕ) 10) := by
    ext ⟨x, y, z⟩
    simp [Finset.mem_Icc]
    <;> omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide