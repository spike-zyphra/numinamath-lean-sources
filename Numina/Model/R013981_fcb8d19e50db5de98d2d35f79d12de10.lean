import Mathlib

theorem number_theory_146105 : {k : ℕ | k ≤ 445000 ∧ (445 : ℤ) ∣ (k ^ 2 - 1)}.encard = 4000 := by
  have h1 : {k : ℕ | k ≤ 445000 ∧ (445 : ℤ) ∣ (k ^ 2 - 1)} = Finset.filter (fun (k : ℕ) => (445 : ℤ) ∣ (k ^ 2 - 1)) (Finset.Iic 445000) := by
    ext k
    simp
    <;> tauto

  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide