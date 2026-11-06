import Mathlib

theorem algebra_3678 : {(a, b, c) : ℕ × ℕ × ℕ | a ≤ 8 ∧ b ≤ 8 ∧ c ≤ 4 ∧ 5*a+6*b+8*c=74}.ncard = 6 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a ≤ 8 ∧ b ≤ 8 ∧ c ≤ 4 ∧ 5*a+6*b+8*c=74} = Finset.filter (fun p => (p.1 ≤ 8) ∧ (p.2.1 ≤ 8) ∧ (p.2.2 ≤ 4) ∧ (5*p.1 + 6*p.2.1 + 8*p.2.2) = 74) (Finset.Icc (0 : ℕ) 8 ×ˢ (Finset.Icc (0 : ℕ) 8 ×ˢ Finset.Icc (0 : ℕ) 4)) := by
    ext ⟨a, b, c⟩
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide