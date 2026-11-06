import Mathlib

theorem number_theory_102963 :
    {(a, b) : ℤ × ℤ | 1 ≤ a ∧ a ≤ 30 ∧ 3 ≤ b ∧ b ≤ 30 ∧ a % b = 0 ∧ a % (b - 2) = 0}.ncard = 22 := by
  have h2 : {(a, b) : ℤ × ℤ | 1 ≤ a ∧ a ≤ 30 ∧ 3 ≤ b ∧ b ≤ 30 ∧ a % b = 0 ∧ a % (b - 2) = 0} = Finset.filter (fun p : ℤ × ℤ => 1 ≤ p.1 ∧ p.1 ≤ 30 ∧ 3 ≤ p.2 ∧ p.2 ≤ 30 ∧ p.1 % p.2 = 0 ∧ p.1 % (p.2 - 2) = 0) (Finset.Icc (1 : ℤ) 30 ×ˢ Finset.Icc (3 : ℤ) 30) := by
    ext ⟨a, b⟩
    simp
    <;> try { omega }
  rw [h2]
  rw [Set.ncard_coe_Finset]
  native_decide