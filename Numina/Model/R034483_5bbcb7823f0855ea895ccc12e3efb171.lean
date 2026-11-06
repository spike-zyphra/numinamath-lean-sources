import Mathlib

theorem number_theory_96531 : { (x, y) : ℕ × ℕ | 1 <= y ∧ y < x ∧ x ≤ 100 ∧ y ∣ x ∧ (y + 1) ∣ (x + 1) }.ncard = 85 := by
  have h1 : { (x, y) : ℕ × ℕ | 1 <= y ∧ y < x ∧ x ≤ 100 ∧ y ∣ x ∧ (y + 1) ∣ (x + 1) } = Finset.filter (fun p : ℕ × ℕ => 1 <= p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 100 ∧ p.2 ∣ p.1 ∧ (p.2 + 1) ∣ (p.1 + 1)) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨x, y⟩
    simp
    <;> try { omega }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide