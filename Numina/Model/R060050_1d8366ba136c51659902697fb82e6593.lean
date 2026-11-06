import Mathlib

theorem number_theory_285985 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 2 * x + 3 * y = 2007}.encard = 334 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 2 * x + 3 * y = 2007} = Finset.filter (fun p => (p.1 > 0 ∧ p.2 > 0 ∧ 2 * p.1 + 3 * p.2 = 2007)) (Finset.Icc (0 : ℕ) 2007 ×ˢ Finset.Icc (0 : ℕ) 2007) := by
    ext ⟨x, y⟩
    simp
    omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide