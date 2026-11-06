import Mathlib

theorem algebra_129645 (father_age : ℕ) (children_age : Fin 3 → ℕ)
    (h₀ : father_age = 46) (h₁ : ∑ i, children_age i = 22) :
    father_age + 12 = ∑ i, (children_age i + 12) := by 
  rw [h₀]
  simp [Finset.sum_add_distrib, h₁]
  <;> try { rfl }
  <;> try { omega }