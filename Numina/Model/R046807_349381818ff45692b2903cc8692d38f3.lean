import Mathlib

theorem algebra_101158 (n : ℕ) (hn : n > 0) :
    ∃ x : Fin n → ℕ,
      (∀ i, x i > 0) ∧
      (∑ i, x i = 16) ∧
      (∑ i, (1 : ℚ)/(x i) = 1) ↔ n = 4 := by 
  by_cases h1 : n = 4
  · -- Assume n = 4, prove the equivalence.
    use λ i ↦ 4
    simp [h1]
    <;> try { native_decide }
  · -- Assume n ≠ 4
    use λ i ↦ 0
    simp at *
    <;> try { tauto }