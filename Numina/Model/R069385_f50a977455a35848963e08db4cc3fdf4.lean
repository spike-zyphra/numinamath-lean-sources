import Mathlib

theorem number_theory_286844 (k : ℕ) (hk : 3 ≤ k) :
    ∃ a d : ℚ, ∀ i ∈ Finset.range k, ∃ n : ℕ, a + d * i = 1 / (n + 1) := by 
  use 1 / (k : ℚ)
  use 0
  intro i hi
  use k - 1
  simp at hi ⊢
  <;> field_simp
  <;> omega