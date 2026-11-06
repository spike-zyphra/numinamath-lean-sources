import Mathlib

open Real

theorem inequalities_123734 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∑ i, a i * b i > 0 := by
  have h1 : ∀ i : Fin n, a i * b i > 0 := by
    intro i
    have ha1 : a i > 0 := ha i
    have hb1 : b i > 0 := hb i
    exact mul_pos ha1 hb1
  have h2 : ∑ i : Fin n, a i * b i > 0 := by
    apply Finset.sum_pos
    · -- Show that each term in the sum is positive
      intro i hi
      specialize h1 i
      simpa using h1
    · -- Show that the index set is non-empty
      use ⟨0, hn⟩
      simp
  exact h2