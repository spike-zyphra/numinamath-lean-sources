import Mathlib

theorem number_theory_4971
    (a : ℕ → ℕ)
    (h_a0 : a 0 > 0)
    (h : ∀ j, a (j + 1) > 2 * a j)
    : ∀ i, a i > (∑ j ∈ Finset.range i, a j) := by 
  intro i 
  have h1 : ∀ i, a i > (∑ j ∈ Finset.range i, a j) := by 
    intro i 
    induction i with 
    | zero => 
      simp [h_a0]
    | succ k ih =>
      have h2 : a (k + 1) > 2 * a k := h k
      rw [Finset.sum_range_succ]
      linarith [ih, h2]
  specialize h1 i 
  simpa using h1