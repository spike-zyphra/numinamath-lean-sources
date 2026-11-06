import Mathlib


lemma lemma_1 :
  ∀ x : ℤ, 2 * x ^ 2 - 11 * x + 15 ≥ 0 := by
  intro x
  have h1 : 2 * x ^ 2 - 11 * x + 15 = (x - 3) * (2 * x - 5) := by
    ring_nf
  rw [h1]
  by_cases h2 : x ≥ 3
  · 
    have h3 : (x - 3 : ℤ) ≥ 0 := by linarith
    have h4 : (2 * x - 5 : ℤ) ≥ 1 := by linarith
    nlinarith
  · 
    have h2' : x ≤ 2 := by omega
    have h3 : (x - 3 : ℤ) ≤ -1 := by omega
    have h4 : (2 * x - 5 : ℤ) ≤ -1 := by omega
    nlinarith


theorem inequalities_440 :
    Set.Infinite {x : ℤ | 3 * x - 4 ≤ (6 * x ^ 2 - 3 * x + 5) / 10} := by
  have h1 : {x : ℤ | 3 * x - 4 ≤ (6 * x ^ 2 - 3 * x + 5) / 10} = Set.univ := by
    ext x
    simp
    have h2 : 3 * x - 4 ≤ (6 * x ^ 2 - 3 * x + 5) / 10 := by
      have h3 : 2 * x ^ 2 - 11 * x + 15 ≥ 0 := lemma_1 x
      omega
    linarith
  rw [h1]
  apply Set.infinite_univ