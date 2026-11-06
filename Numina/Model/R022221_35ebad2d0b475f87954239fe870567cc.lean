import Mathlib

theorem number_theory_142606 (m : ℕ) (hm : m > 0) :
    ∃ k : ℕ, (∏ i ∈ Finset.Icc 1000 2014, i) / (∏ i ∈ Finset.range m, 7) = k ↔
    m ≤ 169 := by
  have h1 : m > 0 := hm
  by_cases h2 : m ≤ 169
  · -- If m ≤ 169, then the quotient is a natural number k
    use (∏ i ∈ Finset.Icc 1000 2014, i) / (∏ i ∈ Finset.range m, 7)
    all_goals
      simp [h2]
      <;> try { 
        native_decide
      }
  · -- If m > 169, the quotient is not a natural number, so the claim is false
    push_neg at h2
    use (∏ i ∈ Finset.Icc 1000 2014, i) / (∏ i ∈ Finset.range m, 7) + 1
    all_goals
      simp [h2]
      <;> try { 
        native_decide
      }