import Mathlib

theorem number_theory_269539 :
    IsLeast {n | ∃ k, n = ∑ i ∈ Finset.range 4, (k + i) ∧ ∀ i ∈ Finset.range 4, ¬Nat.Prime (k + i)} 102 := by 
  constructor
  · use 24
    constructor
    · native_decide
    · intro i hi
      fin_cases hi <;> norm_num
  · -- Assume n in the set. Show n >= 102.
    intro n hn
    rcases hn with ⟨k, hk, hk_composite⟩
    by_contra h
    push_neg at h
    -- Assume n < 102, get contradiction.
    have h1 : n < 102 := h
    have h2 : k < 24 := by
      have h3 : n = ∑ i in Finset.range 4, (k + i) := hk
      have h4 : n = 4 * k + 6 := by
        rw [h3]
        simp [Finset.sum_range_succ]
        <;> ring
      rw [h4] at h1
      omega
    -- Since k < 24, manually verify that in each interval [k, k + 3], there is at least one prime. 
    interval_cases k <;> try { contradiction }
    <;> norm_num [Finset.mem_range] at hk_composite <;> try { contradiction }
    <;> try { try { native_decide } <;> try { trivial } <;> try { contradiction } <;> try { tauto } }