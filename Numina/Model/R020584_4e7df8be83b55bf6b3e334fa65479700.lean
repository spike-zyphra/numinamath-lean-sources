import Mathlib

theorem number_theory_1102 (n : ℕ) (h₀ : n ∈ Finset.Icc 1 100) :
    (∑ i ∈ Finset.Icc 1 100 \ {n}, i) % 98 = n % 98 ↔ n = 26 ∨ n = 75 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨hn1, hn2⟩
  constructor
  · -- Forward implication
    intro h
    have h1 : (5050 - n) % 98 = n % 98 := by
      have eq3 : ∑ i ∈ Finset.Icc 1 100, i = 5050 := by native_decide
      have h2 : ∑ i ∈ Finset.Icc 1 100 \ {n}, i = 5050 - n := by 
        have h3 : n ∈ (Finset.Icc 1 100 : Finset ℕ) := by simp [Finset.mem_Icc]; omega
        have eq1 : ∑ i ∈ Finset.Icc 1 100 \ {n}, i = (∑ i ∈ Finset.Icc 1 100, i) - n := by
          have h3' : n ∈ (Finset.Icc 1 100 : Finset ℕ) := h3
          rw [← Finset.sum_sdiff (show {n} ⊆ Finset.Icc (1 : ℕ) 100 by
              intro x hx
              simp at hx
              rw [Finset.mem_Icc]
              omega
            )]
          simp [h3']
          <;> try { assumption }
          <;> try { omega }
          all_goals try { tauto }
        rw [eq1, eq3]
        <;> try { tauto }
        <;> try { nlinarith }
      -- Simplify the sum 
      have h4 : (∑ i ∈ Finset.Icc 1 100 \ {n}, i) % 98 = n % 98 := h
      rw [h2] at h4
      omega
    have h2 : n = 26 ∨ n = 75 := by 
      omega
    tauto
  · -- Backward implication
    rintro (h | h)
    · -- Assume n = 26
      rw [h]
      native_decide
    · -- Assume n = 75
      rw [h]
      native_decide