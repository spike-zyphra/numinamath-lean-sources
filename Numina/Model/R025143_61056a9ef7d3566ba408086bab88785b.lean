import Mathlib

open Real

theorem inequalities_208365 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i j, i < j → a i ≥ a j) (hb : ∀ i, 0 < b i)
    (h : ∀ i, b i ≥ a i) (h' : ∀ i, ∏ j in Finset.univ.filter (· ≤ i), b j ≥ ∏ j in Finset.univ.filter (· ≤ i), a j) :
    ∑ i, b i ≥ ∑ i, a i ∧ (∑ i, b i = ∑ i, a i ↔ ∀ i, b i = a i) := by

  constructor
  · -- First part: prove $\sum_i b_i \geq \sum i, a i$
    have h1 : ∀ i, b i ≥ a i := h
    have h2 : ∑ i, b i ≥ ∑ i, a i := by
      apply Finset.sum_le_sum
      intro i hi
      exact h i
    linarith
  · -- Second part: prove $\sum i, b i = \sum i, a i \iff \forall i, b i = a i$
    constructor
    · -- Forward: $\sum i, b i = \sum i, a i \implies \forall i, b i = a i$
      intro heq
      have h_eq : ∀ (i : Fin n), b i = a i := by
        intro i
        have h3 : ∀ i : Fin n, b i ≥ a i := by
          intro i
          apply h i
        -- Since the total sum is equal, the difference is zero 
        have h5 : ∑ j : Fin n, (b j) - ∑ j : Fin n, (a j) = 0 := by
          linarith [heq, (show ∑ i, b i ≥ ∑ i, a i by
            apply Finset.sum_le_sum
            intro i hi
            exact h i
          )]
        have h6 : ∑ j : Fin n, (b j - a j) = 0 := by
          rw [Finset.sum_sub_distrib]
          simpa using h5
        have h7 : ∀ i : Fin n, 0 ≤ (b i - a i) := by
          intro i
          specialize h i
          linarith
        -- Each term in the sum must be zero since it's non-negative and the sum is zero
        have h8 : ∀ i : Fin n, b i - a i = 0 := by
          intro i
          have h10 : ∑ j : Fin n, (b j - a j) = 0 := h6
          have h11 : ∀ j : Fin n, (b j - a j) ≥ 0 := by
            intro j
            apply h7 j
          -- From equality deduce each term.
          have h14 : (b i - a i) = 0 := by
            have h15 : (b i - a i) ≤ 0 := by
              have h16 : (b i - a i) ≤ (∑ j : Fin n, (b j - a j)) := by
                have h17 : i ∈ (Finset.univ : Finset (Fin n)) := by 
                  simp
                have h18 : 0 ≤ (b i - a i) := by
                  apply h7 i 
                have h19 : ∀ j, j ∈ (Finset.univ : Finset (Fin n)) → 0 ≤ (b j - a j) := by
                  intro j hj
                  apply h7 j 
                apply Finset.single_le_sum h19 h17
              rw [h10] at h16
              linarith
            have h18 : (b i - a i) ≥ 0 := by
              apply h7 i 
            linarith 
          linarith 
        have h21 : b i - a i = 0 := h8 i
        linarith 
      simpa [h_eq]
    · -- Backward: $\forall i, b i = a i \implies \sum i, b i = \sum i, a i$
      intro h_eq
      have h2 : ∀ i : Fin n, b i = a i := h_eq
      have h3 : ∑ i, b i = ∑ i, a i := by
        apply Finset.sum_congr 
        · rfl 
        · intro i hi 
          exact h2 i 
      linarith