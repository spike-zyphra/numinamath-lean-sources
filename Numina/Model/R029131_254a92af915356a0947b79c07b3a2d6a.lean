import Mathlib


theorem number_theory_611130
  : IsGreatest { ∑ i ∈ Finset.range 2003, (i * (n i)) |
                 n ∈ { n : ℕ → ℕ | ∑ i ∈ Finset.range 2003, ((i + 1) * (n i)) = 2003}} 2002 := by 
  constructor
  · -- Show that 2002 is in the set.
    use (λ i => if i = 2002 then 1 else 0)
    native_decide
  · -- Show that 2002 is greatest in the set
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    have h1 : ∑ i in Finset.range 2003, ((i + 1) * (n i)) = 2003 := hn
    have h2 : ∑ i in Finset.range 2003, (i * (n i)) ≤ 2002 := by
      have h3 : ∑ i in Finset.range 2003, ((i + 1) * (n i)) = ∑ i in Finset.range 2003, (i * (n i)) + ∑ i in Finset.range 2003, (n i) := by
        have h4 : ∀ i : ℕ, (i + 1) * (n i) = i * (n i) + (n i) := by
          intro i
          ring
        calc
          ∑ i in Finset.range 2003, ((i + 1) * (n i))
              = ∑ i in Finset.range 2003, (i * (n i) + (n i)) := by
                apply Finset.sum_congr rfl
                intro i hi
                specialize h4 i
                linarith
          _ = ∑ i in Finset.range 2003, (i * (n i)) + ∑ i in Finset.range 2003, (n i) := by
            rw [Finset.sum_add_distrib]
      have h4 : ∑ i in Finset.range 2003, (n i) ≥ 1 := by
        by_contra h
        push_neg at h
        have h7 : ∑ i in Finset.range 2003, (n i) = 0 := by
          omega
        have h8 : ∀ i ∈ Finset.range 2003, n i = 0 := by
          intro i hi
          have h14 : ∑ j in Finset.range 2003, (n j) = 0 := h7
          have h14 : ∀ j ∈ Finset.range 2003, n j = 0 := by
            intro j hj
            have h15 : n j ≤ ∑ k in Finset.range 2003, (n k) := by
              apply Finset.single_le_sum (fun x hx => by simp) (show j ∈ Finset.range 2003 by simpa using hj)
            rw [h14] at h15
            omega
          specialize h14 i (show i ∈ Finset.range 2003 by simpa using hi)
          assumption
        have h15 : ∑ i in Finset.range 2003, ((i + 1) * (n i)) = 0 := by
          have h12 : ∀ i ∈ Finset.range 2003, n i = 0 := h8
          have h13 : ∀ i ∈ Finset.range 2003, (i + 1) * (n i) = 0 := by
            intro i hi
            rw [h12 i hi]
            simp
          apply Finset.sum_eq_zero
          intro i hi
          exact h13 i hi
        omega
      omega
    linarith