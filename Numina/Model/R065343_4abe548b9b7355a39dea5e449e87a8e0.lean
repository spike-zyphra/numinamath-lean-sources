import Mathlib

theorem number_theory_126596 :
    IsLeast {x | ∃ n : ℕ, x = n + (n + 1) + (n + 2) + (n + 3) ∧ ∀ i ∈ Finset.range 4, ¬Nat.Prime (n + i)} 102 := by
  constructor
  · -- First we prove that 102 is attainable
    use 24
    constructor
    · norm_num
    · intro i hi
      fin_cases hi <;> norm_num
  · -- Now we prove that 102 is the smallest
    intro x hx
    rcases hx with ⟨n, hn_eq, hn⟩
    by_contra h
    push_neg at h
    have h1 : n < 24 := by
      omega -- Solving 4n + 6 < 102, so n < 24
    have h2 := hn 0 (by simp)
    have h3 := hn 1 (by simp)
    have h4 := hn 2 (by simp)
    have h5 := hn 3 (by simp)
    interval_cases n <;> norm_num at hn_eq h2 h3 h4 h5 <;> try { omega } <;> tauto