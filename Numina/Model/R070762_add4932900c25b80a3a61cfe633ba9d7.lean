import Mathlib

theorem number_theory_7695 :
    Set.ncard {n : ℕ | 0 < n ∧ 10 ≤ 3 * n ∧ 3 * n < 100 ∧ 100 ≤ 9 * n ∧ 9 * n < 1000} = 22 := by 
  have h1 : {n : ℕ | 0 < n ∧ 10 ≤ 3 * n ∧ 3 * n < 100 ∧ 100 ≤ 9 * n ∧ 9 * n < 1000} = Set.Icc 12 33 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3, h4, h5⟩
      omega
    · intro h
      omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide