import Mathlib

theorem number_theory_19326 : {n : ℤ | 0 ≤ n ∧ n < 18 ∧ n ≡ -11213141 [ZMOD 18]} = {13} := by 
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor 
  · -- Assume n is in the set
    intro h
    rcases h with ⟨h0, h1, he⟩
    norm_num [Int.ModEq] at he 
    omega 
  · -- Assume n = 13
    intro h 
    rw [h]
    constructor 
    · norm_num
    constructor 
    · norm_num
    · norm_num [Int.ModEq]