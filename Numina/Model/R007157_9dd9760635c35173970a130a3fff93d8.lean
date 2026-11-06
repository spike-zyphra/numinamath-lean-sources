import Mathlib

theorem number_theory_14901 : {n : ℤ | n ∈ Set.Icc 0 7 ∧ n ≡ -3737 [ZMOD 8]} = {7} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_Icc]
  constructor
  · -- Assume n ∈ {n ∈ ℤ | n ∈ Set.Icc 0 7 ∧ n ≡ -3737 [ZMOD 8]}, show n = 7
    intro h
    rcases h with ⟨⟨hn0, hn7⟩, hneq⟩
    norm_num [Int.ModEq] at hneq
    omega
  · -- Assume n = 7, show n ∈ {n ∈ ℤ | n ∈ Set.Icc 0 7 ∧ n ≡ -3737 [ZMOD 8]}
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num [Int.ModEq]