import Mathlib

theorem number_theory_11280 : {n : ℤ | 0 ≤ n ∧ n ≤ 9 ∧ n ≡ -2187 [ZMOD 10]} = {3} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Proof that if n ∈ {n : ℤ | 0 ≤ n ∧ n ≤ 9 ∧ n ≡ -2187 [ZMOD 10]} then n = 3
    intro h
    rcases h with ⟨h0, h1, h2⟩
    norm_num [Int.ModEq] at h2
    omega
  · -- Proof that if n = 3 then n ∈ {n : ℤ | 0 ≤ n ∧ n ≤ 9 ∧ n ≡ -2187 [ZMOD 10]}
    intro h
    rw [h]
    constructor
    · -- Show that 0 ≤ 3
      norm_num
    constructor
    · -- Show that 3 ≤ 9
      norm_num
    · -- Show that 3 ≡ -2187 [ZMOD 10]
      norm_num [Int.ModEq]