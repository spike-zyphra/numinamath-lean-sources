import Mathlib

theorem number_theory_287499 :
  {n : ℕ | n ∈ Finset.Icc 100 999 ∧
    ∃ a b c : ℕ, a ≥ 1 ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ 
    n = 100 * a + 10 * b + c ∧
    (64 * a + 8 * c + b) = n ∧
    (36 * b + 6 * a + c) = n - 16 ∧
    (16 * c + 4 * b + a) = n + 18} = {139} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n is in the left side, prove n = 139
    rintro ⟨⟨hn1, hn2⟩, ⟨a, b, c, ha1, ha2, hb, hc, hn, h1, h2, h3⟩⟩
    omega
  · -- Assume n = 139, prove the membership
    intro h
    rw [h]
    constructor
    · norm_num
    · use 1, 3, 9
      all_goals norm_num