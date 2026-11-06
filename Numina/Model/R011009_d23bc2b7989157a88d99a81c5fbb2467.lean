import Mathlib

theorem number_theory_215847: {n: ℕ | ∃ a b c d: ℕ, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9
 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ (a + 1) * (b + 2) * (c + 3) * (d + 4) = 234} = {2009, 1109} := by 
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First, prove that if n is in the set, then n ∈ {2009, 1109}
    rintro ⟨a, b, c, d, ha1, ha2, hb, hc, hd, hn, heq⟩
    interval_cases a <;> interval_cases b <;> interval_cases c <;> omega
  · -- Now prove the reverse direction: if n ∈ {2009, 1109}, then n is in the set
    rintro (rfl | rfl)
    · -- Let n = 2009
      refine' ⟨2, 0, 0, 9, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · -- Let n = 1109
      refine' ⟨1, 1, 0, 9, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  <;> norm_num
  all_goals norm_num