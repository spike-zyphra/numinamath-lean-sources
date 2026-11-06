import Mathlib

theorem number_theory_12916 :
    ∑ᶠ n ∈ {n : ℕ | 0 < n ∧ 2 * n ^ 2 + 3 * n + 5 ≡ 0 [MOD 7] ∧ 2000 ≤ n ∧ n ≤ 2020}, n = 2006 + 2013 + 2020 + 2000 + 2007 + 2014 := by 
  have h1 : {n : ℕ | 0 < n ∧ 2 * n ^ 2 + 3 * n + 5 ≡ 0 [MOD 7] ∧ 2000 ≤ n ∧ n ≤ 2020} = {2006, 2013, 2020, 2000, 2007, 2014} := by
    ext n
    simp [Nat.ModEq]
    constructor
    · -- Assume n is in {n : ℕ | 0 < n ∧ 2 * n ^ 2 + 3 * n + 5 ≡ 0 [MOD 7] ∧ 2000 ≤ n ∧ n ≤ 2020}
      intro h
      rcases h with ⟨hn_pos, hn_mod, hn_le, hn_le2⟩
      interval_cases n <;> try { contradiction } <;> tauto
    · -- Assume n is in {2006, 2013, 2020, 2000, 2007, 2014}
      intro h
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num [Nat.ModEq]
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num [Nat.ModEq]
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num [Nat.ModEq]
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num [Nat.ModEq]
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num [Nat.ModEq]
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num [Nat.ModEq]
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Finset.sum_insert, Finset.sum_singleton]
  all_goals
  try { try { native_decide } <;> norm_num }
  all_goals
  trivial <;> norm_num
  all_goals
  simp [Finset.sum_insert, Finset.sum_singleton]
  all_goals
  trivial <;> norm_num