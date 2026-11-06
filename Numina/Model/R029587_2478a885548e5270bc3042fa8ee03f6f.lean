import Mathlib

theorem number_theory_254539 (n : ℕ) :
    n ∈ {x | x ∈ Finset.Icc 100 999 ∧ ∀ i ∈ Finset.Icc 2 6, x % i = i - 1} ↔
    n = 119 ∨ n = 179 ∨ n = 239 ∨ n = 299 ∨ n = 359 ∨ n = 419 ∨
      n = 479 ∨ n = 539 ∨ n = 599 ∨ n = 659 ∨ n = 719 ∨ n = 779 ∨
      n = 839 ∨ n = 899 ∨ n = 959 := by
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume n in the set, prove it's in the list
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, hn3⟩
    have h2 := hn3 2 (by norm_num)
    have h3 := hn3 3 (by norm_num)
    have h4 := hn3 4 (by norm_num)
    have h5 := hn3 5 (by norm_num)
    have h6 := hn3 6 (by norm_num)
    interval_cases n <;> norm_num at h2 h3 h4 h5 h6 ⊢ <;> omega
  · -- Show that each n in the list is in the set
    intro h
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      constructor
      · -- Show it's in the range [100, 999]
        norm_num
      · -- Show that it satisfies all congruences
        intro i hi
        rcases hi with ⟨h2, h6⟩
        have : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
          omega
        rcases this with (rfl | rfl | rfl | rfl | rfl) <;> norm_num