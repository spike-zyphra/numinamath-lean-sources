import Mathlib

theorem number_theory_277099 : {m : ℕ | ∃ n, m = n ^ 2} ∩ {32, 33, 34, 35, 36} = {36} := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_inter, Set.mem_singleton_iff, Set.mem_insert_iff, and_imp]
  constructor
  · -- Assume m is in the intersection
    intro h
    rcases h with ⟨⟨n, hn⟩, hm⟩
    rcases hm with (rfl | rfl | rfl | rfl | rfl)
    · -- m = 32
      exfalso
      have h1 : n ≤ 5 := by
        nlinarith
      interval_cases n <;> omega
    · -- m = 33
      exfalso
      have h1 : n ≤ 5 := by
        nlinarith
      interval_cases n <;> omega
    · -- m = 34
      exfalso
      have h1 : n ≤ 5 := by
        nlinarith
      interval_cases n <;> omega
    · -- m = 35
      exfalso
      have h1 : n ≤ 5 := by
        nlinarith
      interval_cases n <;> omega
    · -- m = 36
      omega
  · -- Assume m = 36
    intro h
    rw [h]
    constructor
    · -- Show that 36 is a perfect square
      use 6
      all_goals norm_num
    · -- Show that 36 is in the second set
      norm_num