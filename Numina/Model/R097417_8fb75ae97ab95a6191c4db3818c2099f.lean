import Mathlib

theorem number_theory_266360 :
    Set.ncard {n : ℕ | n > 25 ∧ ∃ b g, b > 2 ∧ b < 10 ∧ g > 14 ∧ g < 23 ∧ n = b + g} = 6 := by
  have h1 : {n : ℕ | n > 25 ∧ ∃ b g, b > 2 ∧ b < 10 ∧ g > 14 ∧ g < 23 ∧ n = b + g} = {26, 27, 28, 29, 30, 31} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n in the original set
      intro h
      rcases h with ⟨hn1, ⟨b, g, h2, h3, h4, h5, heq⟩⟩
      have hb1 : b ≥ 3 := by linarith
      have hb2 : b ≤ 9 := by linarith
      have hg1 : g ≥ 15 := by linarith
      have hg2 : g ≤ 22 := by linarith
      have h6 : n ≥ 26 := by omega
      have h7 : n ≤ 31 := by omega
      interval_cases n <;> try { tauto }
      <;> omega
    · -- Assume n in {26, 27, 28, 29, 30, 31}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 26
        exact ⟨by norm_num, ⟨4, 22, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 27
        exact ⟨by norm_num, ⟨5, 22, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 28
        exact ⟨by norm_num, ⟨6, 22, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 29
        exact ⟨by norm_num, ⟨7, 22, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 30
        exact ⟨by norm_num, ⟨8, 22, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
      · -- n = 31
        exact ⟨by norm_num, ⟨9, 22, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]