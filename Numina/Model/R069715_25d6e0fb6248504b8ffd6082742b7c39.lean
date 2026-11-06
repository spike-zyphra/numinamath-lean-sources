import Mathlib
open Real

theorem number_theory_188 :
    (Set.ncard {x : ℕ | x ∈ Set.Icc 1 6 ∧ ∃ k, k^2 = x}) / 6 = 1 / 3 := by

  have h1 : {x : ℕ | x ∈ Set.Icc 1 6 ∧ ∃ k, k^2 = x} = {1, 4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · -- Assume x ∈ {x : ℕ | x ∈ Set.Icc 1 6 ∧ ∃ k, k^2 = x}
      rintro ⟨⟨hx1, hx2⟩, ⟨k, rfl⟩⟩
      have h2 : k ≤ 2 := by
        by_contra h
        push_neg at h
        have h3 : k ≥ 3 := by omega
        -- Need to prove k^2 > 6 for k >= 3
        have h4 : k ^ 2 ≥ 9 := by
          have h5 : k ≥ 3 := by linarith
          have h6 : k ^ 2 ≥ 3 ^ 2 := by
            nlinarith [show k ≥ 0 from by omega]
          nlinarith
        linarith
      -- We need to show k = 1 or k = 2
      have h7 : k = 1 ∨ k = 2 := by
        -- Because k is a natural number and k <= 2
        have h8 : k ≤ 2 := h2
        have h9 : k ≥ 1 := by
          -- We need to prove k >= 1
          by_contra h
          push_neg at h
          have h10 : k = 0 := by linarith
          -- If k = 0 then k^2 = 0 contradicts with 1 <= x
          have h11 : k ^ 2 = 0 := by
            calc
              k ^ 2 = 0 ^ 2 := by rw [h10]
              _ = 0 := by norm_num
          omega
        interval_cases k <;> tauto
      rcases h7 with (rfl | rfl)
      · -- k = 1
        omega
      · -- k = 2
        omega
    · -- Assume x ∈ {1, 4}
      rintro (rfl | rfl)
      · -- x = 1
        constructor
        · -- Show 1 ∈ [1, 6]
          norm_num
        · -- Show ∃k, k^2 = 1
          use 1
          all_goals norm_num
      · -- x = 4
        constructor
        · -- Show 4 ∈ [1, 6]
          norm_num
        · -- Show ∃k, k^2 = 4
          use 2
          all_goals norm_num

  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals try { rfl <;> tauto }
  all_goals try { linarith }
  <;> rfl
  all_goals tauto