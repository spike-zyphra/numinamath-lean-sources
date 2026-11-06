import Mathlib

theorem number_theory_226679 :
    {x : ℤ | ⌊x / 2⌋ + ⌊x / 4⌋ = x} = {0, -3, -2, -5} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume x in the left side, prove right side
    intro h_eq
    have h1 : ⌊x / 2⌋ + ⌊x / 4⌋ = x := by
      exact_mod_cast h_eq
    have h2 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2)
    · -- Case 1: x % 4 = 0
      have h3 : ∃ k : ℤ, x = 4 * k := by
        refine' ⟨x / 4, by 
          omega
        ⟩
      rcases h3 with ⟨k, h3⟩
      have h4 : ⌊x / 2⌋ = 2 * k := by 
        rw [h3]
        norm_num [Int.floor_eq_iff]
        <;> omega
      have h5 : ⌊x / 4⌋ = k := by 
        rw [h3]
        norm_num [Int.floor_eq_iff]
        <;> omega
      rw [h4, h5] at h1
      have : k = 0 := by
        omega
      subst k
      omega
    · -- Case 2: x % 4 = 1
      have h3 : ∃ k : ℤ, x = 4 * k + 1 := by
        refine' ⟨(x - 1) / 4, by 
          omega
        ⟩
      rcases h3 with ⟨k, h3⟩
      have h4 : ⌊x / 2⌋ = 2 * k := by
        rw [h3]
        norm_num [Int.floor_eq_iff]
        <;> omega
      have h5 : ⌊x / 4⌋ = k := by 
        rw [h3]
        norm_num [Int.floor_eq_iff]
        <;> omega
      rw [h4, h5] at h1
      have : k = -1 := by 
        omega
      subst k
      omega
    · -- Case 3: x % 4 = 2
      have h3 : ∃ k : ℤ, x = 4 * k + 2 := by
        refine' ⟨(x - 2) / 4, by 
          omega
        ⟩
      rcases h3 with ⟨k, h3⟩
      have h4 : ⌊x / 2⌋ = 2 * k + 1 := by 
        rw [h3]
        norm_num [Int.floor_eq_iff]
        <;> omega
      have h5 : ⌊x / 4⌋ = k := by 
        rw [h3]
        norm_num [Int.floor_eq_iff]
        <;> omega
      rw [h4, h5] at h1
      have : k = -1 := by
        omega
      subst k
      omega
    · -- Case 4: x % 4 = 3
      have h3 : ∃ k : ℤ, x = 4 * k + 3 := by
        refine' ⟨(x - 3) / 4, by 
          omega
        ⟩
      rcases h3 with ⟨k, h3⟩
      have h4 : ⌊x / 2⌋ = 2 * k + 1 := by 
        rw [h3]
        norm_num [Int.floor_eq_iff]
        <;> omega
      have h5 : ⌊x / 4⌋ = k := by 
        rw [h3]
        norm_num [Int.floor_eq_iff]
        <;> omega
      rw [h4, h5] at h1
      have : k = -2 := by 
        omega
      subst k
      omega
    -- Backward direction: the right side implies the left side
  · -- Assume right side, prove left side
    rintro (h | h | h | h)
    · -- Case 0
      rw [h]
      all_goals norm_num
    · -- Case -3
      rw [h]
      all_goals norm_num
    · -- Case -2
      rw [h]
      all_goals norm_num
    · -- Case -5
      rw [h]
      all_goals norm_num