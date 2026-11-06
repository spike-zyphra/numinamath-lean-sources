import Mathlib

open Set Real

theorem algebra_301344 {A B : Set ℝ} (hA : A = {1, 2, 1 / 2}) (hB : B = {y | ∃ x ∈ A, y = x ^ 2}) :
    A ∩ B = {1} := by

  have h1 : B = {1, 4, 1 / 4} := by 
    rw [hB]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor 
    · -- If y ∈ B, then y ∈ {1, 4, 1/4}
      rintro ⟨x, hx, rfl⟩
      rw [hA] at hx
      rcases hx with (rfl | rfl | rfl)
      · -- Case x = 1 
        norm_num 
      · -- Case x = 2 
        norm_num 
      · -- Case x = 1/2 
        norm_num 
    · -- If y ∈ {1, 4, 1/4}, then y ∈ B
      rintro (rfl | rfl | rfl)
      · -- Case y = 1 
        use 1
        constructor 
        · -- Show 1 ∈ A 
          rw [hA]
          norm_num 
        · -- Show 1 = 1 ^ 2 
          norm_num 
      · -- Case y = 4 
        use 2 
        constructor 
        · -- Show 2 ∈ A 
          rw [hA]
          norm_num 
        · -- Show 4 = 2 ^ 2 
          norm_num 
      · -- Case y = 1/4 
        use 1 / 2 
        constructor 
        · -- Show 1/2 ∈ A 
          rw [hA]
          norm_num 
        · -- Show 1/4 = (1/2) ^ 2 
          norm_num 
  rw [h1]
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
  constructor 
  · -- Assume x ∈ A ∩ {1, 4, 1 / 4}
    rintro ⟨hx1, hx2⟩ 
    rw [hA] at hx1 
    rcases hx1 with (rfl | rfl | rfl)
    · -- Case x = 1 
      norm_num at hx2 ⊢ 
    · -- Case x = 2 
      norm_num at hx2 
    · -- Case x = 1 / 2 
      norm_num at hx2 
  · -- Assume x = 1 
    intro h 
    rw [h] 
    constructor 
    · -- Show 1 ∈ A 
      rw [hA]
      norm_num 
    · -- Show 1 ∈ {1, 4, 1 / 4} 
      norm_num