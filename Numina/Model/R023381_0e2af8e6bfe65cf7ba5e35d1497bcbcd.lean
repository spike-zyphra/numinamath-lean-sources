import Mathlib

theorem algebra_3691 : ∑ᶠ k ∈ {k : ℤ | ∃ x y : ℕ, x + 2 * y = 6 ∧ y - 2 * x = 8 - 5 * k}, k = 10 := by
  have h1 : {k : ℤ | ∃ x y : ℕ, x + 2 * y = 6 ∧ y - 2 * x = 8 - 5 * k} = {1, 2, 3, 4} := by 
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor 
    · -- First direction: if (k, x, y) satisfy both equations, then k ∈ {1, 2, 3, 4}
      rintro ⟨x, y, h1, h2⟩
      have h3 : y ≤ 3 := by 
        omega 
      have h4 : x ≤ 6 := by 
        omega 
      interval_cases y <;> interval_cases x 
      <;> omega 
    · -- Second direction: if k ∈ {1, 2, 3, 4}, then there are x, y satisfy both equations
      rintro (rfl | rfl | rfl | rfl)
      · -- k = 1 
        refine ⟨0, 3, by norm_num, by norm_num⟩
      · -- k = 2 
        refine ⟨2, 2, by norm_num, by norm_num⟩
      · -- k = 3 
        refine ⟨4, 1, by norm_num, by norm_num⟩
      · -- k = 4 
        refine ⟨6, 0, by norm_num, by norm_num⟩
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp 
  <;> rfl