import Mathlib

theorem algebra_283211 : {(x, y) : ℤ × ℤ | |x| + |y| - 3 = 0}.encard = 12 := by
  have h1 : {(x, y) : ℤ × ℤ | |x| + |y| - 3 = 0} = 
        {(-3, 0), (-2, -1), (-2, 1), (-1, -2), (-1, 2), (0, -3), (0, 3), (1, -2), (1, 2), (2, -1), (2, 1), (3, 0)
        } := by
    ext ⟨x, y⟩
    simp 
    constructor
    · -- Assume |x| + |y| - 3 = 0, prove (x, y) is in the finite set
      intro h
      have h2 : |x| + |y| = 3 := by linarith [h]
      have h3 : x ≤ 3 := by 
        cases' abs_cases x with hx hx
        · -- Case x ≥ 0
          cases' abs_cases y with hy hy
          · -- Case y ≥ 0
            omega
          · -- Case y < 0
            omega
        · -- Case x < 0
          cases' abs_cases y with hy hy
          · -- Case y ≥ 0
            omega
          · -- Case y < 0
            omega
      have h4 : x ≥ -3 := by 
        cases' abs_cases x with hx hx
        · -- Case x ≥ 0
          cases' abs_cases y with hy hy
          · -- Case y ≥ 0
            omega
          · -- Case y < 0
            omega
        · -- Case x < 0
          cases' abs_cases y with hy hy
          · -- Case y ≥ 0
            omega
          · -- Case y < 0
            omega
      have h5 : y ≤ 3 := by 
        cases' abs_cases y with hy hy
        · -- Case y ≥ 0
          cases' abs_cases x with hx hx
          · -- Case x ≥ 0
            omega
          · -- Case x < 0
            omega
        · -- Case y < 0
          cases' abs_cases x with hx hx
          · -- Case x ≥ 0
            omega
          · -- Case x < 0
            omega
      have h6 : y ≥ -3 := by 
        cases' abs_cases y with hy hy
        · -- Case y ≥ 0
          cases' abs_cases x with hx hx
          · -- Case x ≥ 0
            omega
          · -- Case x < 0
            omega
        · -- Case y < 0
          cases' abs_cases x with hx hx
          · -- Case x ≥ 0
            omega
          · -- Case x < 0
            omega
      interval_cases x <;> 
      interval_cases y 
        <;> norm_num at h2 ⊢ 
          <;> tauto 
    · -- Assume (x, y) is in the finite set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }