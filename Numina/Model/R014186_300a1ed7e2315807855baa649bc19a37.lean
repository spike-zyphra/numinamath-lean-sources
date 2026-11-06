import Mathlib

theorem algebra_2126 : {a : ℤ | ∃ x y, x ≠ y ∧ x^2 + a * x - 12 = 0 ∧ y^2 + a * y - 12 = 0}.ncard = 6 := by
  have h1 : {a : ℤ | ∃ x y, x ≠ y ∧ x^2 + a * x - 12 = 0 ∧ y^2 + a * y - 12 = 0} = {1, -1, 4, -4, 11, -11} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: if a exists, then a must be in the explicit set
      intro h
      rcases h with ⟨x, y, hxy, hx, hy⟩
      have h2 : a = -(x + y) := by
        have h3 : (x - y) * (x + y + a) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h3) with h4 h5
        · 
          omega -- This side is x - y = 0, which implies x = y, a contradiction
        · 
          linarith [h5]
      have h3 : x * y = -12 := by
        rw [h2] at hx
        nlinarith
      have h4 : x ∣ 12 := by
        use -y
        nlinarith
      have h5 : x ∣ 12 := h4
      have h6 : x ≤ 12 := by 
        exact Int.le_of_dvd (show (0 : ℤ) < 12 by norm_num) h5
      have h7 : x ≥ -12 := by 
        have h8 : (-x) ∣ 12 := by
          exact Int.neg_dvd.2 h5
        have h9 : -x ≤ 12 := by 
          exact Int.le_of_dvd (show (0 : ℤ) < 12 by norm_num) h8
        omega 
      interval_cases x <;> omega
    · -- Second direction: if a is in the explicit set, then it satisfies the property
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- a = 1 
        use 3, -4 
        all_goals norm_num 
      · -- a = -1 
        use 4, -3 
        all_goals norm_num 
      · -- a = 4 
        use 2, -6 
        all_goals norm_num 
      · -- a = -4 
        use 6, -2 
        all_goals norm_num 
      · -- a = 11 
        use 1, -12 
        all_goals norm_num 
      · -- a = -11 
        use 12, -1 
        all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }