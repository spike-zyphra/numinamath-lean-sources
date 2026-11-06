import Mathlib

theorem algebra_3437 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x * y + x - 7 * y = 23}.ncard = 4 := by 
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x * y + x - 7 * y = 23} = {(15, 1), (11, 3), (9, 7), (8, 15)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume ⟨x, y⟩ satisfies the equation; prove it is one of the four pairs.
      rintro ⟨hx, hy, heq⟩
      have h2 : x * y + x = 7 * y + 23 := by
        omega
      have h3 : x ≤ 30 := by 
        by_contra h
        push_neg at h
        have h4 : y ≤ 7 := by
          nlinarith [show x * y + x = 7 * y + 23 from h2]
        interval_cases y <;> omega
      have h4 : y ≤ 23 := by
        by_contra h
        push_neg at h
        have h5 : x ≤ 7 := by 
          nlinarith [show x * y + x = 7 * y + 23 from h2]
        interval_cases x <;> omega
      interval_cases x <;> try { 
        omega 
      } <;> try { 
        interval_cases y 
        <;> norm_num at h2 <;> tauto 
      }
    · -- Show the four pairs satisfy the condition
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (15, 1)
        constructor
        · norm_num -- x>0
        constructor
        · norm_num -- y>0
        · -- Check equation
          omega
      · -- Check (11, 3)
        constructor
        · norm_num -- x>0
        constructor
        · norm_num -- y>0
        · -- Check equation
          omega
      · -- Check (9, 7)
        constructor
        · norm_num -- x>0
        constructor
        · norm_num -- y>0
        · -- Check equation
          omega
      · -- Check (8, 15)
        constructor
        · norm_num -- x>0
        constructor
        · norm_num -- y>0
        · -- Check equation
          omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }