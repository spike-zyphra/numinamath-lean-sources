import Mathlib

theorem algebra_176866 :
    Set.ncard {p : ℤ × ℤ | p.1 ^ 2 - p.2 ^ 2 = 12} = 4 := by
  have h1 : {p : ℤ × ℤ | p.1 ^ 2 - p.2 ^ 2 = 12} = { (4, 2), (4, -2), (-4, -2), (-4, 2) } := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- First, showing that if (x, y) is a solution, then it's in the right side.
      rintro h
      have h2 : (x - y) * (x + y) = 12 := by
        linarith [h]
      have h3 : x - y ∣ 12 := by
        use x + y
        all_goals nlinarith
      have h4 : x - y ≤ 12 := by
        apply Int.le_of_dvd (by norm_num) h3
      have h5 : x - y ≥ -12 := by
        have h6 : -(x - y) ∣ 12 := by
          exact Int.neg_dvd.2 h3
        have h7 : -(x - y) ≤ 12 := by
          apply Int.le_of_dvd (by norm_num) h6
        linarith
      interval_cases h6 : x - y <;> try { 
        omega
      }
      <;> try { 
        all_goals nlinarith
      }
    · -- Second direction: if (x, y) is in the right side, it's a solution.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { 
    native_decide
  }
  <;> try { 
    all_goals native_decide
  }