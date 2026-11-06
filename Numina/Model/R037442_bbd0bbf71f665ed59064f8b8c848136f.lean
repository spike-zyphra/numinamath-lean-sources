import Mathlib

theorem algebra_236975 :
  {(x, y) : ℤ × ℤ | x * (x + 1) * (x + 7) * (x + 8) = y^2} =
  {(1, 12), (1, -12), (-9, 12), (-9, -12), (0, 0), (-8, 0), (-4 , -12), (-4 ,12), (-1, 0), (-7, 0)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- First direction: if (x,y) satisfies the equation, then (x,y) is in the set
    rintro h
    have h1 : x * (x + 1) * (x + 7) * (x + 8) = y^2 := h
    have eq1 : (2 * (x ^ 2 + 8 * x) + 7) ^ 2 - (2 * y) ^ 2 = 49 := by
      nlinarith [h1]
    have eq2 : (2 * (x ^ 2 + 8 * x) + 7 - 2 * y) * (2 * (x ^ 2 + 8 * x) + 7 + 2 * y) = 49 := by
      nlinarith [eq1]
    have h2 : (2 * (x ^ 2 + 8 * x) + 7 - 2 * y) * (2 * (x ^ 2 + 8 * x) + 7 + 2 * y) = 49 := eq2
    have h3 : (2 * (x ^ 2 + 8 * x) + 7 - 2 * y) ∣ 49 := by
      use (2 * (x ^ 2 + 8 * x) + 7 + 2 * y)
      all_goals nlinarith
    have h4 : (2 * (x ^ 2 + 8 * x) + 7 - 2 * y) ≤ 49 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : (2 * (x ^ 2 + 8 * x) + 7 - 2 * y) ≥ -49 := by
      have h6 : (- (2 * (x ^ 2 + 8 * x) + 7 - 2 * y) ) ∣ 49 := by
        exact Int.neg_dvd.2 h3
      have h7 : - (2 * (x ^ 2 + 8 * x) + 7 - 2 * y) ≤ 49 := by
        apply Int.le_of_dvd (by norm_num) h6
      linarith
    interval_cases h8 : (2 * (x ^ 2 + 8 * x) + 7 - 2 * y) <;> try { 
      omega 
    } <;> try { 
      norm_num at h2 ⊢ <;> 
      ring_nf at h2 ⊢ <;> 
      norm_num at h2 ⊢
      all_goals
        have : x ≤ 12 := by nlinarith
        have : x ≥ -12 := by nlinarith
        have : y ≤ 24 := by nlinarith
        have : y ≥ -24 := by nlinarith
        interval_cases x <;> try { 
          omega 
        } 
        <;> try { 
          interval_cases y <;> 
          omega 
        }
    }
  · -- Second direction: if (x,y) is in the set, then it satisfies the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num