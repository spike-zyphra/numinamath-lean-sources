import Mathlib

theorem number_theory_216444 :
  {(x, y) : ℤ × ℤ | x^2 + 12 = y^4} = {(2, 2), (2, -2), (-2, 2), (-2, -2)} := by
  ext ⟨x, y⟩
  simp 
  constructor
  · -- Assume x^2 + 12 = y^4, prove (x, y) ∈ {(2, 2), (2, -2), (-2, 2), (-2, -2)}
    rintro H 
    have eq1 : y ^ 4 - x ^ 2 = 12 := by 
      nlinarith 
    have eq2 : (y^2 - x) * (y^2 + x) = 12 := by 
      nlinarith [eq1]
    have h1 : (y^2 - x) ∣ 12 := by 
      use (y^2 + x)
      all_goals linarith [eq2]
    have h2 : (y^2 - x) ∣ 12 := h1 
    -- From h1, we know y^2 - x divides 12, which gives us a finite set of possible values
    have h3 : (y^2 - x) ≤ 12 := by
      apply Int.le_of_dvd (by norm_num) h1
    have h4 : (y^2 - x) ≥ -12 := by 
      have h5 : - (y^2 - x) ∣ 12 := by 
        exact Int.neg_dvd.2 h1
      have h6 : - ((y^2 - x)) ≤ 12 := by 
        apply Int.le_of_dvd (by norm_num) h5
      linarith 
    interval_cases h9 : (y^2 - x) <;> try { 
      omega 
    } 
    <;> try { 
      have h_y2 : y ^ 2 ≤ 16 := by nlinarith 
      have h10 : y ≤ 4 := by nlinarith [sq_nonneg (y ^ 2 - 16 : ℤ)]
      have h11 : y ≥ -4 := by nlinarith [sq_nonneg (y ^ 2 - 16 : ℤ)]
      interval_cases y <;> norm_num at eq1 eq2 h9 ⊢ 
      <;> try { 
        omega 
      }
      <;> try { 
        have h8 : x ≤ 6 := by nlinarith
        have h9 : x ≥ -6 := by nlinarith 
        interval_cases x <;> omega 
      }
    }
  · -- Show the reverse direction: if (x, y) ∈ {(2, 2), (2, -2), (-2, 2), (-2, -2)}, then x^2 + 12 = y^4
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (2, 2)
      norm_num 
    · -- Check (2, -2)
      norm_num 
    · -- Check (-2, 2)
      norm_num 
    · -- Check (-2, -2)
      norm_num