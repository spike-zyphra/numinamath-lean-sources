import Mathlib

theorem algebra_13489 : IsLeast {m : ℕ | ∃ x : ℤ, 10 * x ^ 2 - m * x + 420 = 0} 130 := by
  constructor
  · -- Show 130 is in the set
    use 7
    all_goals
      norm_num
  · -- Show no smaller m is in the set
    intro m hm
    rcases hm with ⟨x, hx⟩
    by_contra h
    push_neg at h
    have h1 : m < 130 := by 
      omega 
    have eq1 : (10 : ℤ) * x ^ 2 - (m : ℤ) * x + 420 = 0 := by 
      simpa using hx 
    have h5 : x ∣ 420 := by
      use m - 10 * x 
      nlinarith 
    have h6 : x ≤ 420 := by
      apply Int.le_of_dvd (by norm_num) h5
    have h7 : x ≥ -420 := by 
      have h7 : (-x) ∣ 420 := by 
        exact Int.neg_dvd.2 h5 
      have h8 : -x ≤ 420 := by
        apply Int.le_of_dvd (by norm_num) h7 
      omega 
    have h8 : x ≤ 420 := by 
      apply Int.le_of_dvd (by norm_num) h5 
    interval_cases x <;> omega