import Mathlib

theorem algebra_228567 (a : ℤ) :
    (∃ x1 x2 : ℤ, x1^2 - (3 + a)*x1 + 3*a + 3 = 0 ∧ x2^2 - (3 + a)*x2 + 3*a + 3 = 0) ↔
    a = -1 ∨ a = 7 := by
  constructor
  · -- Assume there's integer solutions
    intro h
    rcases h with ⟨x1, x2, hx1, hx2⟩
    have eq1 : (x1 - 3) * (x1 - a) = -3 := by
      nlinarith
    have eq2 : (x2 - 3) * (x2 - a) = -3 := by
      nlinarith
    have h1 : (x1 - 3) ∣ -3 := by
      use (x1 - a)
      all_goals linarith
    have h1' : (x1 - 3) ∣ 3 := by
      have h11 : (x1 - 3) ∣ -3 := h1
      have : (x1 - 3) ∣ 3 := by
        exact Int.dvd_neg.mp h11
      assumption
    have h2 : (x1 - 3) ≤ 3 := by 
      apply Int.le_of_dvd (by norm_num) h1'
    have h3 : (x1 - 3) ≥ -3 := by
      have h5 : (- (x1 - 3)) ∣ 3 := by 
        exact Int.neg_dvd.2 h1'
      have h6 : (- (x1 - 3)) ≤ 3 := by
        apply Int.le_of_dvd (by norm_num) h5
      omega
    interval_cases h5 : x1 - 3 <;> omega
  · -- Assume a = -1 or 7, prove there's integer solutions
    rintro (h | h)
    · -- a = -1
      rw [h]
      use 2, 0
      constructor
      · -- Check equation for x1 = 2
        norm_num
      · -- Check equation for x2 = 0
        norm_num
    · -- a = 7
      rw [h]
      use 4, 6
      constructor
      · -- Check equation for x1 = 4
        norm_num
      · -- Check equation for x2 = 6
        norm_num