import Mathlib


theorem number_theory_155115  (a b : ℤ) (apos : 0 < a) (bpos : 0 < b) (h: a^2 - b^4 = 2009) :  a + b = 47 := by

  have h1 : a^2 = b^4 + 2009 := by
    linarith
  have h5 : a > b^2 := by
    have h6 : a^2 > b^4 := by
      nlinarith
    nlinarith [sq_nonneg (a - b^2), sq_nonneg (b^2), sq_pos_of_pos apos, sq_pos_of_pos (show 0 < b by linarith)]
  
  have h2 : (a - b^2) * (a + b^2) = 2009 := by
    nlinarith

  have h3 : (a - b^2) ∣ 2009 := by
    use (a + b^2)
    all_goals
      nlinarith

  have h4 : (a - b^2) ≤ 2009 := by
    exact Int.le_of_dvd (by norm_num) h3

  have h9 : (a - b^2) > 0 := by nlinarith

  have h14 : (a - b^2) = 1 ∨ (a - b^2) = 7 ∨ (a - b^2) = 41 ∨ (a - b^2) = 49 ∨ (a - b^2) = 287 ∨ (a - b^2) = 2009 := by
    have h30 : (a - b^2) ∣ 2009 := h3
    have h31 : (a - b^2) ≥ 1 := by omega
    have h32 : (a - b^2) ≤ 2009 := by
      exact Int.le_of_dvd (by norm_num) h30
    interval_cases h33 : (a - b^2) <;> tauto
  rcases h14 with (h14 | h14 | h14 | h14 | h14 | h14)
  · -- case `a - b^2 = 1` 
    have h15 : (a + b^2) = 2009 := by
      rw [show (a - b^2) = 1 by linarith [h14]] at h2
      linarith
    have h16 : b^2 = 1004 := by
      nlinarith
    have h30 : b ≤ 31 := by
      nlinarith [sq_nonneg (b - 31 : ℤ), sq_nonneg (b + 31 : ℤ), sq_nonneg (b ^ 2 - 1004 : ℤ)]
    have h31 : b ≥ -31 := by
      nlinarith [sq_nonneg (b - 31 : ℤ), sq_nonneg (b + 31 : ℤ), sq_nonneg (b ^ 2 - 1004 : ℤ)]
    interval_cases b <;> omega
  · -- case `a - b^2 = 7` 
    have h15 : (a + b^2) = 287 := by
      rw [show (a - b^2) = 7 by linarith [h14]] at h2
      linarith
    have h16 : b^2 = 140 := by
      nlinarith
    have h30 : b ≤ 11 := by
      nlinarith [sq_nonneg (b - 11 : ℤ), sq_nonneg (b + 11 : ℤ), sq_nonneg (b ^ 2 - 140 : ℤ)]
    have h31 : b ≥ -11 := by
      nlinarith [sq_nonneg (b - 11 : ℤ), sq_nonneg (b + 11 : ℤ), sq_nonneg (b ^ 2 - 140 : ℤ)]
    interval_cases b <;> omega
  · -- case `a - b^2 = 41` 
    have h15 : (a + b^2) = 49 := by
      rw [show (a - b^2) = 41 by linarith [h14]] at h2
      linarith
    have h16 : b^2 = 4 := by
      nlinarith
    have h17 : b = 2 := by
      have h20 : b > 0 := by nlinarith
      have h21 : b ≤ 2 := by
        nlinarith [sq_nonneg (b ^ 2 - 4 : ℤ), sq_nonneg (b - 2 : ℤ)]
      interval_cases b <;> omega
    have h18 : a = 45 := by
      nlinarith
    linarith
  · -- case `a - b^2 = 49` 
    have h15 : (a + b^2) = 41 := by
      rw [show (a - b^2) = 49 by linarith [h14]] at h2
      linarith
    nlinarith
  · -- case `a - b^2 = 287` 
    have h15 : (a + b^2) = 7 := by
      rw [show (a - b^2) = 287 by linarith [h14]] at h2
      linarith
    nlinarith
  · -- case `a - b^2 = 2009` 
    have h15 : (a + b^2) = 1 := by
      rw [show (a - b^2) = 2009 by linarith [h14]] at h2
      linarith
    nlinarith