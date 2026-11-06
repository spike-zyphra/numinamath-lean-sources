import Mathlib

theorem algebra_292563 (x y : ℤ) (hx : x > 0) (hy : y > 0) :
    x * (x + 2) ≠ y * (y + 1) := by
  intro h
  have h1 : x * (x + 2) = y * (y + 1) := h
  have h2 : (2 * (x + 1) : ℤ) ^ 2 - (2 * y + 1) ^ 2 = 3 := by
    nlinarith
  have h3 : ((2 * (x + 1) : ℤ) - (2 * y + 1 : ℤ)) * ((2 * (x + 1) : ℤ) + (2 * y + 1 : ℤ)) = 3 := by
    nlinarith
  have h4 : (2 * (x + 1) - (2 * y + 1) : ℤ) ∣ 3 := by
    use ( (2 * (x + 1) : ℤ) + (2 * y + 1 : ℤ) )
    nlinarith
  have h5 : (2 * (x + 1) - (2 * y + 1) : ℤ) ≤ 3 := by
    apply Int.le_of_dvd (show (0 : ℤ) < 3 by norm_num) h4
  have h6 : (2 * (x + 1) - (2 * y + 1) : ℤ) ≥ -3 := by
    have h61 : -( (2 * (x + 1) - (2 * y + 1) : ℤ) ) ∣ 3 := by
      apply Int.neg_dvd.2
      simpa using h4
    have h62 : -( (2 * (x + 1) - (2 * y + 1) : ℤ) ) ≤ 3 := by
      apply Int.le_of_dvd (show (0 : ℤ) < 3 by norm_num) h61
    omega
  interval_cases h7 : (2 * (x + 1) - (2 * y + 1) : ℤ) <;> omega