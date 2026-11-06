import Mathlib
theorem algebra_627974 {x y z : ℕ}
  (hx : x ≥ 1) (hy : y ≥ 1) (hz : z ≥ 1)
  (h : x * y * z + x * y + x * z + y * z + x + y + z = 1000) :
  x + y + z = 28 := by
  have h1 : (x + 1) * (y + 1) * (z + 1) = 1001 := by
    have eq1 : (x + 1) * (y + 1) * (z + 1) = x * y * z + x * y + x * z + y * z + x + y + z + 1 := by
      ring
    rw [eq1] at *
    omega
  have h2 : (x + 1) ∣ 1001 := by 
    use (y + 1) * (z + 1)
    all_goals nlinarith [h1]
  have h3 : (x + 1) ≤ 1001 := by 
    exact Nat.le_of_dvd (by norm_num) h2 
  have h4 : (x + 1) = 7 ∨ (x + 1) = 11 ∨ (x + 1) = 13 ∨ (x + 1) = 77 ∨ (x + 1) = 91 ∨ (x + 1) = 143 ∨ (x + 1) = 1001 := by 
    interval_cases k : (x + 1) <;> norm_num at h2 h1 <;> omega 
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4)
  · -- Assume (x + 1) = 7 
    have hx6 : x = 6 := by 
      omega 
    rw [show x + 1 = 7 by omega] at h1
    have h5 : (y + 1) * (z + 1) = 143 := by
      nlinarith
    have h7 : y + 1 ∣ 143 := by 
      use (z + 1)
      all_goals nlinarith [h5]
    have h8 : y + 1 ≤ 143 := by
      exact Nat.le_of_dvd (by norm_num) h7 
    interval_cases h9 : y + 1 <;> omega 
  · -- Assume (x + 1) = 11 
    have hx6 : x = 10 := by 
      omega 
    rw [show x + 1 = 11 by omega] at h1 
    have h5 : (y + 1) * (z + 1) = 91 := by 
      nlinarith 
    have h7 : y + 1 ∣ 91 := by 
      use (z + 1)
      all_goals nlinarith [h5]
    have h8 : y + 1 ≤ 91 := by 
      exact Nat.le_of_dvd (by norm_num) h7 
    interval_cases h9 : y + 1 <;> omega 
  · -- Assume (x + 1) = 13 
    have hx6 : x = 12 := by 
      omega 
    rw [show x + 1 = 13 by omega] at h1 
    have h5 : (y + 1) * (z + 1) = 77 := by 
      nlinarith 
    have h7 : y + 1 ∣ 77 := by 
      use (z + 1)
      all_goals nlinarith [h5] 
    have h8 : y + 1 ≤ 77 := by 
      exact Nat.le_of_dvd (by norm_num) h7 
    interval_cases h9 : y + 1 <;> omega 
  · -- Assume (x + 1) = 77 
    have hx6 : x = 76 := by 
      omega 
    rw [show x + 1 = 77 by omega] at h1
    have h5 : (y + 1) * (z + 1) = 13 := by
      nlinarith 
    have h7 : y + 1 ∣ 13 := by 
      use (z + 1)
      all_goals nlinarith [h5]
    have h8 : y + 1 ≤ 13 := by 
      exact Nat.le_of_dvd (by norm_num) h7 
    interval_cases h9 : y + 1 <;> omega 
  · -- Assume (x + 1) = 91 
    have hx6 : x = 90 := by 
      omega 
    rw [show x + 1 = 91 by omega] at h1 
    have h5 : (y + 1) * (z + 1) = 11 := by
      nlinarith 
    have h7 : y + 1 ∣ 11 := by 
      use (z + 1)
      all_goals nlinarith [h5] 
    have h8 : y + 1 ≤ 11 := by 
      exact Nat.le_of_dvd (by norm_num) h7 
    interval_cases h9 : y + 1 <;> omega 
  · -- Assume (x + 1) = 143 
    have hx6 : x = 142 := by 
      omega 
    rw [show x + 1 = 143 by omega] at h1
    have h5 : (y + 1) * (z + 1) = 7 := by
      nlinarith 
    have h7 : y + 1 ∣ 7 := by 
      use (z + 1)
      all_goals nlinarith [h5]
    have h8 : y + 1 ≤ 7 := by 
      exact Nat.le_of_dvd (by norm_num) h7 
    interval_cases h9 : y + 1 <;> omega 
  · -- Assume (x + 1) = 1001 
    have hx6 : x = 1000 := by 
      omega 
    rw [show x + 1 = 1001 by omega] at h1 
    have h5 : (y + 1) * (z + 1) = 1 := by 
      nlinarith 
    nlinarith