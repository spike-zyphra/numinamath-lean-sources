import Mathlib

theorem algebra_108869 {x y : ℕ} (h : (x + y) * (x - y) = 23) :
    (x + y) / (x - y) = 23 := by
  have h1 : (x + y) ∣ 23 := by
    use (x - y)
    all_goals nlinarith
  have h2 : (x + y) = 1 ∨ (x + y) = 23 := by
    have h1' : (x + y) ∣ 23 := h1
    have h3 : (x + y) ≤ 23 := by
      exact Nat.le_of_dvd (by norm_num) h1'
    interval_cases h4 : (x + y) <;> omega
  rcases h2 with (h3 | h3)
  · -- assume (x + y) = 1
    have h4 : (x - y) = 23 := by
      rw [h3] at h
      nlinarith
    have h5 : x ≤ y := by
      omega
    have h6 : (x - y) = 0 := by
      omega
    omega
  · -- assume (x + y) = 23
    have h7 : (x - y) = 1 := by
      rw [h3] at h
      nlinarith
    -- Now compute the quotient
    have h8 : (x - y) = 1 := h7
    have h9 : (x + y) = 23 := h3
    rw [h8]
    all_goals norm_num [h9]