import Mathlib

theorem number_theory_291653 (n : ℕ) (h : n > 10) (m : ℕ) (hm : m * n = 357) (o : ℕ) (ho : o * n = 441) :
    m + o = 38 := by
  have h1 : n ∣ 357 := by
    use m
    linarith
  have h2 : n ∣ 441 := by
    use o
    linarith

  have h3 : n = 21 := by
    have h4 : n ∣ 357 := h1
    have h5 : n ∣ 441 := h2
    have h6 : n > 10 := h

    -- Need to find the GCD of 357 and 441.
    have h7 : n ≤ 357 := by 
      exact Nat.le_of_dvd (by norm_num) h4
  
    interval_cases n <;> norm_num at h4 h5 <;> tauto
  -- Once n = 21 is proven, solve for m and o
  have h3' : m = 17 := by
    simp [h3] at hm
    omega
  have h4' : o = 21 := by
    simp [h3] at ho
    omega
  omega