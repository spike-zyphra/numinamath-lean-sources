import Mathlib

theorem algebra_118219 (m : ℕ) (hm : m > 0) (x y : ℤ) (h : 13 * x + 11 * y = 700) (h' : y = m * x - 1) :
    m = 6 := by 
  rw [h'] at h 
  have h1 : (13 + 11 * (m : ℤ)) * x = 711 := by 
    linarith 
  have h2 : (13 + 11 * (m : ℤ)) ∣ 711 := by 
    use x 
    linarith 
  have h3 : (13 + 11 * (m : ℤ)) > 0 := by 
    nlinarith 
  have h4 : (13 + 11 * (m : ℤ)) ≤ 711 := by 
    apply Int.le_of_dvd (by norm_num) h2 
  have h5 : (13 + 11 * (m : ℤ)) = 79 := by 
    interval_cases h6 : (13 + 11 * (m : ℤ)) <;> 
      omega 
  have h6 : (m : ℤ) = 6 := by 
    linarith 
  have h7 : m = 6 := by 
    exact_mod_cast h6 
  exact h7