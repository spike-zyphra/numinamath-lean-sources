import Mathlib

theorem algebra_54662 {a b : ℤ} (ha : a > 0) (hb : b > 0)
    (h : 2 * a - 9 * b + 18 * a * b = 2018) : b - a = 223 := by
  have h1 : 18 * a * b + 2 * a - 9 * b = 2018 := by linarith 
  have eq1 : 2 * a * (9 * b + 1) = 2018 + 9 * b := by
    linarith [h1]

  have eq2 : (9 * b + 1) ∣ (2018 + 9 * b : ℤ) := by
    use 2 * a
    all_goals 
      linarith [eq1]

  have eq3 : (9 * b + 1) ∣ (2017 : ℤ) := by
    have h1 : (9 * b + 1) ∣ (2018 + 9 * b : ℤ) := eq2
    have h2 : (9 * b + 1) ∣ (1 * (9 * b + 1) : ℤ) := by
      simp
    have h3 : (9 * b + 1) ∣ ((2018 + 9 * b : ℤ) - (1 * (9 * b + 1) : ℤ)) := by
      apply Dvd.dvd.sub 
      · exact h1 
      · exact h2 
    have h4 : ((2018 + 9 * b : ℤ) - (1 * (9 * b + 1) : ℤ)) = (2017 : ℤ) := by 
      omega 
    rw [h4] at h3 
    exact h3 

  have eq4 : (9 * b + 1) = 1 ∨ (9 * b + 1) = 2017 := by 
    have h2017 : (9 * b + 1) ∣ (2017 : ℤ) := eq3 
    have hx1 : (9 * b + 1) ≤ (2017 : ℤ) := by 
      exact Int.le_of_dvd (by norm_num) h2017 
    have hx2 : (9 * b + 1) > (0 : ℤ) := by
      omega 
    interval_cases k : (9 * b + 1) <;> norm_num at h2017 ⊢ <;> tauto 

  rcases eq4 with h_eq | h_eq 
  · -- Case 9b + 1 = 1 
    have h_eq1 : 9 * b = 0 := by
      omega 
    have h_eq2 : b = 0 := by
      omega 
    linarith [hb, h_eq2] 
  · -- Case 9b + 1 = 2017 
    have h2b : b = 224 := by
      ring_nf at h_eq 
      omega 
    have h2a : a = 1 := by
      rw [h2b] at eq1
      norm_num at eq1 
      omega 
    have : b - a = 223 := by
      omega 
    exact_mod_cast this