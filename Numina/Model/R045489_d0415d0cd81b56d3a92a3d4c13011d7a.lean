import Mathlib
open Real
theorem algebra_309962 {a b c m n : ℤ} (h1 : ∀ x : ℤ, x ^ 2 + a * x + b = (x - m) * (x - n)) (h2 : ∀ x : ℤ, x ^ 2 + c * x + a = (x - m - 1) * (x - n - 1)) : a + b + c = -3 ∨ a + b + c = 29:= by

  have eq1 := h1 0
  have eq2 := h1 1
  have eq3 := h2 0
  have eq4 := h2 1

  have eq5 : b = m * n := by 
    nlinarith 
  have eq6 : a = (m + 1) * (n + 1) := by
    nlinarith 
  have eq7 : 1 + c + a = m * n := by 
    nlinarith 
  have eq8 : a = -m - n := by 
    have eq9 : 1 + a + b = (1 - m) * (1 - n) := by
      nlinarith 
    rw [show b = m * n by linarith [eq5]] at eq9 
    nlinarith 
  have eq9 : m * n + 2 * m + 2 * n + 1 = 0 := by
    have eq10 : (m + 1) * (n + 1) = -m - n := by
      linarith [eq6, eq8]
    nlinarith 
  have eq10 : (m + 2) * (n + 2) = 3 := by
    nlinarith 
  have eq11 : (m + 2) ∣ 3 := by
    use (n + 2)
    all_goals 
      linarith [eq10]

  have h3 : (m + 2) = 1 ∨ (m + 2) = 3 ∨ (m + 2) = -1 ∨ (m + 2) = -3 := by
    have h4 : (m + 2) ∣ 3 := eq11
    have h5 : (m + 2) ≤ 3 := by 
      apply Int.le_of_dvd (by norm_num) h4
    have h6 : (m + 2) ≥ -3 := by
      have h7 : -(m + 2) ∣ 3 := by
        exact Int.neg_dvd.2 h4
      have h8 : -(m + 2) ≤ 3 := by
        apply Int.le_of_dvd (by norm_num) h7
      omega
    interval_cases h9 : (m + 2) <;> tauto

  rcases h3 with (h3 | h3 | h3 | h3)
  · -- Case m + 2 = 1 
    have hm1 : m = -1 := by 
      omega 
    have hn1 : n = 1 := by 
      have h9 : (n + 2) = 3 := by 
        rw [show (m + 2) = 1 by linarith [h3]] at eq10 
        linarith 
      omega 
    have ha1 : a = 0 := by 
      rw [hm1, hn1] at eq8 
      linarith 
    have hb1 : b = -1 := by 
      rw [hm1, hn1] at eq5 
      nlinarith 
    have hc1 : c = -2 := by 
      nlinarith [eq7, ha1, hb1, hm1, hn1] 
    left 
    linarith [ha1, hb1, hc1] 
  · -- Case m + 2 = 3 
    have hm1 : m = 1 := by 
      omega 
    have hn1 : n = -1 := by 
      have h9 : (n + 2) = 1 := by 
        rw [show (m + 2) = 3 by linarith [h3]] at eq10 
        linarith 
      omega 
    have ha1 : a = 0 := by 
      rw [hm1, hn1] at eq8 
      linarith 
    have hb1 : b = -1 := by 
      rw [hm1, hn1] at eq5 
      nlinarith 
    have hc1 : c = -2 := by 
      nlinarith [eq7, ha1, hb1, hm1, hn1] 
    left 
    linarith [ha1, hb1, hc1] 
  · -- Case m + 2 = -1 
    have hm1 : m = -3 := by 
      omega 
    have hn1 : n = -5 := by 
      have h9 : (n + 2) = -3 := by 
        rw [show (m + 2) = -1 by linarith [h3]] at eq10 
        linarith 
      omega 
    have ha1 : a = 8 := by 
      rw [hm1, hn1] at eq8 
      linarith 
    have hb1 : b = 15 := by 
      rw [hm1, hn1] at eq5 
      nlinarith 
    have hc1 : c = 6 := by 
      nlinarith [eq7, ha1, hb1, hm1, hn1] 
    right 
    linarith [ha1, hb1, hc1] 
  · -- Case m + 2 = -3 
    have hm1 : m = -5 := by 
      omega 
    have hn1 : n = -3 := by 
      have h9 : (n + 2) = -1 := by 
        rw [show (m + 2) = -3 by linarith [h3]] at eq10 
        linarith 
      omega 
    have ha1 : a = 8 := by 
      rw [hm1, hn1] at eq8 
      linarith 
    have hb1 : b = 15 := by 
      rw [hm1, hn1] at eq5 
      nlinarith 
    have hc1 : c = 6 := by 
      nlinarith [eq7, ha1, hb1, hm1, hn1] 
    right 
    linarith [ha1, hb1, hc1]