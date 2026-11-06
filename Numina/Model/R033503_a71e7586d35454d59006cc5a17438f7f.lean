import Mathlib

theorem algebra_318674 {m n : ℕ} (hm : m > 0) (hn : n > 0)
    (h : (m * n + 9 * m + 11 * n + 145) = k * (m + 11)) (hk : k > 0)
    (h' : (m * n + 9 * m + 11 * n + 145) = k * (9 + n)) :
    k = 47 ∨ k = 25 := by

  have h8 : k * (m + 11) = k * (9 + n) := by 
    nlinarith 
  have h1 : m + 11 = 9 + n := by 
    apply (mul_left_inj' (show k ≠ 0 by linarith)).mp 
    linarith 
  have h2 : n = m + 2 := by 
    omega 
  rw [show n = m + 2 by omega] at h 
  have h3 : m * (m + 2) + 9 * m + 11 * (m + 2) + 145 = m^2 + 22 * m + 167 := by 
    nlinarith 
  have h4 : m^2 + 22 * m + 167 = k * (m + 11) := by 
    nlinarith [h, h3] 
  have h5 : m^2 + 22 * m + 167 = (m + 11)^2 + 46 := by 
    ring_nf 
  have h6 : k * (m + 11) = (m + 11)^2 + 46 := by 
    nlinarith [h4, h5]
  have h8 : (m + 11) ∣ 46 := by 
    have eq5 : k * (m + 11) - (m + 11)^2 = 46 := by 
      omega 
    have eq6 : (m + 11 : ℕ) ∣ (46 : ℕ) := by
      have eq7 : (m + 11 : ℕ) ∣ (k * (m + 11) - (m + 11)^2 : ℕ) := by 
        apply Nat.dvd_sub' 
        · -- Show that $m+11$ divides $k*(m+11)$ 
          use k 
          all_goals ring 
        · -- Show that $m+11$ divides $(m+11)^2$ 
          use (m + 11) 
          all_goals ring 
      have eq8 : (k * (m + 11) - (m + 11)^2 : ℕ) = 46 := by 
        omega 
      rw [eq8] at eq7 
      exact_mod_cast eq7 
    exact_mod_cast eq6 
  have h9 : (m + 11) ≤ 46 := by 
    exact Nat.le_of_dvd (by norm_num) h8 
  have h10 : (m + 11) ≥ 12 := by 
    omega 
  have h11 : (m + 11) = 23 ∨ (m + 11) = 46 := by 
    interval_cases h14 : (m + 11) <;> norm_num at h8 <;> omega 
  rcases h11 with h12 | h13 
  · -- Case m+11=23. 
    have eq1 : m + 11 = 23 := h12 
    have eq2 : k * 23 = 23^2 + 46 := by 
      rw [eq1] at h6 
      all_goals 
        nlinarith [h6]
    have eq3 : k = 25 := by 
      nlinarith 
    right 
    omega 
  · -- Case m+11=46. 
    have eq1 : m + 11 = 46 := h13 
    have eq2 : k * 46 = 46^2 + 46 := by 
      rw [eq1] at h6 
      all_goals 
        nlinarith [h6]
    have eq3 : k = 47 := by 
      nlinarith 
    left 
    omega