import Mathlib

theorem algebra_107312 {p q a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hroots : a^2 + p * a + q = 0 ∧ b^2 + p * b + q = 0)
    (hne : a ≠ b) (hdiv : (a + p) % (q - 2 * b) = 0) :
    a = 3 ∨ a = 1 := by
  rcases hroots with ⟨ha_eq, hb_eq⟩
  have h1 : p = -a - b := by 
    have eq1 : a^2 + p * a + q - (b^2 + p * b + q) = 0 := by linarith
    have eq2 : (a - b) * (a + b + p) = 0 := by
      nlinarith 
    have h2 : a - b ≠ 0 := by 
      intro h
      apply hne 
      linarith 
    have h3 : a + b + p = 0 := by 
      apply (mul_eq_zero.mp eq2).resolve_left 
      exact h2 
    linarith 
  have h2 : q = a * b := by 
    rw [h1] at ha_eq 
    nlinarith 
  have eq1 : a + p = -b := by 
    rw [h1] 
    linarith 
  have eq2 : q - 2 * b = b * (a - 2) := by 
    rw [h2]
    all_goals linarith 
  rw [eq1, eq2] at hdiv 
  have h3 : b * (a - 2) ∣ -b := by 
    exact Int.dvd_of_emod_eq_zero hdiv 
  have h5 : (a - 2) ∣ -1 := by 
    have h7 : b * (a - 2) ∣ -b := h3 
    obtain ⟨k, hk⟩ := h7
    have eq3 : (-b) = (b * (a - 2)) * k := by 
      linarith [hk]
    have h8 : b ≠ 0 := hb 
    have : -1 = (a - 2) * k := by
      apply (mul_left_inj' h8).mp 
      linarith 
    have : (a - 2) ∣ -1 := by 
      use k 
      all_goals linarith 
    assumption 
  have h6 : (a - 2) ∣ 1 := by 
    exact Int.dvd_neg.mp h5 
  have h7 : (a - 2) = 1 ∨ (a - 2) = -1 := by 
    have h8 : (a - 2) ≤ 1 := by 
      exact Int.le_of_dvd (show (0 : ℤ) < 1 by norm_num) h6 
    have h9 : (a - 2) ≥ -1 := by 
      have h10 : -(a - 2) ∣ 1 := by 
        exact Int.neg_dvd.2 h6 
      have h11 : -(a - 2) ≤ 1 := by 
        exact Int.le_of_dvd (show (0 : ℤ) < 1 by norm_num) h10 
      omega 
    interval_cases (a - 2) <;> tauto 
  rcases h7 with h7 | h7 
  · -- a - 2 = 1 
    have ha0 : a = 3 := by linarith 
    simp [ha0]
  · -- a - 2 = -1 
    have ha0 : a = 1 := by linarith 
    simp [ha0]