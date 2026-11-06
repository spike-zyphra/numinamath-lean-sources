import Mathlib

theorem algebra_320488 (a b c : ℤ) (h : ∀ x : ℝ, (x - a) * (x - 8) + 1 = (x - b) * (x - c)) :
    a + b + c = 20 ∨ a + b + c = 28 := by
  have eq1 := h 8 
  norm_num at eq1 
  have eq2 : (8 - (b : ℝ)) * (8 - (c : ℝ)) = 1 := by 
    nlinarith 
  have eq3 : ((8 - b : ℤ)) * ((8 - c : ℤ)) = 1 := by 
    have eq4 : (8 - (b : ℝ)) * (8 - (c : ℝ)) = 1 := by 
      nlinarith 
    exact_mod_cast eq4 
  have h1 : (8 - b) * (8 - c) = 1 := by
    exact_mod_cast eq3 
  have h2 : (8 - b = 1 ∨ 8 - b = -1) := by 
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h1 
  cases h2 with 
  | inl h2b =>
    have h3c : 8 - c = 1 := by 
      rw [h2b] at h1 
      linarith 
    -- From 8 - b = 1, we have b = 7
    -- From 8 - c = 1, we have c = 7 
    have eq5 : (b : ℤ) = 7 := by linarith 
    have eq6 : (c : ℤ) = 7 := by linarith 
    -- We use h with x = 0 
    have eq7 := h 0 
    norm_num at eq7 
    rw [show (b : ℝ) = 7 by exact_mod_cast eq5, show (c : ℝ) = 7 by exact_mod_cast eq6] at eq7 
    ring_nf at eq7 ⊢ 
    have eq8 : (a : ℝ) = 6 := by linarith 
    have eq9 : a = 6 := by 
      exact_mod_cast eq8 
    -- Check: a = 6, b = 7, c = 7 
    -- Then a + b + c = 6 + 7 + 7 = 20 
    left 
    omega 
  | inr h2b =>
    have h3c : 8 - c = -1 := by 
      rw [h2b] at h1 
      linarith 
    -- From 8 - b = -1, we have b = 9
    -- From 8 - c = -1, we have c = 9 
    have eq5 : (b : ℤ) = 9 := by linarith 
    have eq6 : (c : ℤ) = 9 := by linarith 
    -- We use h with x = 0 
    have eq7 := h 0 
    norm_num at eq7 
    rw [show (b : ℝ) = 9 by exact_mod_cast eq5, show (c : ℝ) = 9 by exact_mod_cast eq6] at eq7 
    ring_nf at eq7 ⊢ 
    have eq8 : (a : ℝ) = 10 := by linarith 
    have eq9 : a = 10 := by 
      exact_mod_cast eq8 
    -- Check: a = 10, b = 9, c = 9 
    -- Then a + b + c = 10 + 9 + 9 = 28 
    right 
    omega