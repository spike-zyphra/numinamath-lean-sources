import Mathlib

theorem algebra_148701 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + a * x + b)
    (h0 : f (f 0) = 0) (h1 : f (f 1) = 0) (h2 : f 0 ≠ f 1) : f 2 = 3 := by

  have h3 : f 0 = b := by
    rw [hf]
    all_goals norm_num

  have h4 : f 1 = 1 + a + b := by
    rw [hf]
    all_goals ring

  have eq1 : f (f 0) = (f 0) ^ 2 + a * (f 0) + b := by
    apply hf

  rw [eq1] at h0
  rw [show f 0 = b by linarith [h3] ] at h0

  have eq2 : b * (b + a + 1) = 0 := by
    nlinarith

  have eq3 : f (f 1) = (f 1) ^ 2 + a * (f 1) + b := by
    apply hf

  rw [eq3] at h1
  rw [show f 1 = 1 + a + b by linarith [h4] ] at h1

  have h5 : f 0 ≠ f 1 := h2
  have h6 : b ≠ 1 + a + b := by
    intro h
    have : f 0 = f 1 := by
      rw [h3, h4]
      linarith
    contradiction

  by_cases h7 : b = 0 
  · -- If b = 0, substitute into the second equation from h1
    have eq4 : 1 + 3 * a + 2 * a ^ 2 = 0 := by
      rw [h7] at h1
      nlinarith 
    have eq5 : (a + 1) * (2 * a + 1) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp eq5) with h8 h9
    · -- h8 : a + 1 = 0 
      have ha : a = -1 := by linarith
      have h8' : f 0 = f 1 := by 
        rw [h3, h4]
        rw [h7, ha]
        all_goals norm_num 
      contradiction
    · -- h9
      have ha : a = -1 / 2 := by linarith
      have hb : b = (0 : ℝ) := by linarith
      have h8' : f 2 = 3 := by
        rw [hf]
        rw [ha, hb]
        norm_num 
      linarith 
  · -- Case b ≠ 0
    have eq6 : b + a + 1 = 0 := by 
      apply (mul_left_inj' (show b ≠ 0 by 
        intro h
        apply h7
        linarith 
      )).mp 
      linarith
    have eq7 : b = -a - 1 := by linarith 
    rw [eq7] at h1 
    nlinarith [sq_pos_of_ne_zero (show (f 0 - f 1) ≠ 0 by
      intro h
      apply h2
      have : f 0 = f 1 := by
        nlinarith 
      assumption
    ), sq_nonneg (f 0 - f 1)]