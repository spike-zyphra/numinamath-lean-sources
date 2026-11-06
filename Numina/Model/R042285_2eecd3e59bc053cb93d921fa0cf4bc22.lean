import Mathlib

theorem algebra_145796 {f : ℕ → ℕ → ℕ}
    (h1 : ∀ x, x > 0 → f x x = x)
    (h2 : ∀ x y, x > 0 → y > 0 → f x y = f y x)
    (h3 : ∀ x y, x > 0 → y > 0 → (x + y) * f x y = y * f x (x + y)) :
    f 14 52 = 364 := by

  -- Compute f 2 4
  have h4 : f 2 4 = 4 := by
    have h5 : f 2 2 = 2 := h1 2 (show (2 : ℕ) > 0 by norm_num)
    have eq1 := h3 2 2 (by norm_num) (by norm_num)
    norm_num [h5] at eq1 
    omega

  -- Compute f 4 2
  have h5 : f 4 2 = 4 := by 
    have h6 : f 4 2 = f 2 4 := h2 4 2 (by norm_num) (by norm_num)
    rw [h6, h4]

  -- Compute f 4 6
  have h6 : f 4 6 = 12 := by
    have eq1 := h3 4 2 (by norm_num) (by norm_num)
    have eq2 : (4 + 2) * f 4 2 = 2 * f 4 6 := by
      simpa using eq1
    norm_num [h5] at eq2 
    omega

  -- Compute f 4 10
  have h7 : f 4 10 = 20 := by
    have eq1 := h3 4 6 (by norm_num) (by norm_num)
    have eq2 : (4 + 6) * f 4 6 = 6 * f 4 10 := by
      simpa using eq1
    norm_num [h6] at eq2 
    omega

  -- Compute f 10 4
  have h8 : f 10 4 = 20 := by
    have h9 : f 10 4 = f 4 10 := h2 10 4 (by norm_num) (by norm_num)
    rw [h9, h7]

  -- Compute f 14 10
  have h9 : f 14 10 = 70 := by
    have eq1 := h3 10 4 (by norm_num) (by norm_num)
    have eq2 : (10 + 4) * f 10 4 = 4 * f 10 14 := by
      simpa using eq1
    have eq3 : f 14 10 = 70 := by
      have eq4 : f 14 10 = f 10 14 := by 
        apply h2 14 10 
        all_goals norm_num
      have eq5 : f 10 14 = 70 := by
        omega
      omega
    exact eq3

  -- Compute f 14 24
  have h10 : f 14 24 = 168 := by
    have eq1 := h3 14 10 (by norm_num) (by norm_num)
    have eq2 : (14 + 10) * f 14 10 = 10 * f 14 24 := by
      simpa using eq1
    norm_num [h9] at eq2 
    omega

  -- Compute f 14 38
  have h11 : f 14 38 = 266 := by
    have eq1 := h3 14 24 (by norm_num) (by norm_num)
    have eq2 : (14 + 24) * f 14 24 = 24 * f 14 38 := by
      simpa using eq1
    norm_num [h10] at eq2 
    omega

  -- Compute f 14 52
  have h12 : f 14 52 = 364 := by
    have eq1 := h3 14 38 (by norm_num) (by norm_num)
    have eq2 : (14 + 38) * f 14 38 = 38 * f 14 52 := by
      simpa using eq1
    norm_num [h11] at eq2 
    omega
  exact h12