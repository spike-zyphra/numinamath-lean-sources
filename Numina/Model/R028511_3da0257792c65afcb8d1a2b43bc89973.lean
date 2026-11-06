import Mathlib

theorem algebra_187890 {f : ℝ → ℝ} (hf1 : f 1 = 1)
    (hfx : ∀ x ≠ 0, f (1 / x) = (1 / x ^ 2) * f x)
    (hfadd : ∀ x y, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → f (x + y) = f x + f y) :
    f (5 / 7) = 5 / 7 := by
  have eq1 : f (5 / 7 : ℝ) + f (2 / 7 : ℝ) = 1 := by 
    have h1 : f 1 = f (5 / 7 : ℝ) + f (2 / 7 : ℝ) := by 
      rw [← hfadd (5 / 7) (2 / 7) (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    linarith [hf1, h1]
  have eq2 : f (2 / 7 : ℝ) = 2 * f (1 / 7 : ℝ) := by 
    have h2 : f (2 / 7 : ℝ) = f (1 / 7 : ℝ) + f (1 / 7 : ℝ) := by 
      have h3 : f (1 / 7 + 1 / 7) = f (1 / 7) + f (1 / 7) := hfadd (1 / 7) (1 / 7) (by norm_num) (by norm_num) (by norm_num)
      rw [show (1 / 7 : ℝ) + (1 / 7 : ℝ) = (2 / 7 : ℝ) by norm_num] at h3
      linarith 
    linarith 
  have eq3 : f (7 / 2 : ℝ) = (49 / 4) * f (2 / 7 : ℝ) := by
    have h4 := hfx (2 / 7 : ℝ) (by norm_num)
    have h5 : (1 / (2 / 7 : ℝ)) = (7 / 2 : ℝ) := by 
      field_simp 
    rw [h5] at h4 
    have h6 : (1 / (2 / 7 : ℝ) ^ 2) = (49 / 4 : ℝ) := by 
      field_simp 
      <;> norm_num 
    rw [h6] at h4 
    linarith 
  have eq4 : f (7 / 2 : ℝ) = f (5 / 2 : ℝ) + f 1 := by 
    rw [← hfadd (5 / 2) 1 (by norm_num) (by norm_num) (by norm_num)]
    norm_num 
  have eq5 : f (5 / 2 : ℝ) = f (2 : ℝ) + f (1 / 2 : ℝ) := by 
    rw [← hfadd (2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num) (by norm_num)]
    norm_num 
  have eq6 : f (1 / 2 : ℝ) = (1 / 4) * f (2 : ℝ) := by 
    have h7 := hfx (2 : ℝ) (by norm_num)
    norm_num at h7 ⊢ 
    linarith 
  have eq7 : f (2 : ℝ) = 4 * f (1 / 2 : ℝ) := by 
    have h8 := hfx (1 / 2 : ℝ) (by norm_num)
    have h9 : (1 / (1 / 2 : ℝ)) = (2 : ℝ) := by 
      field_simp 
    rw [h9] at h8 
    have h10 : (1 / (1 / 2 : ℝ) ^ 2) = (4 : ℝ) := by 
      field_simp 
      <;> norm_num 
    rw [h10] at h8 
    nlinarith 
  have eq8 : f (7 : ℝ) = f (5 : ℝ) + f (2 : ℝ) := by 
    rw [← hfadd (5 : ℝ) (2 : ℝ) (by norm_num) (by norm_num) (by norm_num)]
    norm_num 
  have eq9 : f (1 / 7 : ℝ) = (1 / 49) * f (7 : ℝ) := by 
    have h10 := hfx (7 : ℝ) (by norm_num) 
    have h11 : (1 / (7 : ℝ)) = (1 / 7 : ℝ) := by norm_num 
    rw [h11] at h10 
    have h12 : (1 / (7 : ℝ) ^ 2) = (1 / 49 : ℝ) := by 
      norm_num 
    rw [h12] at h10 
    linarith 
  have eq10 : f (5 : ℝ) = f (3 : ℝ) + f (2 : ℝ) := by 
    rw [← hfadd (3 : ℝ) (2 : ℝ) (by norm_num) (by norm_num) (by norm_num)]
    norm_num 
  have eq11 : f (3 : ℝ) = f (1 : ℝ) + f (2 : ℝ) := by 
    rw [← hfadd (1 : ℝ) (2 : ℝ) (by norm_num) (by norm_num) (by norm_num)]
    norm_num 
  have h2 : f (2 : ℝ) = 2 := by
    have eq12 : f (1 / 2 : ℝ) = (1 / 4) * f (2 : ℝ) := eq6 
    have eq13 : f (2 : ℝ) = 4 * f (1 / 2 : ℝ) := eq7 
    have h14 : f (2 : ℝ) = 2 := by 
      nlinarith [hf1, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11]
    linarith 
  have h31 : f (1 / 7 : ℝ) = 1 / 7 := by
    have eqf7 : f (7 : ℝ) = 7 := by
      nlinarith [hf1, eq8, eq10, eq11, h2]
    rw [eqf7] at eq9
    linarith 
  have h4 : f (2 / 7 : ℝ) = 2 / 7 := by 
    rw [h31] at eq2 
    linarith 
  have h5 : f (5 / 7 : ℝ) = 5 / 7 := by
    nlinarith [eq1, h4]
  linarith [h5]