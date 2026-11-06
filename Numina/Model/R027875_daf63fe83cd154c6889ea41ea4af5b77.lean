import Mathlib

theorem algebra_302885 {n : ℕ} (hn : n ≤ 5000)
    (h1 : (1 / 3 : ℚ) * n * (1 / 40 : ℚ) + (2 / 7 : ℚ) * n * (1 / 16 : ℚ) +
      (1 / 5 : ℚ) * n * (1 / 9 : ℚ) + (3 / 5 : ℚ) * n * (1 / 3 : ℚ) = 183) :
    n = 5000 := by
  have h2 : (n : ℚ) ≤ 5000 := by exact_mod_cast hn
  have eq1 : (313 / 1260 : ℚ) * (n : ℚ) = 183 := by 
    ring_nf at h1 ⊢
    linarith
  have h3 : (n : ℚ) = 736 + (212 / 313 : ℚ) := by 
    linarith
  have h4 : (n : ℚ) * (313 : ℚ) = 230580 := by
    have h5 : (n : ℚ) = 736 + (212 / 313 : ℚ) := h3
    rw [h5]
    norm_num
    all_goals linarith
  have h5 : (n : ℤ) * 313 = 230580 := by 
    exact_mod_cast (show (n : ℚ) * (313 : ℚ) = (230580 : ℚ) by
      linarith [h4]
    )
  omega