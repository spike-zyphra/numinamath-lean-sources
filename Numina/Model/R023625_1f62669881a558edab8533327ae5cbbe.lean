import Mathlib

theorem algebra_100888 (n : ℕ) (hn : n > 0) (x y : ℝ)
    (hx : x = (1 + 1 / n : ℝ)^n) (hy : y = (1 + 1 / n : ℝ)^(n + 1)) :
    x^y = y^x := by
  rw [hx] at *
  rw [hy] at *
  have eq1 : ((1 + 1 / (n : ℝ)) ^ n) ^ ((1 + 1 / (n : ℝ)) ^ (n + 1)) =
      (1 + 1 / (n : ℝ)) ^ (n * ((1 + 1 / (n : ℝ)) ^ (n + 1)) ) := by
    have h_nonneg : 0 ≤ (1 + 1 / (n : ℝ)) := by
      have h1 : (n : ℝ) > 0 := by exact_mod_cast (show (n : ℕ) > 0 by exact hn)
      have h2 : 1 / (n : ℝ) > 0 := by
        apply div_pos
        norm_num
        exact_mod_cast (show (n : ℕ) > 0 by exact hn)
      have h3 : (1 + 1 / (n : ℝ)) > 0 := by
        linarith
      linarith
    have h4 : ((1 + 1 / (n : ℝ)) ^ n) ^ ((1 + 1 / (n : ℝ)) ^ (n + 1)) =
        (1 + 1 / (n : ℝ)) ^ (↑n * ((1 + 1 / (n : ℝ)) ^ (n + 1 : ℕ)) ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul h_nonneg]
      all_goals norm_cast
      all_goals norm_num
      all_goals positivity
      all_goals linarith
    norm_cast at h4 ⊢
    all_goals linarith
    all_goals norm_cast
    all_goals norm_num
    all_goals linarith
    all_goals positivity
  have eq2 : ((1 + 1 / (n : ℝ)) ^ (n + 1)) ^ ((1 + 1 / (n : ℝ)) ^ n) =
      (1 + 1 / (n : ℝ)) ^ ((↑(n + 1)) * ((1 + 1 / (n : ℝ)) ^ n) ) := by
    have h_nonneg : 0 ≤ (1 + 1 / (n : ℝ)) := by
      have h1 : (n : ℝ) > 0 := by exact_mod_cast (show (n : ℕ) > 0 by exact hn)
      have h2 : 1 / (n : ℝ) > 0 := by
        apply div_pos
        norm_num
        exact_mod_cast (show (n : ℕ) > 0 by exact hn)
      have h3 : (1 + 1 / (n : ℝ)) > 0 := by
        linarith
      linarith
    have h5 : ((1 + 1 / (n : ℝ)) ^ (n + 1)) ^ ((1 + 1 / (n : ℝ)) ^ n) =
        (1 + 1 / (n : ℝ)) ^ (↑(n + 1) * ((1 + 1 / (n : ℝ)) ^ n) ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul h_nonneg]
      all_goals norm_cast
      all_goals norm_num
      all_goals positivity
      all_goals linarith
    norm_cast at h5 ⊢
    all_goals linarith
    all_goals norm_cast
    all_goals norm_num
    all_goals linarith
    all_goals positivity
  have h_eq : (n : ℝ) * ((1 + 1 / (n : ℝ)) ^ (n + 1)) = (↑(n + 1 : ℕ) : ℝ) * ((1 + 1 / (n : ℝ)) ^ n) := by
    have h6 : (1 + 1 / (n : ℝ)) ^ (n + 1 : ℕ) = (1 + 1 / (n : ℝ)) ^ n * (1 + 1 / (n : ℝ)) := by
      ring_nf
    rw [h6]
    have h7 : (n : ℝ) * ((1 + 1 / (n : ℝ)) ^ n * (1 + 1 / (n : ℝ))) = ((↑(n + 1 : ℕ) : ℝ) ) * ((1 + 1 / (n : ℝ)) ^ n) := by
      have h8 : (n : ℝ) * (1 + 1 / (n : ℝ)) = (↑(n + 1 : ℕ) : ℝ) := by
        have h1 : (n : ℝ) > 0 := by exact_mod_cast (show (n : ℕ) > 0 by exact hn)
        field_simp at *
        <;> ring_nf <;> norm_num
        <;> linarith
      have h9 : (↑(n + 1 : ℕ) : ℝ) = (↑(n + 1 : ℕ) : ℝ) := by rfl
      calc
        (n : ℝ) * ((1 + 1 / (n : ℝ)) ^ n * (1 + 1 / (n : ℝ)))
          = ((n : ℝ) * (1 + 1 / (n : ℝ))) * ((1 + 1 / (n : ℝ)) ^ n) := by ring
        _ = ((↑(n + 1 : ℕ) : ℝ) ) * ((1 + 1 / (n : ℝ)) ^ n) := by rw [h8]
    norm_cast at h7 ⊢
    all_goals norm_cast at *
    all_goals linarith
    all_goals norm_cast
    all_goals norm_num
    all_goals linarith
  rw [eq1, eq2]
  rw [h_eq]
  all_goals norm_num
  all_goals positivity
  all_goals norm_num
  all_goals linarith