import Mathlib

theorem algebra_244392 (x : ℕ → ℝ) (hx1 : x 1 = 123456789) (hxn : ∀ n ≥ 1, x (n + 1) = (n + 1) / x n) :
    x 1 * x 2 * x 18 * x 19 * x 52 * x 53 = 2014 := by

  have h1 : ∀ n ≥ 1, x n * x (n + 1) = n + 1 := by 
    intro n hn
    have h2 : n ≥ 1 := hn 
    have eq1 : x (n + 1) = (n + 1 : ℝ) / x n := hxn n (by linarith)
    have eq2 : x n ≠ 0 := by
      have h11 : x 1 = (123456789 : ℝ) := hx1
      have h12 : ∀ (n : ℕ), n ≥ 1 → x n ≠ 0 := by 
        intro n hn 
        induction n with 
        | zero => 
          exfalso
          linarith 
        | succ n ih => 
          cases n with 
          | zero => 
            rw [h11]
            norm_num 
          | succ n => 
            have h15 : x (n + 1 + 1) = (↑(n + 1) + 1 : ℝ) / x (n + 1) := by 
              have h15' : x (n + 1 + 1) = (↑(n + 1) + 1 : ℝ) / x (n + 1) := hxn (n + 1) (by linarith)
              simpa using h15'
            have eq4 : x (n + 1) ≠ 0 := ih (by linarith)
            rw [h15]
            intro h 
            have h5 : (↑(n + 1) + 1 : ℝ) / x (n + 1) = 0 := by simpa using h
            have h6 : (↑(n + 1) + 1 : ℝ) = 0 := by 
              have h7 : x (n + 1) ≠ 0 := eq4
              field_simp at h5 ⊢
              all_goals linarith 
            have h7 : (↑(n + 1) + 1 : ℝ) > 0 := by
              have h100 : (n : ℝ) ≥ (0 : ℝ) := by exact_mod_cast (show n ≥ (0 : ℕ) by omega)
              nlinarith
            linarith 
      exact h12 n (by linarith)
    rw [eq1]
    have h9 : x n ≠ 0 := eq2
    field_simp [h9]
    all_goals norm_num
    all_goals linarith
  have h2 : x 1 * x 2 = 2 := by 
    have h11 := h1 1 (by norm_num)
    norm_num at h11 ⊢
    all_goals linarith
  have h3 : x 18 * x 19 = 19 := by 
    have h118 := h1 18 (by norm_num)
    norm_num at h118 ⊢
    all_goals linarith 
  have h4 : x 52 * x 53 = 53 := by
    have h152 := h1 52 (by norm_num)
    norm_num at h152 ⊢ 
    all_goals linarith 
  calc 
    x 1 * x 2 * x 18 * x 19 * x 52 * x 53 
        = (x 1 * x 2) * (x 18 * x 19) * (x 52 * x 53) := by ring
    _ = 2 * 19 * 53 := by rw [h2, h3, h4]
    _ = 2014 := by norm_num