import Mathlib

open Real

theorem algebra_98102 (x : ℝ) (m n : ℕ) (hx : x > 0) (hm: m > 0) (hn: n > 0) (hmn_cop: Nat.Coprime m n) (hxmn : x = (m:ℝ) / n)
(hl₁: logb 8 (2 * x) ≠ 0) (hl₂: logb 4 x ≠ 0) (hl₃: logb 2 x ≠ 0)
(h : ∃ r > 0, logb 8 (2 * x) * r = logb 4 x ∧ logb 4 x * r = logb 2 x) : m + n = 17 := by
  rcases h with ⟨r, hr_pos, hr₁, hr₂⟩
  have h1 : logb 8 (2 * x) = (1 + logb 2 x) / 3 := by
    have h2 : logb 8 (2 * x) = logb 2 (2 * x) / logb 2 (8:ℝ) := by 
      field_simp [logb]
    have h3 : logb 2 (8:ℝ) = 3 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h4 : logb 2 (2 * x) = 1 + logb 2 x := by 
      rw [logb_mul (by norm_num) (by linarith)]
      norm_num
    rw [h2, h3, h4]
  have h2 : logb 4 x = (logb 2 x) / 2 := by 
    have h3 : logb 4 x = logb 2 x / logb 2 (4:ℝ) := by 
      field_simp [logb]
    have h4 : logb 2 (4:ℝ) = 2 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h3, h4]
  rw [h1] at hr₁ 
  rw [h2] at hr₁ hr₂ 
  have h3 : r = 2 := by 
    have h4 : logb 2 x ≠ 0 := by 
      exact hl₃
    have eq1 : (logb 2 x / 2) * r = logb 2 x := by 
      linarith [hr₂]
    have eq2 : r = 2 := by 
      apply (mul_left_inj' (show logb 2 x / 2 ≠ 0 by 
        intro h'
        apply h4
        linarith 
      )).mp 
      linarith 
    linarith 
  have h4 : logb 2 x = -4 := by 
    rw [h3] at hr₁ 
    nlinarith [hr₁]
  -- Now from h4, x = 2^(-4), in Lean:
  have h5 : x = (1 : ℝ) / 16 := by 
    have h6 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by 
      field_simp [Real.rpow_logb, hx]
    rw [h6, h4]
    norm_num 
  rw [h5] at hxmn 
  have h6 : (m : ℝ) / n = (1 : ℝ) / 16 := by 
    linarith 
  -- Now converting h6 into a statement about natural numbers
  have h7 : m * 16 = n := by 
    have h8 : (m : ℝ) * 16 = n := by 
      have h9 : n ≠ 0 := by 
        exact Nat.not_eq_zero_of_lt hn
      field_simp at h6 ⊢ 
      nlinarith [h6]
    exact_mod_cast h8 
  -- Now using h7 and coprimality to solve
  have h8 : m = 1 := by 
    have h9 : m.gcd n = 1 := hmn_cop
    have h9' : m.gcd n = m := by 
      rw [show n = 16 * m by 
        omega
      ]
      simp [Nat.gcd_mul_right]
    rw [h9'] at h9 
    omega
  have h9 : n = 16 := by 
    nlinarith [h7, h8]
  calc 
    m + n = 1 + 16 := by 
      rw [h8, h9]
    _ = 17 := by 
      norm_num