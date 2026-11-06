import Mathlib

theorem algebra_9168 (f : ℝ → ℝ) (m : ℝ) (h₀ : ∀ x, f x = Real.sin (x + Real.pi / 2) + Real.cos (x - Real.pi / 2)+m) (hG: IsGreatest {f x | x:ℝ} (2*Real.sqrt 2)): m = Real.sqrt 2 := by
  have h1 : ∀ x, f x = Real.sin x + Real.cos x + m := by
    intro x
    calc
      f x = Real.sin (x + Real.pi / 2) + Real.cos (x - Real.pi / 2) + m := by 
        rw [h₀ x]
      _ = Real.cos x + Real.sin x + m := by 
        have h2 : Real.sin (x + Real.pi / 2) = Real.cos x := by 
          rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
          ring 
        have h3 : Real.cos (x - Real.pi / 2) = Real.sin x := by 
          rw [Real.cos_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
          ring 
        rw [h2, h3]
        all_goals ring 
      _ = Real.sin x + Real.cos x + m := by 
        ring 
  have h5 : ∃ x, f x = 2 * Real.sqrt 2 := by
    have h4 : 2 * Real.sqrt 2 ∈ {f x | x : ℝ} := by
      exact hG.left
    rcases h4 with ⟨x, hx⟩ 
    exact ⟨x, by linarith [hx]⟩
  rcases h5 with ⟨c, hc⟩ 
  have eq := hc 
  rw [h1 c] at eq 
  have h5 : ∀ x : ℝ, f x ≤ 2 * Real.sqrt 2 := by 
    have h4 : ∀ y ∈ {f x | x : ℝ}, y ≤ 2 * Real.sqrt 2 := by 
      apply hG.right 
    intro x
    have hx2 : f x ∈ {f x | x : ℝ} := by 
      simpa using x 
    have h6 := h4 (f x) hx2 
    linarith 
  have h6c : Real.sin c + Real.cos c ≤ Real.sqrt 2 := by
    have h7 : (Real.sin c) ^ 2 + (Real.cos c) ^ 2 = 1 := Real.sin_sq_add_cos_sq c 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sin c - Real.cos c)]
  have eq3 : Real.sin c + Real.cos c + m = 2 * Real.sqrt 2 := by 
    linarith [eq] 
  have eq6 : f (Real.pi / 4) ≤ 2 * Real.sqrt 2 := h5 (Real.pi / 4) 
  rw [h1 (Real.pi / 4)] at eq6 
  have eq7 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four 
  have eq8 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four 
  have eq9 : Real.sin (Real.pi / 4) + Real.cos (Real.pi / 4) = Real.sqrt 2 := by 
    nlinarith [eq7, eq8, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  have eq10 : m ≤ Real.sqrt 2 := by 
    nlinarith [eq6, eq9, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have eq5 : m ≥ Real.sqrt 2 := by 
    nlinarith [eq3, h6c, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  linarith [eq10, eq5, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]