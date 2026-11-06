import Mathlib

theorem algebra_305218 (a : ℝ) (ha : a > 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = x ^ 2 + a * abs x + a ^ 2 - 3) :
    (∃! x, f x = 0) ↔ a = Real.sqrt 3 := by 
  constructor
  · -- Assume there exists a unique x such that f x = 0, then a = sqrt 3
    intro h 
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have h1 : f x = 0 := hx1 
    have h2 : ∀ y, f y = 0 → y = x := hx2 
    have h3 : x = 0 := by 
      have h4 : f (-x) = 0 := by 
        have eq1 : f (-x) = (-x) ^ 2 + a * abs (-x) + a ^ 2 - 3 := by 
          rw [hf]
        have eq2 : f x = x ^ 2 + a * abs x + a ^ 2 - 3 := by 
          rw [hf]
        have h5 : abs (-x) = abs x := by 
          rw [abs_neg]
        rw [eq1]
        rw [h5]
        linarith [h1, eq2]
      have h5 : -x = x := by 
        apply h2 (-x) 
        exact h4 
      linarith 
    have h4 : f x = 0 := hx1 
    rw [show x = (0 : ℝ) by linarith] at h4 
    have eq0 : f 0 = 0 ^ 2 + a * abs (0 : ℝ) + a ^ 2 - 3 := by 
      rw [hf]
    rw [eq0] at h4 
    have h5 : a ^ 2 = 3 := by 
      norm_num [abs_zero] at h4 
      nlinarith 
    have h6 : a = Real.sqrt 3 := by 
      have h7 : a > 0 := ha 
      have h8 : Real.sqrt 3 > 0 := by 
        apply Real.sqrt_pos.mpr 
        all_goals linarith 
      have h9 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by linarith) 
      have h10 : a ^ 2 = (Real.sqrt 3) ^ 2 := by 
        rw [h5, h9] 
      have h11 : a = Real.sqrt 3 := by 
        nlinarith [Real.sqrt_nonneg 3] 
      linarith 
    linarith 
  · -- Assume a = sqrt 3, then prove there exists unique x such that f x = 0 
    intro h_eq 
    have ha_eq : a = Real.sqrt 3 := by linarith [h_eq] 
    refine ⟨0, ?_, ?_⟩ 
    · -- Show that 0 is indeed a solution 
      have h0 : f 0 = 0 := by 
        rw [hf]
        rw [show a = Real.sqrt 3 by linarith [h_eq]]
        norm_num [abs_zero, Real.sqrt_pos.mpr] 
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      simpa using h0 
    · -- Show that it's unique 
      intro y hy 
      have hy0 : f y = 0 := by 
        simpa using hy 
      rw [hf] at hy0 
      simp only [ha_eq] at hy0 
      have h1 : y ^ 2 + Real.sqrt 3 * abs y + (Real.sqrt 3) ^ 2 - 3 = 0 := by 
        nlinarith 
      have h2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num) 
      have h3 : y ^ 2 + Real.sqrt 3 * abs y = 0 := by 
        nlinarith [h1, h2] 
      have h5 : abs y = 0 := by 
        cases' abs_cases y with hy1 hy1 
        · -- Case y ≥ 0 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        · -- Case y < 0 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h5' : y = 0 := by 
        rw [abs_eq_zero] at h5 
        linarith 
      linarith