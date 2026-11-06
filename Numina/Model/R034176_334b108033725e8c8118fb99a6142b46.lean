import Mathlib

theorem algebra_157157 (a : ℝ) (h : ∃! x : ℝ, x^2 - a * abs x + a^2 - 3 = 0) :
    a = -Real.sqrt 3 := by
  rcases h with ⟨x, ⟨hx1, hx2⟩⟩
  have h1 : x ^ 2 - a * abs x + a ^ 2 - 3 = 0 := hx1
  have h2 : (-x) ^ 2 - a * abs (-x) + a ^ 2 - 3 = 0 := by
    have h3 : abs (-x) = abs x := by
      rw [abs_neg]
    have h4 : (-x) ^ 2 = x ^ 2 := by ring
    rw [h3, h4]
    linarith [h1]
  -- Therefore by uniqueness
  have h3 : -x = x := by 
    apply hx2 
    exact h2
  -- Solving x=0
  have hx0 : x = 0 := by linarith 
  have ha2_pos : a ^ 2 = 3 := by 
    rw [hx0] at h1 
    have h4 : abs ((0 : ℝ) : ℝ) = 0 := by simp 
    rw [h4] at h1 
    nlinarith 
  have ha2_cases : a = Real.sqrt 3 ∨ a = -Real.sqrt 3 := by
    have h2 : a^2 = (3 : ℝ) := ha2_pos 
    have h4 : a ^ 2 - (3 : ℝ) = (a - Real.sqrt 3) * (a + Real.sqrt 3) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h5 : a ^ 2 - (3 : ℝ) = 0 := by linarith 
    rw [h4] at h5 
    cases' (mul_eq_zero.mp h5) with h5 h6 
    · -- Case a - Real.sqrt 3 = 0 
      left 
      linarith 
    · -- Case a + Real.sqrt 3 = 0 
      right 
      linarith 
  cases ha2_cases with
  | inl ha_pos =>
    have ha_s : a = Real.sqrt 3 := ha_pos 
    -- Let's test the solution x = Real.sqrt 3 with a = sqrt(3)
    have h4 : (Real.sqrt 3) ^ 2 - a * abs (Real.sqrt 3) + a ^ 2 - 3 = 0 := by
      rw [ha_s]
      have hsqrt3_pos : Real.sqrt 3 > 0 := by positivity 
      have h11 : abs (Real.sqrt 3) = Real.sqrt 3 := by 
        rw [abs_of_pos hsqrt3_pos] 
      rw [h11] 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    -- However from hx2 uniqueness
    have h5 : (Real.sqrt 3) = x := by 
      apply hx2 
      exact h4 
    -- which leads to sqrt(3) = 0, a contradiction
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
  | inr ha_neg =>
    linarith