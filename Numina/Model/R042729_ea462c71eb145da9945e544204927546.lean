import Mathlib

open Real

theorem algebra_147975 {x : ℤ} (hx : x^2 + 7 > 0) (hx1 : x + 1 > 0) (hx2 : x > 0)
    (h : logb 2 (x^2 + 7) = logb 2 (x + 1) / logb 8 2 - logb 2 x) :
    x = 1 := by
  have h1 : (x : ℝ) > (0 : ℝ) := by exact_mod_cast hx2
  have h2 : (x + 1 : ℝ) > (0 : ℝ) := by exact_mod_cast hx1
  have h3 : (x^2 + 7 : ℝ) > (0 : ℝ) := by exact_mod_cast hx
  have h4 : logb 8 2 = 1 / 3 := by
    have h5 : logb 8 2 = log (2 : ℝ) / log (8 : ℝ) := by
      field_simp [logb]
    have h6 : log (8 : ℝ) = 3 * log (2 : ℝ) := by 
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
      simp [log_pow]
    have hd : log (2 : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply log_pos
      norm_num
    rw [h6] at h5
    rw [h5]
    field_simp [hd]
    <;> nlinarith
  have h5' : logb 2 (x + 1) / logb 8 2 = 3 * logb 2 (x + 1) := by 
    rw [h4]
    field_simp
    <;> nlinarith
  rw [h5'] at h 
  have h6 : 3 * logb (2 : ℝ) (x + 1) = logb (2 : ℝ) ((x + 1 : ℝ) ^ 3) := by 
    have h7 : logb (2 : ℝ) ((x + 1 : ℝ) ^ 3) = 3 * logb (2 : ℝ) (x + 1) := by 
      simp [logb_pow]
    linarith [h7]
  rw [h6] at h 
  -- We have $\log_2(x^2+7)=\log_2((x+1)^3)-\log_2(x) = \log_2\left( \frac{(x+1)^3}{x} \right)$
  have h7 : logb (2 : ℝ) (x^2 + 7) = logb (2 : ℝ) ((x + 1 : ℝ) ^ 3 / (x : ℝ)) := by
    have h8 : logb (2 : ℝ) ((x + 1 : ℝ) ^ 3 / (x : ℝ)) = logb (2 : ℝ) ((x + 1 : ℝ) ^ 3) - logb (2 : ℝ) (x : ℝ) := by 
      rw [logb_div (by positivity) (by positivity)]
    linarith [h8, h]
  -- Now that they are equal, set the arguments equal
  have h8' : (x^2 + 7 : ℝ) = ((x + 1 : ℝ) ^ 3 / (x : ℝ)) := by 
    have h10 : (x^2 + 7 : ℝ) > 0 := h3
    have h11 : ((x + 1 : ℝ) ^ 3 / (x : ℝ)) > 0 := by positivity
    have h9 : logb (2 : ℝ) (x^2 + 7) = logb (2 : ℝ) ((x + 1 : ℝ) ^ 3 / (x : ℝ)) := h7
    have h13 : (x^2 + 7 : ℝ) = ((x + 1 : ℝ) ^ 3 / (x : ℝ)) := by
      apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h10) (Set.mem_Ioi.mpr h11) h9
    exact h13 
  have h9 : (x : ℝ) * ((x ^ 2 + 7 : ℝ)) = ((x + 1 : ℝ) ^ 3) := by
    have h10 : (x^2 + 7 : ℝ) = ((x + 1 : ℝ) ^ 3 / (x : ℝ)) := h8'
    have h11 : (x : ℝ) > (0 : ℝ) := by exact_mod_cast hx2
    have h12 : (x : ℝ) * (x^2 + 7 : ℝ) = (x + 1 : ℝ) ^ 3 := by 
      have h13 : (x^2 + 7 : ℝ) = ((x + 1 : ℝ) ^ 3 / (x : ℝ)) := h10
      have h14 : (x : ℝ) * (x^2 + 7 : ℝ) = (x : ℝ) * ((x + 1 : ℝ) ^ 3 / (x : ℝ)) := by 
        rw [h13]
      have h15 : (x : ℝ) * ((x + 1 : ℝ) ^ 3 / (x : ℝ)) = (x + 1 : ℝ) ^ 3 := by 
        field_simp
        <;> nlinarith 
      linarith [h14, h15]
    linarith [h12]
  have h10 : x * (x ^ 2 + 7) = (x + 1) ^ 3 := by
    have h11 : (x : ℝ) * ((x ^ 2 + 7 : ℝ)) = ((x + 1 : ℝ) ^ 3) := h9
    norm_cast at h11 ⊢
  -- Now solve quadratic.
  have h11 : 3 * x^2 - 4 * x + 1 = 0 := by
    nlinarith [h10]
  have h13 : x = 1 := by
    have h14 : 3 * x^2 - 4 * x + 1 = 0 := h11
    have h15 : x ≤ 1 := by
      nlinarith [sq_nonneg (3 * x - 1), sq_nonneg (x - 1)]
    have h16 : x ≥ 1 := by
      nlinarith [sq_nonneg (3 * x - 1), sq_nonneg (x - 1)]
    nlinarith 
  exact h13