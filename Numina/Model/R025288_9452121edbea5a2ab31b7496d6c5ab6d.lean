import Mathlib

open Real

theorem algebra_111551 {f : ℝ → ℝ}
    (hf : ∀ x, f x = 1 / (1 + 2 ^ (logb 10 x)) + 1 / (1 + 4 ^ (logb 10 x)) +
      1 / (1 + 8 ^ (logb 10 x))) :
    ∀ x, x ≠ 0 → f x + f (1 / x) = 3 := by
  intro x hx
  have hfx : f x = 1 / (1 + 2 ^ (logb 10 x)) + 1 / (1 + 4 ^ (logb 10 x)) +
      1 / (1 + 8 ^ (logb 10 x)) := by
    apply hf
  have hf1x : f (1 / x) = 1 / (1 + 2 ^ (logb 10 (1 / x))) + 1 / (1 + 4 ^ (logb 10 (1 / x))) +
      1 / (1 + 8 ^ (logb 10 (1 / x))) := by 
    apply hf
  have h1 : logb 10 (1 / x) = - logb 10 x := by 
    simp [logb_div, logb_one]
  rw [hfx, hf1x, h1]
  -- Now, we need to rewrite each term of f(1/x) using the relation: logb 10 (1/x) = - logb 10 x
  -- Therefore, 2^(-logb 10 x) = 1/(2^(logb 10 x)), similarly for 4 and 8.
  have h2 : (2 : ℝ) ^ (-logb 10 x) = 1 / ((2 : ℝ) ^ (logb 10 x)) := by 
    rw [show (-logb 10 x : ℝ) = - (logb 10 x : ℝ) by ring]
    rw [Real.rpow_neg]
    <;> norm_num
  have h4 : (4 : ℝ) ^ (-logb 10 x) = 1 / ((4 : ℝ) ^ (logb 10 x)) := by 
    rw [show (-logb 10 x : ℝ) = - (logb 10 x : ℝ) by ring]
    rw [Real.rpow_neg]
    <;> norm_num
  have h8 : (8 : ℝ) ^ (-logb 10 x) = 1 / ((8 : ℝ) ^ (logb 10 x)) := by 
    rw [show (-logb 10 x : ℝ) = - (logb 10 x : ℝ) by ring]
    rw [Real.rpow_neg]
    <;> norm_num
  simp only [h2, h4, h8] at *
  -- Now, for each pair of terms (original and transformed), their sum should be 1.
  -- This is proven in the next lemmas.
  have h3 : 1 / (1 + (2 : ℝ) ^ (logb 10 x)) + 1 / (1 + 1 / ((2 : ℝ) ^ (logb 10 x))) = 1 := by
    field_simp
    <;> ring
  have h4' : 1 / (1 + (4 : ℝ) ^ (logb 10 x)) + 1 / (1 + 1 / ((4 : ℝ) ^ (logb 10 x))) = 1 := by
    field_simp
    <;> ring
  have h8' : 1 / (1 + (8 : ℝ) ^ (logb 10 x)) + 1 / (1 + 1 / ((8 : ℝ) ^ (logb 10 x))) = 1 := by
    field_simp
    <;> ring
  -- The total sum is 3 * 1 = 3
  linarith [h3, h4', h8']