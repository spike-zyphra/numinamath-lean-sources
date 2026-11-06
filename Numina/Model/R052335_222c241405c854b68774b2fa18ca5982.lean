import Mathlib

theorem algebra_281570 (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc (-1) 1, 0 ≤ f x ∧ f x ≤ 1)
    (h : f = fun x => a * x - b) :
    -4 / 5 ≤ (3 * a + b + 1) / (a + 2 * b - 2) ∧
    (3 * a + b + 1) / (a + 2 * b - 2) ≤ 2 / 7 := by 
  have h1 := hf (-1) (Set.left_mem_Icc.mpr (by norm_num))
  have h2 := hf 1 (Set.right_mem_Icc.mpr (by norm_num))
  have h3 := hf 0 (by norm_num [Set.mem_Icc])
  simp [h] at h1 h2 h3 
  have h4 : a + b ≤ 0 := by linarith
  have h5 : a + b ≥ -1 := by linarith
  have h6 : b ≤ 0 := by linarith
  have h7 : b ≥ -1 := by linarith
  have h8 : a - b ≥ 0 := by linarith
  have h9 : a - b ≤ 1 := by linarith 
  have h10 : a + 2 * b - 2 < 0 := by nlinarith 
  have h11 : -19 * a - 13 * b + 3 ≥ 0 := by 
    nlinarith
  have h12 : 19 * a + 3 * b + 11 ≥ 0 := by 
    nlinarith 
  constructor 
  · -- Proving that (3a + b +1)/(a + 2b - 2) ≥ -4/5 
    apply (le_div_iff_of_neg' h10).mpr 
    nlinarith
  · -- Proving that (3a + b +1)/(a + 2b - 2) ≤ 2/7
    apply (div_le_iff_of_neg' h10).mpr 
    nlinarith