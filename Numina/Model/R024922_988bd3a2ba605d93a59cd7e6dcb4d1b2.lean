import Mathlib

open Real

theorem algebra_320310 {f g : ℝ → ℝ} (hf : f = fun x => (1 / 2) * logb 2 ((1 + x) / (1 - x))) (hg : g = fun x => (2 ^ x - 2 ^ (-x)) / (2 ^ x + 2 ^ (-x))) :
    ∀ x, f (g x) = x := by
  intro x
  rw [hf]
  rw [hg]
  have hx1 : ((2 : ℝ) ^ x + (2 : ℝ) ^ (-x)) ≠ 0 := by 
    have h11 : (2 : ℝ) ^ x > 0 := by positivity
    have h22 : (2 : ℝ) ^ (-x) > 0 := by positivity
    linarith
  have h4 : (1 + ((2 : ℝ) ^ x - (2 : ℝ) ^ (-x)) / ((2 : ℝ) ^ x + (2 : ℝ) ^ (-x))) / 
    (1 - ((2 : ℝ) ^ x - (2 : ℝ) ^ (-x)) / ((2 : ℝ) ^ x + (2 : ℝ) ^ (-x))) =
    (2 : ℝ) ^ x / (2 : ℝ) ^ (-x) := by
    field_simp [hx1]
    <;> ring_nf <;> field_simp [hx1] 
  have h9 : (2 : ℝ) ^ x / (2 : ℝ) ^ (-x) = (2 : ℝ) ^ (2 * x) := by
    have h12 : (2 : ℝ) ^ x / (2 : ℝ) ^ (-x) = (2 : ℝ) ^ (x - (-x) ) := by
      rw [← Real.rpow_sub]
      ring_nf
      all_goals linarith
    have h13 : x - (-x) = 2 * x := by
      ring_nf
    rw [h12, h13]
  have h3 : (1 + ((2: ℝ) ^ x - (2: ℝ) ^ (-x)) / ((2: ℝ) ^ x + (2: ℝ) ^ (-x))) / (1 - ((2: ℝ) ^ x - (2: ℝ) ^ (-x)) / ((2: ℝ) ^ x + (2: ℝ) ^ (-x))) = (2 : ℝ) ^ (2 * x) := by
    rw [h4]
    rw [h9]
  simp only [h3]
  have h40 : (1 / 2 : ℝ) * logb (2 : ℝ) ((2 : ℝ) ^ (2 * x)) = x := by
    have h41 : logb (2 : ℝ) ((2 : ℝ) ^ (2 * x)) = 2 * x := by
      rw [Real.logb_rpow]
      all_goals linarith
    rw [h41]
    all_goals linarith
  simpa using h40