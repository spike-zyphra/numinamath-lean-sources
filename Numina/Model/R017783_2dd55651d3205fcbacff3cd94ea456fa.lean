import Mathlib

open Real

theorem algebra_282440 (f : ℝ → ℝ) (hf : f = fun x => 2 * sqrt (x - 1) + sqrt (6 - 2 * x)) :
    IsGreatest (Set.image f {x | 1 ≤ x ∧ x ≤ 3}) (f (7 / 3)) := by
  have h1 : ∀ x, f x = 2 * sqrt (x - 1) + sqrt (6 - 2 * x) := by
    intro x
    rw [hf]
  have h2 : 7 / 3 ∈ {x | 1 ≤ x ∧ x ≤ 3} := by
    constructor
    · norm_num
    · norm_num
  have h3 : f (7 / 3) = 2 * sqrt (7 / 3 - 1) + sqrt (6 - 2 * (7 / 3)) := by
    rw [h1]
  have h4 : f (7 / 3) = 2 * Real.sqrt (4 / 3) + Real.sqrt (4 / 3) := by
    rw [h3]
    have h5 : (7 / 3 : ℝ) - 1 = 4 / 3 := by norm_num
    have h6 : (6 - 2 * (7 / 3 : ℝ)) = 4 / 3 := by norm_num
    rw [h5, h6]
  have h5 : (2 * Real.sqrt (4 / 3) + Real.sqrt (4 / 3)) = 2 * Real.sqrt 3 := by
    have h6 : Real.sqrt (4 / 3) = (2 / Real.sqrt 3) := by
      have h7 : Real.sqrt (4 / 3) = Real.sqrt (4 : ℝ) / Real.sqrt (3 : ℝ) := by 
        rw [Real.sqrt_div (by norm_num)]
      have h8 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_cases]
        all_goals norm_num
      rw [h7, h8]
    rw [h6]
    have h9 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp [h9]
    <;> ring_nf
    <;> norm_num [Real.sqrt_nonneg]
  constructor
  · -- Show that f(7/3) is in the image
    use 7 / 3
    all_goals
    simp [h4, h5]
    <;> norm_num [h1, h2]
  · -- Show that f(7/3) is greatest in the image
    intro y
    rintro ⟨x, hx, hfx⟩
    have hx1 : 1 ≤ x := hx.1
    have hx2 : x ≤ 3 := hx.2
    have hx5 : f x = 2 * Real.sqrt (x - 1) + Real.sqrt (6 - 2 * x) := by 
      rw [h1]
      <;> ring_nf <;> simp [Real.sqrt_nonneg]
    have hx7 : y = 2 * Real.sqrt (x - 1) + Real.sqrt (6 - 2 * x) := by 
      linarith [hfx, hx5]
    have h6 : f (7 / 3) = 2 * Real.sqrt 3 := by 
      rw [h4]
      all_goals try linarith [h5]
    have h7 : f (7 / 3) = 2 * Real.sqrt 3 := h6
    have h8 : y ≤ f (7 / 3) := by
      rw [h7]
      have hx3 : 0 ≤ x - 1 := by linarith
      have hx4 : 0 ≤ 6 - 2 * x := by linarith
      have hx7' : y = 2 * Real.sqrt (x - 1) + Real.sqrt (6 - 2 * x) := by
        linarith [hfx, hx5]
      rw [show y = 2 * Real.sqrt (x - 1) + Real.sqrt (6 - 2 * x) by linarith [hfx, hx5]]
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (6 - 2 * x), 
        sq_nonneg (Real.sqrt (x - 1) - (Real.sqrt (4 / 3))), sq_nonneg (Real.sqrt (6 - 2 * x) - (Real.sqrt (4 / 3))), 
        sq_nonneg (2 * Real.sqrt (x - 1) - Real.sqrt (6 - 2 * x)), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1) by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (6 - 2 * x) by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (4 / 3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sqrt_le_sqrt (show (4 / 3 : ℝ) ≤ (4 : ℝ) by norm_num), 
        Real.sqrt_nonneg (4 / 3), Real.sqrt_nonneg (3 : ℝ), 
        mul_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (6 - 2 * x)), 
        Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1) by linarith)
      ]
    linarith [h8, hx7]