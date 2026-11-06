import Mathlib

open Real

theorem algebra_20290 (f : ℝ → ℝ) (hf : f = fun x => 2 * logb 10 x - logb x (1 / 100)) :
    IsLeast {y | ∃ x, x > 1 ∧ f x = y} 4 := by
  constructor
  · -- Show 4 is in the set
    use 10
    constructor
    · -- Show that 10 > 1
      norm_num
    · -- Show that f 10 = 4
      rw [hf]
      have h3 : logb (10 : ℝ) 10 = 1 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h4 : logb (10 : ℝ) (1 / 100 : ℝ) = -2 := by 
        rw [show (1 / 100 : ℝ) = (10 : ℝ) ^ (-2 : ℝ) by norm_num]
        rw [logb_rpow]
        all_goals norm_num
      have h5 : (fun (x : ℝ) => 2 * logb 10 x - logb x (1 / 100 : ℝ)) 10 = 4 := by 
        simp_all [logb_div, logb_pow]
        all_goals linarith
      simpa using h5
  · -- Show 4 is the least element
    intro y hy
    rcases hy with ⟨x, hx1, h_eq⟩
    rw [hf] at h_eq
    have h1 : logb x (1 / 100 : ℝ) = (logb 10 (1 / 100 : ℝ)) / (logb 10 (x : ℝ)) := by 
      field_simp [logb]
      all_goals norm_num
    have h2 : logb 10 (1 / 100 : ℝ) = -2 := by 
      rw [show (1 / 100 : ℝ) = (10 : ℝ) ^ (-2 : ℝ) by norm_num]
      rw [logb_rpow]
      all_goals norm_num
    have eq1 : 2 * logb 10 x - logb x (1 / 100 : ℝ) = 2 * logb 10 x + 2 / (logb 10 x) := by
      rw [h1, h2]
      <;> field_simp [(show logb 10 x ≠ 0 by
        have h3 : logb 10 x > 0 := by
          apply logb_pos
          all_goals linarith
        linarith
      )
      ]
      <;> ring_nf
      <;> field_simp [(show logb 10 x ≠ 0 by
        have h3 : logb 10 x > 0 := by
          apply logb_pos
          all_goals linarith
        linarith
      )
      ]
      <;> linarith
    have h_eq1 : 2 * logb 10 x + 2 / (logb 10 x) ≥ 4 := by
      have h3 : logb 10 x > 0 := by
        apply logb_pos
        all_goals linarith
      have h4 : 2 * (logb 10 x) + 2 / (logb 10 x) - 4 ≥ 0 := by
        have h5 : 2 * (logb 10 x) + 2 / (logb 10 x) - 4 = (2 * (logb 10 x)^2 + 2 - 4 * (logb 10 x)) / (logb 10 x) := by
          field_simp
          ring
        rw [h5]
        have h6 : (2 * (logb 10 x)^2 + 2 - 4 * (logb 10 x)) ≥ 0 := by
          nlinarith [sq_nonneg (logb 10 x - 1)]
        have h7 : (logb 10 x) > 0 := h3
        apply div_nonneg
        · linarith
        · linarith
      linarith
    have h3 : (2 * logb 10 x - logb x (1 / 100 : ℝ)) ≥ 4 := by
      linarith [eq1, h_eq1]
    have h10 : (2 * logb 10 x - logb x (1 / 100 : ℝ)) = y := by 
      simpa using h_eq
    linarith [h10, h3]