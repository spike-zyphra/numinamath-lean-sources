import Mathlib

open Real Set

theorem algebra_101429 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = min (min (4 * x + 1) (x + 2)) (-2 * x + 4)) :
    IsGreatest (range (fun x => 6 * f x + 2012)) 2028 := by
  constructor
  · -- Show that 2028 is in the range.
    use 2 / 3
    have h1 : f (2 / 3) = 8 / 3 := by 
      rw [h₀]
      norm_num [min_eq_left, min_eq_right]
    have h2 : (fun x : ℝ => 6 * f x + 2012) (2 / 3) = 2028 := by 
      simp [h1]
      <;> norm_num
    exact h2
  · -- Show that 2028 is greatest
    intro y hy
    rcases hy with ⟨x, hx⟩
    have eq1 : (fun x₀ : ℝ => 6 * f x₀ + 2012) x = 6 * f x + 2012 := by
      simp
    have eq2 : 6 * f x + 2012 ≤ 2028 := by
      have hfx_le : f x ≤ 8 / 3 := by 
        have eq3 : f x = min (min (4 * x + 1) (x + 2)) (-2 * x + 4) := h₀ x 
        rw [eq3]
        by_cases h1 : (4 * x + 1) ≤ (x + 2)
        · -- When $4x + 1 \le x + 2$ (i.e., $x \le 1/3$)
          have eq4 : min (4 * x + 1) (x + 2) = 4 * x + 1 := by
            apply min_eq_left
            linarith [h1]
          rw [eq4]
          by_cases h2 : (4 * x + 1) ≤ (-2 * x + 4)
          · -- When $4x + 1 \le -2x + 4$ (i.e., $x \le 5/12$)
            have eq5 : min (4 * x + 1) (-2 * x + 4) = 4 * x + 1 := by 
              apply min_eq_left 
              linarith [h2]
            rw [eq5]
            linarith 
          · -- When $4x + 1 > -2x + 4$ (i.e., $x > 5/12$)
            have eq6 : min (4 * x + 1) (-2 * x + 4) = -2 * x + 4 := by 
              apply min_eq_right 
              linarith [h2]
            rw [eq6]
            linarith 
        · -- When $4x + 1 > x + 2$ (i.e., $x > 1/3$)
          have eq7 : min (4 * x + 1) (x + 2) = x + 2 := by 
            apply min_eq_right 
            linarith [show (x + 2) ≤ (4 * x + 1) by linarith [h1]]
          rw [eq7]
          by_cases h2 : (x + 2) ≤ (-2 * x + 4)
          · -- When $x + 2 \le -2x + 4$ (i.e., $x \le 2/3$)
            have eq8 : min (x + 2) (-2 * x + 4) = x + 2 := by 
              apply min_eq_left 
              linarith [h2]
            rw [eq8]
            linarith 
          · -- When $x + 2 > -2x + 4$ (i.e., $x > 2/3$)
            have eq9 : min (x + 2) (-2 * x + 4) = -2 * x + 4 := by 
              apply min_eq_right 
              linarith [h2]
            rw [eq9]
            linarith 
      linarith 
    have h4 : (fun x₀ : ℝ => 6 * f x₀ + 2012) x = y := hx
    linarith [eq2, eq1, h4]