import Mathlib

open Real 

/-- Find the sum of the $x$-coordinates of the distinct points of intersection of the plane curves given by $x^{2}=x+y+4$ and $y^{2}=y-15 x+36$.-/
theorem Algebra_611308 {x y: ℝ} (h1 : x ^ 2 = x + y + 4) (h2 : y ^ 2 = y - 15 * x + 36) : 
x = 2 ∨ x = - 1 + 5 ^ (1 / (2 : ℝ)) ∨ x = - 1 - 5 ^ (1 / (2 : ℝ)) := by 
  have y_eq : y = x ^ 2 - x - 4 := by 
    calc 
      _ = (x + y + 4) - x - 4 := by ring
      _ = x ^ 2 - x - 4 := by 
        rw [←h1]
  have eq_zero : y ^ 2 - (y - 15 * x + 36) = 0 := by rw [←h2]; ring
  have eq_zero' : (x - 2) ^ 2 * (x ^ 2 + 2 * x - 4) = 0 := by 
    rw [←eq_zero, y_eq]
    ring
  obtain h' := mul_eq_zero.mp eq_zero'
  -- two case `(x - 2) ^ 2 = 0 ∨ x ^ 2 + 2 * x - 4 = 0`
  -- first case `(x - 2) ^ 2 = 0`
  obtain h₁ | h₂ := h'
  · left
    simp at h₁
    calc
      _ = x - 2 + 2 := by ring
      _ = 2 := by rw [h₁]; simp
  · -- second case `x ^ 2 + 2 * x - 4 = 0`
    right
    -- just use the `quadratic_eq_zero_iff.2`
    have eq : 1 * (x * x) + 2 * x + (-4) = x ^ 2 + 2 * x - 4  := by ring
    rw [←eq] at h₂
    have x_root : x = (- 2 + 2 * 5 ^ (1 / (2 : ℝ))) / (2 * (1 : ℝ)) 
      ∨ x = (- 2 - 2 * 5 ^ (1 / (2 : ℝ))) / (2 * (1 : ℝ)) := by 
      refine(quadratic_eq_zero_iff (by norm_num) ?_ x).mp h₂
      unfold discrim
      have dis_eq : 2 * 5 ^ (1 / (2 : ℝ)) * (2 * (5 : ℝ) ^ (1 / (2 : ℝ))) = 20 := by 
        calc
          _ = 2 * 2 * (5 ^ (1 / (2 : ℝ)) * (5 : ℝ) ^ (1 / (2 : ℝ))) := by ring
          _ = 4 * (5 ^ (1 / (2 : ℝ)) * (5 : ℝ) ^ (1 / (2 : ℝ))) := by norm_num
          _ = 4 * 5 := by 
            congr
            rw [←mul_rpow]
            have eq_aux : (5 : ℝ) * 5 = 5 ^ (2 : ℝ) := by ring
            rw [eq_aux]
            rw [←rpow_mul]
            simp
            positivity
            positivity
            positivity
          _ = 20 := by norm_num
      rw [dis_eq]
      norm_num
    field_simp at x_root
    obtain x₁ | x₂ := x_root
    left 
    calc 
      _ = x * 2 / (2 : ℝ) := by ring
      _ = -1 + 5 ^ (1 / (2 : ℝ)) := by 
        rw [x₁]
        field_simp
        ring_nf
    right 
    calc 
      _ = x * 2 / (2 : ℝ) := by ring
      _ = -1 - 5 ^ (1 / (2 : ℝ)) := by 
        rw [x₂]
        field_simp
        ring_nf