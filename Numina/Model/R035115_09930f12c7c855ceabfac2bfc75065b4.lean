import Mathlib

theorem inequalities_166125 :
    ¬∃ x y z t : ℝ,
      abs x > abs (y - z + t) ∧
      abs y > abs (x - z + t) ∧
      abs z > abs (x - y + t) ∧
      abs t > abs (x - y + z) := by 
  rintro ⟨x, y, z, t, h1, h2, h3, h4⟩ 
  have h1' : x^2 > (y - z + t)^2 := by 
    apply sq_lt_sq.mpr 
    exact h1
  have h2' : y^2 > (x - z + t)^2 := by 
    apply sq_lt_sq.mpr 
    exact h2
  have h3' : z^2 > (x - y + t)^2 := by 
    apply sq_lt_sq.mpr 
    exact h3
  have h4' : t^2 > (x - y + z)^2 := by 
    apply sq_lt_sq.mpr 
    exact h4 
  nlinarith [sq_nonneg (x - y + z - t), sq_nonneg (x - z + t - y), 
      sq_nonneg (x - y + t - z), sq_nonneg (y - z + t - x),
      sq_nonneg (x + y - z - t), sq_nonneg (x - y + z - t), 
      sq_nonneg (x - z + y - t), sq_nonneg (y + z - x - t),
      abs_nonneg (x - y + z), abs_nonneg (x - y + t), 
      abs_nonneg (x - z + t), abs_nonneg (y - z + t),
      abs_nonneg x, abs_nonneg y, abs_nonneg z, abs_nonneg t]