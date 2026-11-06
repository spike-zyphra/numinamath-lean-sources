import Mathlib

theorem inequalities_604053 :
    ¬∃ x y z t : ℝ, abs x > abs (y - z + t) ∧ abs y > abs (x - z + t) ∧
      abs z > abs (x - y + t) ∧ abs t > abs (x - y + z) := by
  intro h
  rcases h with ⟨x, y, z, t, h1, h2, h3, h4⟩
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
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t), sq_nonneg (y - z), sq_nonneg (y - t), sq_nonneg (z - t), 
  abs_nonneg (x), abs_nonneg (y), abs_nonneg (z), abs_nonneg (t)]