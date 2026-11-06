import Mathlib

theorem inequalities_190982 (x y t : ℝ) :
    ¬(abs x < abs (y - t) ∧ abs y < abs (t - x) ∧ abs t < abs (x - y)) := by
  rintro ⟨h₁, h₂, h₃⟩
  have h1' : x ^ 2 < (y - t) ^ 2 := by
    apply sq_lt_sq.2 
    exact h₁
  have h2' : y ^ 2 < (t - x) ^ 2 := by 
    apply sq_lt_sq.2 
    exact h₂
  have h3' : t ^ 2 < (x - y) ^ 2 := by
    apply sq_lt_sq.2 
    exact h₃
  have h4 : x ^ 2 + y ^ 2 + t ^ 2 < (y - t) ^ 2 + (t - x) ^ 2 + (x - y) ^ 2 := by 
    linarith 
  have h5 : (y - t) ^ 2 + (t - x) ^ 2 + (x - y) ^ 2 = 2 * (x ^ 2 + y ^ 2 + t ^ 2) - 2 * (x * y + y * t + t * x) := by 
    ring 
  have h7 : x ^ 2 + y ^ 2 + t ^ 2 < 2 * (x ^ 2 + y ^ 2 + t ^ 2) - 2 * (x * y + y * t + t * x) := by 
    nlinarith [h4, h5]
  nlinarith [sq_nonneg (x - y + t), sq_nonneg (y + t - x), sq_nonneg (t + x - y), 
    sq_nonneg (x - y - (y - t) - (t - x)), 
    sq_nonneg (y - (t - x) - (x - y)), 
    sq_nonneg ((y - t) - (t - x) - (x - y)), 
    sq_nonneg (x - y), sq_nonneg (y - t), sq_nonneg (t - x)
  ]