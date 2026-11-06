import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_16089 (f : ℝ → ℝ) (hf : f = λ x => -3 * x + 5)
  (P : ℝ × ℝ) (hP : P = (-4, -2)) :
  IsLeast {d | ∃ x, d = sqrt ((x - P.1)^2 + (f x - P.2)^2)} (sqrt ((17 / 10 - P.1)^2 + (-1 / 10 - P.2)^2)) := by 
  rw [hP] at *
  rw [hf] at *
  constructor 
  · -- Show that sqrt ((17 / 10 + 4) ^ 2 + (-1 / 10 + 2) ^ 2) is in the set
    use 17 / 10 
    all_goals norm_num 
  · -- Show that sqrt ((17 / 10 + 4) ^ 2 + (-1 / 10 + 2) ^ 2) is the least element 
    intro d hd 
    rcases hd with ⟨x, hx⟩ 
    have h1 : sqrt ((x - (-4: ℝ)) ^ 2 + (-3 * x + 5 - (-2: ℝ)) ^ 2) ≥ sqrt ((17 / 10 - (-4: ℝ)) ^ 2 + (-1 / 10 - (-2: ℝ)) ^ 2) := by 
      have h2 : (x - (-4: ℝ)) ^ 2 + (-3 * x + 5 - (-2: ℝ)) ^ 2 ≥ (17 / 10 - (-4: ℝ)) ^ 2 + (-1 / 10 - (-2: ℝ)) ^ 2 := by 
        nlinarith [sq_nonneg (x - 17 / 10)]
      apply Real.sqrt_le_sqrt 
      all_goals linarith 
    have hx' : sqrt ((x - (-4: ℝ)) ^ 2 + (-3 * x + 5 - (-2: ℝ)) ^ 2) = d := by 
      linarith [hx] 
    linarith [hx', h1]