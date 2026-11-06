import Mathlib


theorem algebra_281425 :
    ∃ x y : ℝ, x^3 = y ∧ ∃ x' y' : ℝ, x'^3 + abs x' + 1 = y' ∧
      Real.sqrt ((x - x')^2 + (y - y')^2) ≤ 1 / 100 := by
  use 49 + 50 / 7203, (49 + 50 / 7203) ^ 3 --A
  constructor
  · -- Show $A$ is on $y = x^{3}$.
    norm_num
  · -- Show the existence of point $B$.
    use 49, (49 : ℝ) ^ 3 + 49 + 1 --B
    constructor
    · -- Show $B$ is on $y = x^{3}+|x|+1$.
      norm_num [abs_of_nonneg]
    · -- Show distance $\leq \frac{1}{100}$.
      have h1 : Real.sqrt ((49 + 50 / 7203 - (49 : ℝ)) ^ 2 + ((49 + 50 / 7203 : ℝ) ^ 3 - ((49 : ℝ) ^ 3 + (49 : ℝ) + 1 : ℝ)) ^ 2) ≤ (1 / 100 : ℝ) := by
        have h2 : (49 + 50 / 7203 - (49 : ℝ)) ^ 2 + ((49 + 50 / 7203 : ℝ) ^ 3 - ((49 : ℝ) ^ 3 + (49 : ℝ) + 1 : ℝ)) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
          norm_num [abs_of_nonneg]
        have h3 : Real.sqrt ((49 + 50 / 7203 - (49 : ℝ)) ^ 2 + ((49 + 50 / 7203 : ℝ) ^ 3 - ((49 : ℝ) ^ 3 + (49 : ℝ) + 1 : ℝ)) ^ 2) ≤ Real.sqrt ((1 / 100 : ℝ) ^ 2) := by
          apply Real.sqrt_le_sqrt
          linarith
        have h4 : Real.sqrt ((1 / 100 : ℝ) ^ 2) = (1 / 100 : ℝ) := by
          rw [Real.sqrt_sq (show (0 : ℝ) ≤ (1 / 100 : ℝ) by norm_num)]
        linarith [h3, h4]
      simpa using h1