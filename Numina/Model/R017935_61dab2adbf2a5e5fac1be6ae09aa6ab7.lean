import Mathlib

open Real Set

/- When $s$ and $t$ take all real numbers, the minimum value that can be achieved by ${{\left( s+5-3|\cos t| \right)}^{2}}+{{\left( s-2|\sin t| \right)}^{2}}$ is ___          ___. -/
theorem algebra_9870 :
  IsLeast {x : ℝ | ∃ s t : ℝ, x = (s + 5 - 3 * abs (cos t))^2 + (s - 2 * abs (sin t))^2} 2 := by
  constructor
  · -- Show 2 is achievable by finding specific s and t
    use -1, 0
    have h1 : abs (cos (0 : ℝ)) = 1 := by
      simp [abs_of_nonneg]
    have h2 : abs (sin (0 : ℝ)) = (0 : ℝ) := by
      simp [abs_of_nonneg]
    norm_num [h1, h2]
    <;> norm_num [abs_of_nonneg]
  · -- Show 2 is the minimal value
    intro x hx
    rcases hx with ⟨s, t, heq⟩
    have h1 : 0 ≤ abs (cos t) := abs_nonneg (cos t)
    have h2 : 0 ≤ abs (sin t) := abs_nonneg (sin t)
    have h3 : abs (cos t) ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [Real.cos_sq_add_sin_sq t, sq_nonneg (cos t), sq_nonneg (sin t)]
    have h4 : abs (sin t) ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [Real.cos_sq_add_sin_sq t, sq_nonneg (cos t), sq_nonneg (sin t)]
    have h5 : (s + 5 - 3 * abs (cos t))^2 + (s - 2 * abs (sin t))^2 ≥ 2 := by
      nlinarith [sq_nonneg (s + 1), sq_nonneg (abs (cos t) - 1), sq_nonneg (abs (sin t) - 0), 
        Real.cos_sq_add_sin_sq t, 
        abs_nonneg (cos t), abs_nonneg (sin t), 
        mul_nonneg (show (0 : ℝ) ≤ abs (cos t) by positivity) (show (0 : ℝ) ≤ abs (sin t) by positivity), 
        sq_nonneg (abs (cos t)), sq_nonneg (abs (sin t)), 
        sq_nonneg (abs (cos t) - 1), sq_nonneg (abs (sin t) - 0)
      ]
    linarith [heq, h5]