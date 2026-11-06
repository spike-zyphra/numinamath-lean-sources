import Mathlib

theorem algebra_278799 : IsLeast {x : ℝ | ∃ s t : ℝ, x = (s + 5 - 3 * abs (Real.cos t))^2 + (s - 2 * abs (Real.sin t))^2} 2 := by
  constructor
  · -- Show that 2 is in the set.
    use -1, 0
    norm_num [Real.cos_zero, Real.sin_zero, abs_of_nonneg]
  · -- Show that 2 is the minimum.
    intro x hx
    rcases hx with ⟨s, t, h⟩
    have h1 : 0 ≤ abs (Real.cos t) := abs_nonneg (Real.cos t)
    have h2 : 0 ≤ abs (Real.sin t) := abs_nonneg (Real.sin t)
    have h3 : (abs (Real.cos t))^2 + (abs (Real.sin t))^2 = 1 := by
      have ht1 : (Real.cos t)^2 + (Real.sin t)^2 = 1 := Real.cos_sq_add_sin_sq t
      have ht4 : (abs (Real.cos t))^2 + (abs (Real.sin t))^2 = (Real.cos t)^2 + (Real.sin t)^2 := by
        have h1 : (abs (Real.cos t))^2 = (Real.cos t)^2 := by
          rw [sq_abs]
        have h2 : (abs (Real.sin t))^2 = (Real.sin t)^2 := by
          rw [sq_abs]
        rw [h1, h2]
      nlinarith
    have h4 : (s + 5 - 3 * abs (Real.cos t))^2 + (s - 2 * abs (Real.sin t))^2 ≥ 2 := by
      nlinarith [sq_nonneg ((s + 1) ), sq_nonneg ((abs (Real.cos t) - 1) ), sq_nonneg ((abs (Real.sin t) - 0) ), 
        sq_nonneg ((s +1 - (abs (Real.sin t) )) ), sq_nonneg ((abs (Real.cos t) - abs (Real.sin t) ) ), 
      mul_nonneg (abs_nonneg (Real.cos t)) (abs_nonneg (Real.sin t)), 
        sq_nonneg ((abs (Real.cos t)) ^ 2 - (abs (Real.sin t)) ^ 2 ), 
          sq_nonneg ((s) - (abs (Real.cos t) ) ) ]
    linarith [h4, h]