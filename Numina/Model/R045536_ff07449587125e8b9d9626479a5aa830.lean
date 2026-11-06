import Mathlib

theorem algebra_309995 : IsLeast {x : ℝ | ∃ s t : ℝ, x = (s + 5 - 3*abs (Real.cos t))^2 + (s - 2*abs (Real.sin t))^2} 2 := by
  constructor
  · -- Show 2 is in the set
    use -1, 0
    norm_num [abs_zero, Real.cos_zero, Real.sin_zero]
  · -- Show 2 is the minimum
    intro x hx
    rcases hx with ⟨s, t, h⟩
    have h3 : (s + 5 - 3*abs (Real.cos t))^2 + (s - 2*abs (Real.sin t))^2 ≥ 2 := by
      have h1 : abs (Real.cos t) ≤ 1 := by
        apply abs_le.mpr
        constructor
        · -- Show that -1 ≤ Real.cos t
          linarith [Real.neg_one_le_cos t, Real.cos_le_one t]
        · -- Show that Real.cos t ≤ 1
          linarith [Real.neg_one_le_cos t, Real.cos_le_one t]
      have h2 : abs (Real.sin t) ≤ 1 := by
        apply abs_le.mpr
        constructor
        · -- Show that -1 ≤ Real.sin t
          linarith [Real.neg_one_le_sin t, Real.sin_le_one t]
        · -- Show that Real.sin t ≤ 1
          linarith [Real.neg_one_le_sin t, Real.sin_le_one t]
      have h4 : (s + 5 - 3*abs (Real.cos t))^2 + (s - 2*abs (Real.sin t))^2 ≥ 2 := by
        nlinarith [sq_nonneg (s + 1), sq_nonneg (abs (Real.cos t) - 1), sq_nonneg (abs (Real.sin t) - 0), 
          Real.sin_sq_add_cos_sq t, 
          abs_nonneg (Real.sin t), abs_nonneg (Real.cos t), 
          mul_nonneg (abs_nonneg (Real.cos t)) (abs_nonneg (Real.sin t))
        ]
      linarith
    linarith [h, h3]