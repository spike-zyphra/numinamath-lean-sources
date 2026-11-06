import Mathlib

/-when s and t take all real values, the minimum value that can be reached by (s + 5 - 3*abs (Real.cos t))^2 + (s - 2*abs (Real.sin t))^2 is ?-/
theorem algebra_309995 : IsLeast {x : ℝ | ∃ s t : ℝ, x = (s + 5 - 3*abs (Real.cos t))^2 + (s - 2*abs (Real.sin t))^2} 2 := by
  constructor
  -- the forward direction --
  · -- Prove that 2 belongs to the set
    use -1, 0
    norm_num [Real.cos_zero, Real.sin_zero]
  -- the backward direction --
  · -- Prove that 2 is a lower bound
    intro x hx
    rcases hx with ⟨s, t, h⟩
    have h1 : abs (Real.cos t) ≤ 1 := abs_le.mpr (Real.cos_mem_Icc t)
    have h2 : abs (Real.sin t) ≤ 1 := abs_le.mpr (Real.sin_mem_Icc t)
    -- we use completing the square technique to show that --
    have h3 : (s + 5 - 3 * abs (Real.cos t)) ^ 2 + (s - 2 * abs (Real.sin t)) ^ 2 ≥ 2 := by
      nlinarith [sq_nonneg (s + 5 - 3 * abs (Real.cos t) + 1), sq_nonneg (s - 2 * abs (Real.sin t) + 1),
        abs_nonneg (Real.cos t), abs_nonneg (Real.sin t), Real.cos_sq_add_sin_sq t]
    linarith [h, h3]