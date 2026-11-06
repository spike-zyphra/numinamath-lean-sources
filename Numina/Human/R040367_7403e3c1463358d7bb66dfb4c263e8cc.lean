import Mathlib



/- The minimum value of the function $y = -\sin^3 x - 2\sin x$ is $\boxed{-3}$. -/
theorem Algebra_9432 (f : ℝ → ℝ) (hf : f = fun (x : ℝ) => - (Real.sin x) ^ 3 - 2 * Real.sin x) :
  IsLeast (Set.range f) (-3) := by
  rw [IsLeast]
  constructor
  -- $-3$ is a lower bound
  · simp
    use (Real.pi / 2)
    simp [hf]
    norm_num
  · rw [lowerBounds]
    simp
    intro x
    set t := Real.sin x
    -- $sinx ≤ 1$
    have ht : t ≤ 1 := by
      simp [t]
      exact Real.sin_le_one x
    -- $-t^3 - 2t$ is monotonically decreasing
    have hf' : Antitone (fun (t : ℝ) => -t ^ 3 - 2 * t) := by
      apply antitone_of_deriv_nonpos
      · apply Differentiable.sub
        · simp
        · apply Differentiable.const_mul differentiable_id
      · intro x
        rw [deriv_sub]
        · rw [deriv_const_mul]
          · simp
            rw [neg_le_iff_add_nonneg]
            positivity
          · apply differentiable_id
        · simp
        · apply Differentiable.const_mul differentiable_id
    -- $- (Real.sin x) ^ 3 - 2 * Real.sin x ≥ -1^3 - 2$
    specialize hf' ht
    simp at hf'
    simp [hf]
    linarith
