import Mathlib

/- A ball travels on a parabolic path in which the height (in feet) is given by the expression $-16t^2+32t+15$, where $t$ is the time after launch. What is the maximum height of the ball, in feet? -/
theorem algebra_13164 (h : ℝ → ℝ) (h_def : h = fun t => -16 * t ^ 2 + 32 * t + 15) :
    IsGreatest (Set.image h {t | t ≥ 0}) 31 := by
  simp_all only [Set.image, Set.mem_setOf_eq]
  refine' ⟨by use 1; norm_num, fun x hx ↦ _⟩
  obtain ⟨t, ht, rfl⟩ := hx
  linarith [sq_nonneg (t - 1)]