import Mathlib

/- A ball travels on a parabolic path in which the height (in feet) is given by the expression $-16t^2+80t+21$, where $t$ is the time after launch. What is the maximum height of the ball, in feet? -/
theorem algebra_10400 (h : ℝ → ℝ) (h_def : h = fun t => -16 * t ^ 2 + 80 * t + 21) :
    IsGreatest (Set.image h (Set.Ici 0)) 121 := by
  simp_all only [Set.image, Set.Icc, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_range,
    Set.mem_preimage, exists_prop]
  refine' ⟨⟨5 / 2, by norm_num [h_def]⟩, _⟩
  rintro y ⟨x, hxy, rfl⟩
  norm_num [h_def] at hxy ⊢
  nlinarith [sq_nonneg (x - 5 / 2)]