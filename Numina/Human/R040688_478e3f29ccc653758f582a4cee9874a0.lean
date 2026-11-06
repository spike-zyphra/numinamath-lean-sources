import Mathlib

/- 1. Solve the equation


$$

\sqrt{5 x+1}-2 \sqrt{4-x}+\sqrt{5} \sqrt{x+2}=\sqrt{61-4 x}

$$
 -/
theorem algebra_247723 (x : ℝ) : √ (5 * x + 1) - 2 * √ (4 - x) + √ 5 * √ (x + 2) =
    √ (61 - 4 * x) ∧ 0 ≤ 5 * x + 1 ∧ 0 ≤ 4 - x ∧ 0 ≤ x + 2 ∧ 0 ≤ 61 - 4 * x ↔ x = 3 := by
  constructor
  -- first proving equation implies x = 3
  . rintro ⟨h, h1, h2, h3, h4⟩
    -- change the equation by putting two roots in each side
    nth_rw 1 [show 2 = √(2^2) by simp] at h
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by norm_num)] at h
    replace h : √(5 * x + 1) + √(5 * x + 10) = √(61 - 4 * x) + √(16 - 4 * x) := by
      ring_nf at h ⊢
      linarith
    -- derive bounds for x from validity condition of roots
    have hx_lb : -1/5 ≤ x := by linarith
    have hx_ub : x ≤ 4 := by linarith
    -- define the two sides using following functions
    let f (x : ℝ) := √(5 * x + 1) + √(5 * x + 10)
    let g (x : ℝ) := √(61 - 4 * x) + √(16 - 4 * x)
    replace h : f x = g x := by simpa [f, g]
    -- show that f 3 = g 3 i.e. x = 3 is a solution
    have hfg3 : f 3 = g 3 := by
      simp [f, g]
      norm_num
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, show (16 : ℝ) = 4 ^ 2 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num, show (49 : ℝ) = 7 ^ 2 by norm_num]
      simp
      norm_num
    -- prove f is increasing inside the bounds
    have hf : StrictMonoOn f (Set.Icc (-1 / 5) 4) := by
      rintro a ha b hb hab
      simp [f]
      gcongr
      . linarith [ha.left]
      . linarith [ha.left]
    -- prove g is decreasing inside the bounds
    have hg : StrictAntiOn g (Set.Icc (-1 / 5) 4) := by
      rintro a ha b hb hab
      simp [g]
      gcongr
      . linarith [hb.right]
      . linarith [hb.right]
    -- now we'll prove by contradiction, if not x = 3, then x < 3 or x > 3
    by_contra hc
    obtain hc | hc := lt_or_gt_of_ne hc
    -- in first case f x < g x due to their nature and f 3 = g 3
    . have : f x < g x := by calc
        f x < f 3 := by
          refine hf ?_ (by norm_num) hc
          and_intros <;> linarith
        _ = g 3 := hfg3
        _ < g x := by
          refine hg ?_ (by norm_num) hc
          and_intros <;> linarith
      linarith
    -- in sectonc case g x < f x due to their nature and f 3 = g 3
    . have : g x < f x := by calc
        g x < g 3 := by
          refine hg (by norm_num) ?_ hc
          and_intros <;> linarith
        _ = f 3 := hfg3.symm
        _ < f x := by
          refine hf (by norm_num) ?_ hc
          and_intros <;> linarith
      linarith
  -- in the otherside, if x = 3, then pluggin in we see f x = g x
  . rintro rfl
    norm_num
    rw [show (16 : ℝ) = 4 ^ 2 by ring, show (49 : ℝ) = 7 ^ 2 by ring]
    simp
    norm_num