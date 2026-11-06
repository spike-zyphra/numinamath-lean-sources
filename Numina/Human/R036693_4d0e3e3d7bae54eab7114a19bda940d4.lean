import Mathlib
open Real Set

/- Determine the range of the function $y=\log_2(-x^2 + 2x + 7)$. -/
theorem algebra_9142 : image (λ x => logb 2 (-x^2 + 2 * x + 7)) {x | -x^2 + 2 * x + 7 > 0} = {y | y ≤ 3} := by
  -- The function is the composition of the function $g(x) = -x^2 + 2x + 7$ and the function $f(x) = \log_2 x$.
  -- Write g in a more convenient form.
  let g := λ (x : ℝ) => 8 - (x-1)^2
  -- Rewrite the goal
  suffices h : image (λ x => logb 2 (g x)) {x | g x > 0} = {y | y ≤ 3} by
    -- 8 - (x-1)^2 = -x^2 + 2x + 7
    have hg (x : ℝ) : g x = -x^2 + 2 * x + 7 := by
      simp [g]
      ring
    simp only [hg] at h
    exact h

  -- The range of g is {y | y ≤ 8}
  have hg' : range g = {y | y ≤ 8} := by
    ext y
    simp
    -- Two goals: ∃ x, g x = y -> y ≤ 8 and y ≤ 8 -> ∃ x, g x = y
    constructor <;> intro h
    . obtain ⟨x, hx⟩ := h
      subst y
      simp [g]
      -- 8 - (x-1)^2 ≤ 8
      linarith [sq_nonneg (x-1)]
    . -- 8 - (1 + √(8-y) - 1)^2 = y
      use (1 + √(8 - y))
      simp [g]
      rw [sq_sqrt (by linarith)]
      simp

  -- The image of g on {x | g x > 0} is {y | 0 < y ∧ y ≤ 8}
  have hg : image g {x | g x > 0} = {y | 0 < y ∧ y ≤ 8} := by
    ext y
    simp
    -- Two goals: ∃ x, g x = y -> 0 < y ∧ y ≤ 8 and 0 < y ∧ y ≤ 8 -> ∃ x, g x = y
    constructor <;> intro h
    . -- 0 < g x = y ∈ range g
      obtain ⟨x, hx, hgx⟩ := h
      subst y
      refine ⟨hx, ?_⟩
      suffices _ : g x ∈ {y | y ≤ 8} by simpa
      rw [← hg']
      exact mem_range_self x
    . obtain ⟨h1, h2⟩ := h
      apply_fun (y ∈ ·) at hg'
      simp [h2] at hg'
      -- Get x such that g x = y, available because y ∈ range g
      obtain ⟨x, hx⟩ := hg'
      use x
      constructor <;> linarith

  -- Two simple lemmas
  have k1 : (fun x ↦ logb 2 (g x)) = logb 2 ∘ g := rfl
  have k2 : logb 2 8 = 3 := by
    rw [(by norm_num : (8 : ℝ) = 2^(3 : ℝ))]
    exact logb_rpow (by norm_num) (by norm_num)

  -- The image of f ∘ g on D is the image of f on the image of g on D
  rw [k1, ← k2, image_comp, hg]
  ext y
  simp
  -- Two goals: ∃ x, logb 2 (g x) = y -> y ≤ 3 and y ≤ 3 -> ∃ x, logb 2 (g x) = y
  constructor <;> intro h
  . obtain ⟨x, ⟨hx1, hx2⟩, hgx⟩ := h
    subst y
    -- Use monotonicity of logb 2
    exact (logb_le_logb (by norm_num) hx1 (by norm_num)).2 hx2
  . -- 2 ^ y satisfies the conditions
    use 2 ^ y
    refine ⟨⟨?_, ?_⟩, ?_⟩
    . positivity
    . exact (le_logb_iff_rpow_le (by norm_num) (by norm_num)).1 h
    . exact logb_rpow (by norm_num) (by norm_num)
