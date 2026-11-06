import Mathlib

/- 3. Solve the equation


$$

2 x+2+x \sqrt{x^{2}+1}+(x+2) \sqrt{x^{2}+4 x+5}=0 .

$$
 -/
theorem algebra_171718 (x : ℝ) (hx : x^2 + 1 ≥ 0) (h : 2 * x + 2 + x * Real.sqrt (x^2 + 1) + (x + 2) * Real.sqrt (x^2 + 4 * x + 5) = 0) :
    x = -1 := by
  -- let f = fun x => x*(1+√(x^2+1))
  let q:∃ f:ℝ → ℝ, f = fun x => x*(1+√(x^2+1)) := by
    use fun x => x*(1+Real.sqrt (x^2 + 1))
  obtain ⟨f, fdef⟩ := q
  -- then the original equation can be expressed as f(x) + f(x+2)=0
  have h0: f x + f (x + 2) = 0 := by
    rw [fdef, ←h]
    ring_nf
  -- we can also show that f is odd
  have h1: ∀ x, f (-x) = -f x := by
    intro x
    rw [fdef]
    ring_nf
  -- we can also show that f is strictly increasing
  have h2: StrictMono f := by
    -- since f is odd we only have to show it's monotonic on nonnegatives
    apply strictMono_of_odd_strictMonoOn_nonneg h1
    unfold StrictMonoOn
    intro a ha b hb hab
    rw [fdef]
    simp at ha hb ⊢
    apply mul_lt_mul hab
    rotate_right
    assumption
    rotate_right
    linarith [Real.sqrt_nonneg (a^2 + 1)]
    simp
    refine Real.sqrt_le_sqrt ?_
    simp
    nlinarith
  have hinj:= StrictMono.injective h2
  -- combine the results
  suffices f x = - f (x + 2) by
    rw [← h1 (x+2)] at this
    specialize hinj this
    linarith
  linarith