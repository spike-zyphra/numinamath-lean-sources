import Mathlib

/- Find all functions $f: \mathbf{R} \rightarrow \mathbf{R}$ satisfying the equation

$$
|x| f(y)+y f(x)=f(x y)+f\left(x^{2}\right)+f(f(y))
$$

for all real numbers $x$ and $y$. -/
theorem algebra_605549 (f : ℝ → ℝ) :
    (∀ x y, abs x * f y + y * f x = f (x * y) + f (x ^ 2) + f (f y)) ↔
    ∃ c ≥ 0, ∀ x, f x = c * (abs x - x) := by
  constructor; intro h
  · -- first direction.
    -- denote a = f(0)
    set a := f 0 with a_def
    -- then f(a) = -2a
    have hfa: f a = -2 * a := by
      -- choose x=y=0
      have := h 0 0
      simp [← a_def] at this
      linarith [this]
    -- and we claim f(x^2) = a(|x|+1)
    have h1(x:ℝ): f (x^2) = a * (|x|+1) := by
      -- choose y=0
      have := h x 0
      simp [← a_def, hfa] at this
      nlinarith [this]
    -- further more, we can prove az^2 = a + f(2a)
    have h2(z:ℝ): a*z^2 = a + f (2*a) := by
      -- choose (x,y) = (z^2, 1)
      have := h (z^2) 1
      -- notice that from h1, f 1 = 2a
      have hf1: f 1 = 2*a := by
        replace := h1 1
        simp at this; simp [this]; ring
      simp [hf1, h1 (z^2)] at this
      nlinarith [this]
    -- therefore a must be zero
    -- because left side az^2 depends on z, but right side is constant
    have aeq: a = 0 := by
      have hh1 := h2 0
      have hh2 := h2 1
      simp at hh1 hh2
      simp [hh2] at hh1
      exact hh1.symm
    -- then f(x^2) = 0, i.e., f (x) = 0 for all x ≥ 0
    have h3{x:ℝ}(x_nng: 0 ≤ x): f x = 0 := by
      have hh1: x = (√x)^2 := by simp [x_nng]
      have hh2 := h1 (√x)
      simp [← hh1, aeq] at hh2
      exact hh2
    have h3'(x:ℝ): f (x^2) = 0 := by
      simp [h1 x, aeq]
    -- and f(f(y)) = 0 for all y
    have h4(y:ℝ): f (f y) = 0 := by
      -- choose x = 0
      have := h 0 y
      simp [← a_def, aeq] at this
      exact this.symm
    -- simplify the original equation.
    have hfxy(x y: ℝ): f (x*y) = |x| * (f y) + y * (f x) := by
      have := h x y
      simp [h4 y, h3' x] at this
      rw [← this]
    -- swap x,y, following holds.
    have h'(x y: ℝ): |x| * (f y) + y * (f x) = |y| * (f x) + x * (f y) := by
      rw [← hfxy y x, mul_comm y x, hfxy x y]
    -- let c = f(-1)/2
    set c := (f (-1))/2 with c_def'
    have c_def: f (-1) = 2*c := by
      simp [c_def']; ring
    -- choose y = -1
    have hfx(x:ℝ): f x = c*(|x|-x) := by
      have := h' x (-1)
      simp [c_def] at this
      nlinarith [this]
    -- easy to verify c ≥ 0
    have c_nng: 0 ≤ c := by
      by_contra! hc
      have := hfx (2*c)
      -- f (2c) = f(f(-1)) = 0
      replace: c*(|2*c|-2*c) = 0 := by
        rw [← this, ← c_def, h4 (-1)]
      -- but we suppose c < 0, contradiction.
      rcases (mul_eq_zero.mp this) with hh1 | hh2
      · simp [hh1] at hc
      · rw [abs_of_neg (by linarith [hc])] at hh2
        have: c = 0 := by linarith [hh2]
        simp [this] at hc
    -- done
    use c
  · -- verify this is the function desired.
    rintro ⟨c, c_nng, hf⟩ x y
    have hsub: |(|y| - y)| = |y|-y := by
      by_cases hy: 0 ≤ y
      · simp [abs_of_nonneg hy]
      · push_neg at hy
        simp [abs_of_neg hy, le_of_lt hy]
    have h1: f (f y) = 0 := by
      simp [hf, abs_mul, hsub]; right
      simp [abs_of_nonneg c_nng]
    have h2: f (x^2) = 0 := by
      simp [hf]
    simp [h1, h2, hf, abs_mul, hsub, abs_of_nonneg c_nng]
    ring