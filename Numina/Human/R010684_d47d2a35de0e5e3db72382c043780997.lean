import Mathlib

/- The polynomial $p(x) = x^2+ax+b$ has distinct roots $2a$ and $b$. Find $a+b$. -/
theorem algebra_20306 {a b : ℝ} (p : ℝ → ℝ) (hp: p = fun x => x ^ 2 + a * x + b) (h : 2 * a ≠ b) (h1 : p (2 * a) = 0)
    (h2 : p b = 0) : a + b = -1 := by
  -- Simplify and normalize the equations using the polynomial definition
  simp [hp] at h1 h2
  ring_nf at h1 h2

  -- From h1: (2a)² + a(2a) + b = 0
  -- Solve for b: b = -6a²
  replace h1 : b = -6 * a ^ 2:= by linarith

  -- Substitute b = -6a² into h2: p(b) = 0
  rw [h1] at h2
  ring_nf at h2

  -- After substitution and simplification:
  -- a²(6a² - a - 1) = 0
  replace h2 : a ^ 2 * (6 * a ^ 2 - a - 1) = 0:= by linarith

  -- Prove that a² ≠ 0
  -- If a = 0, then b = 0 (from b = -6a²)
  -- This would contradict h: 2a ≠ b
  have g : a ^ 2 ≠ 0:= by
      by_contra H
      replace H : a = 0:= by exact pow_eq_zero H
      simp [H] at h1
      rw [H, h1] at h
      ring_nf at h
      trivial

  -- Since a² ≠ 0, we can conclude:
  -- 6a² - a - 1 = 0
  replace h2 : 6 * a ^ 2 - a - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g h2

  -- From this equation and b = -6a²,
  -- we can prove that a + b = -1
  linarith
