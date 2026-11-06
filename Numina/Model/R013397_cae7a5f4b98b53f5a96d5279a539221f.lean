import Mathlib

theorem algebra_14035 {f : ℝ → ℝ} (hf0 : f 0 = 1) (hfπ2 : f (Real.pi / 2) = 2)
    (hadd : ∀ x y, f (x + y) + f (x - y) = 2 * f x * Real.cos y) :
    ∀ x, f x = Real.cos x + 2 * Real.sin x := by
  -- first, calculate $f(\pi)$ by setting $x = y = \pi/2$
  have hfpi : f Real.pi = -1 := by
    specialize hadd (Real.pi / 2) (Real.pi / 2)
    have h1 : (Real.pi / 2 : ℝ) + (Real.pi / 2 : ℝ) = Real.pi := by ring
    have h2 : (Real.pi / 2 : ℝ) - (Real.pi / 2 : ℝ) = (0 : ℝ) := by ring
    rw [h1, h2, hfπ2, Real.cos_pi_div_two] at hadd
    rw [hf0] at hadd
    linarith

  -- prove $f(x) + f(-x) = 2\cos(x)$ for all real $x$
  have heven : ∀ x, f x + f (-x) = 2 * Real.cos x := by
    intro x
    specialize hadd (0 : ℝ) x
    simp at hadd
    rw [hf0] at hadd
    linarith

  -- prove $f(x + \pi) = -f(x)$ for all real $x$
  have hp : ∀ x, f (x + Real.pi) = - f x := by
    intro x
    have h1 := hadd (x + Real.pi / 2) (Real.pi / 2)
    have h2 : (x + Real.pi / 2 : ℝ) + (Real.pi / 2 : ℝ) = x + Real.pi := by ring
    have h3 : (x + Real.pi / 2 : ℝ) - (Real.pi / 2 : ℝ) = (x : ℝ) := by ring
    rw [h2, h3, Real.cos_pi_div_two] at h1
    have value := h1
    simp at value
    linarith

  -- finally, derive the explicit form of $f(x)$
  intro x

  -- set $x = \pi/2, y = x + \pi/2$
  have h1 := hadd (Real.pi / 2) (x + Real.pi / 2)

  -- simplify $x + y = \pi/2 + (x + \pi/2) = x + \pi$
  have h2 : Real.pi / 2 + (x + Real.pi / 2) = x + Real.pi := by ring

  -- simplify $x - y = \pi/2 - (x + \pi/2) = -x$
  have h3 : Real.pi / 2 - (x + Real.pi / 2) = -x := by ring

  -- calculate $\cos(x + \pi/2) = -\sin(x)$
  have h4 : Real.cos (x + Real.pi / 2) = - Real.sin x := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring

  rw [h2, h3, hfπ2, h4] at h1

  have h5 : f x + f (-x) = 2 * Real.cos x := heven x

  have h6 : f (x + Real.pi) = - f x := hp x

  have h7 : f (-x) = 2 * Real.cos x - f x := by linarith [h5]

  rw [h6] at h1
  rw [h7] at h1

  linarith