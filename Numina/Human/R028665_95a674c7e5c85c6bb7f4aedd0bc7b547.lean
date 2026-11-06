import Mathlib

open Real Int Nat

/-
Given a function $f(x)$ defined on $\mathbb{R}$ that is an even function with a period of $\pi$, and for $x \in [0, \frac{\pi}{2}]$, $f(x)= \frac{\pi}{2}-x$. Find the value of $f\left( \frac{5\pi}{3}\right)$.
-/
theorem algebra_9306 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x)
    (h₁ : ∀ x, f (x + Real.pi) = f x) (h₂ : ∀ x ∈ Set.Icc 0 (Real.pi / 2), f x = Real.pi / 2 - x) :
    f (5 * Real.pi / 3) = Real.pi / 6 := by
  -- Having a period of $\pi$ means that $f(x + k\pi) = f(x)$ for any integer $k$.
  have hcycle : ∀ (k : Int), ∀ x, f (x + k * Real.pi) = f x := by
    intro k x
    have h0 : f (x + (0 : ℤ) * π) = f x := by simp_all
    have hp : ∀ (i : ℕ), f (x + i * π) = f x → f (x + (i + 1 : ℤ) * π) = f x := by
      intro i h
      simp_all
      have := h₁ (x + i * π)
      rw [h] at this
      have h' : x + i * π + π = x + (i + 1) * π := by ring
      rw [h'] at this
      exact this
    have hn : ∀ (i : ℕ), f (x + (-i : ℤ) * π) = f x → f (x + (-i - 1 : ℤ) * π) = f x := by
      intro i h; simp_all
      have h' := h₁ (x + (-i - 1 : ℤ) * π)
      simp at h'
      have : x + (-i - 1 : ℤ) * π + π = x + (-i : ℤ) * π := by simp_all; ring_nf
      simp at this
      rw [this] at h'
      rw [← h']
      exact h
    exact Int.induction_on k h0 hp hn
  -- $$f\left(\frac{5\pi}{3}\right) = f\left(\frac{5\pi}{3} - 2\pi\right) = f\left(-\frac{\pi}{3}\right).$$
  have h1 : f (5 * π / 3) = f (-π / 3) := by
    have := hcycle (-2) (5 * π / 3)
    ring_nf at this; ring_nf
    exact Eq.symm this
  rw [h1]
  -- Next, because $f(x)$ is an even function,
  have h2 : f (-π / 3) = f (π / 3) := by
    have := h₀ (π / 3)
    ring_nf at this; ring_nf
    exact this
  rw [h2]
  have : π / 3 ∈ Set.Icc 0 (π / 2) := by
    constructor
    · exact div_nonneg Real.pi_nonneg (by linarith)
    · exact mul_le_mul_of_nonneg_left (by norm_num) (Real.pi_nonneg)
  -- Since $\frac{\pi}{3}$ is within the given interval $[0, \frac{\pi}{2}]$, we can use the defined expression for $f(x)$:
  rw [h₂ (π / 3) this]
  ring_nf
  -- Therefore, the value of $f\left( \frac{5\pi}{3}\right)$ is $\boxed{\frac{\pi}{6}}$.
