import Mathlib

theorem algebra_29988 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 - 2 * x + 1) :
    {k : ℝ | ∀ x, f (x + k) = x ^ 2 + 2 * x + 1} = {2} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume that $k$ is a solution, i.e., $f(x+k) = x^2+2x+1$ for all $x$.
    intro h
    have eq1 := h 0
    rw [hf] at eq1
    have eq2 : k ^ 2 - 2 * k = 0 := by
      nlinarith
    have eq2k : k * (k - 2) = 0 := by 
      linarith
    have eq3 := h 1
    rw [hf] at eq3
    have eq4 : k ^ 2 = 4 := by
      nlinarith
    cases' (mul_eq_zero.mp eq2k) with h1 h2
    · -- If k = 0, which contradicts
      nlinarith
    · -- k - 2 = 0, i.e., k = 2
      linarith
  · -- Assume k = 2, prove that it satisfies f(x + k) = x^2 + 2 * x + 1
    intro hk
    rw [hk]
    intro x
    rw [hf]
    ring