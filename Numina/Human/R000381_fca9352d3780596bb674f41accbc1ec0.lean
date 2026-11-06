import Mathlib

/-Define a function $f(x)$ on $\mathbb{R}$ that is an increasing function. Then, the range of values that satisfy $f(x) < f(2x-3)$ is.-/
theorem algebra_9316 {f : ℝ → ℝ} (h_inc : StrictMono f) :
  ∀ x : ℝ, (f x < f (2*x - 3) ↔ x > 3) := by
  intro x
  constructor
  · intro h
    have h1 : x < 2*x - 3 := by exact (StrictMono.lt_iff_lt h_inc).mp h 
    linarith
  · intro h
    apply h_inc
    have h1 : x > 3 := h
    have h2 : 2*x > 6 := by linarith
    have h3 : 2*x - 3 > x := by linarith
    exact lt_of_lt_of_le h3 (le_refl _)