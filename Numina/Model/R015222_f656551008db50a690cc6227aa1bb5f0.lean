import Mathlib

theorem algebra_241689 (f : ℝ → ℝ) :
    (∀ x y, f (x + f y) = f (f y) + 2 * x * f y + x ^ 2) ↔
    ∀ x, f x = x ^ 2 + f 0 := by
  constructor
  · -- First, we show that if $f$ satisfies the equation, then $f(x) = x^2 + f(0)$.
    intro h
    have h1 : ∀ y, f (f y) = f 0 + (f y) ^ 2 := by
      intro y
      have eq1 := h (-f y) y
      have eq2 : -f y + f y = (0 : ℝ) := by ring
      rw [eq2] at eq1
      nlinarith
    have h3 : ∀ x, f (x + f 0) = f (f 0) + 2 * x * f 0 + x ^ 2 := by
      intro x
      specialize h x 0
      simpa using h
    have h4 : ∀ x, f x = x ^ 2 + f 0 := by
      intro x
      have eq4 := h3 (x - f 0)
      have eq5 : f x = f (f 0) + 2 * (x - f 0) * f 0 + (x - f 0) ^ 2 := by
        have eq6 : (x - f 0) + f 0 = (x : ℝ) := by ring
        rw [eq6] at eq4
        linarith
      have eq7 : f (f 0) = f 0 + (f 0) ^ 2 := by
        apply h1 0
      nlinarith
    exact h4
  · -- Now the converse: if $f(x) = x^2 + f(0)$, then $f$ satisfies the equation.
    intro h
    intro x y
    have h1 : ∀ x, f x = x ^ 2 + f 0 := h
    have eq1 : f (x + f y) = (x + f y) ^ 2 + f 0 := by
      specialize h1 (x + f y)
      simpa using h1
    have eq2 : f (f y) = (f y) ^ 2 + f 0 := by
      specialize h1 (f y)
      simpa using h1
    rw [eq1, eq2]
    <;> ring