import Mathlib

theorem algebra_9024 (f : ℝ → ℝ) (hf : f = fun x => x * Real.sin x) : ∃ m c, ∀ x, x = Real.pi → (f x = m * x + c ∧ m = deriv f Real.pi ∧ c = f Real.pi - m * Real.pi) := by

  use -Real.pi
  use Real.pi ^ 2

  intro x hx

  rw [hx]

  constructor
  · -- Show that f(π) = -π * π + π²
    rw [hf]
    have h1 : Real.sin Real.pi = 0 := Real.sin_pi
    simp [h1]
    <;> nlinarith
  constructor
  · -- Show that -π = deriv f π
    rw [hf]
    simp [deriv_mul, deriv_id'', Real.deriv_sin, Real.sin_pi, Real.cos_pi]
    <;> ring
  · -- Show that c = f(π) - m * π
    rw [hf]
    have h1 : Real.sin Real.pi = 0 := Real.sin_pi
    simp [h1]
    <;> nlinarith