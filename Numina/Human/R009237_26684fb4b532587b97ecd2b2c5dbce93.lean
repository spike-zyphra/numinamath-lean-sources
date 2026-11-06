import Mathlib

/-!
Let `x₁`, `x₂`, `x₃` be the roots of the polynomial `x³ - a x² + a x - a = 0`
with `a > 0`. We are to minimize the expression `x₁³ + x₂³ + x₃³ - 3x₁x₂x₃`.

By Vieta:
- x₁ + x₂ + x₃ = a
- x₁x₂ + x₂x₃ + x₃x₁ = a
- x₁x₂x₃ = a

So the target expression becomes:
  f(a) = a³ - 3a²

We minimize f(a) for a > 0.
-/

open Real

noncomputable def f (a : ℝ) := a ^ 3 - 3 * a ^ 2

-- Identity: f x - f 2 = (x - 2)^2 * (x + 1)
lemma fx_minus_f2 (x : ℝ) : f x - f 2 = (x - 2)^2 * (x + 1) := by
  simp [f]
  ring_nf

-- Final theorem: f attains its minimum at a = 2 for a > 0
theorem Algebra_608206 : ∃ a > 0, ∀ x > 0, f a ≤ f x := by
  use 2
  constructor
  · norm_num  -- 2 > 0
  · intro x hx
    -- f x - f 2 = (x - 2)^2 * (x + 1)
    have h_eq : f x - f 2 = (x - 2)^2 * (x + 1) := fx_minus_f2 x
    -- It suffices to prove: 0 ≤ (x - 2)^2 * (x + 1)
    suffices : 0 ≤ (x - 2)^2 * (x + 1)
    · linarith [this]
    apply mul_nonneg
    · apply sq_nonneg
    · linarith [hx]  -- x > 0 ⇒ x + 1 > 0
