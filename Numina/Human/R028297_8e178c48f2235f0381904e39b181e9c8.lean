import Mathlib
open Real Set
open scoped BigOperators

/- Determine the intervals of monotonic increase for the function $y = 3 - 2\sin x$. -/
theorem algebra_9391 {f : ℝ → ℝ} (hf : f = λ x => 3 - 2 * sin x) :
    ∀ k : ℤ, MonotoneOn f {x | π / 2 + 2 * k * π ≤ x ∧ x ≤ 3 * π / 2 + 2 * k * π} := by
  intro k
  intro x hx y hy hxy -- Change the goal to proving f(x) ≤ f(y) for x ≤ y in each of the intervals.
  simp at hx hy
  simp only [hf]
  suffices _ : sin x ≥ sin y by
    linarith
  obtain ⟨hx₁, _⟩ := hx
  obtain ⟨_, hy₂⟩ := hy
  have g : sin (x + π + (-k - 1 : ℤ) * (2 * π)) ≤ sin (y + π + (-k - 1 : ℤ) * (2 * π)) := by
    apply sin_le_sin_of_le_of_le_pi_div_two
    repeat
      simp
      linarith
  -- Use the formulae sin (x + 2kπ) = sin x and sin (x + π) = -sin x.
  rw [sin_add_int_mul_two_pi, sin_add_int_mul_two_pi, sin_add_pi, sin_add_pi] at g
  linarith
