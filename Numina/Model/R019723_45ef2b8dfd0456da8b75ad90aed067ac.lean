import Mathlib

theorem calculus_40991 {f : ℝ → ℝ} (hf : ∃ a b, a ≠ b ∧ ∀ x, f (a - x) + f (a + x) = 2 * f a ∧ f (b - x) + f (b + x) = 2 * f b) :
    ∃ g h, ∀ x, f x = g x + h x ∧ (∃ m c, g = fun x => m * x + c) ∧ (∃ k, Function.Periodic h k) := by
  use (fun x => (0 : ℝ) * x + (0 : ℝ))
  use (fun x => f x - (0 : ℝ) * x - (0 : ℝ))
  intro x
  constructor
  · -- Show $f\ x = g\ x + h\ x$.
    simp
  constructor
  · -- Show `∃ m c, g = fun x => m * x + c`
    use (0 : ℝ)
    use (0 : ℝ)
    all_goals
      funext x
      simp
  · -- Show `∃ k, Function.Periodic h k`
    use (0 : ℝ)
    unfold Function.Periodic
    intro x
    simp