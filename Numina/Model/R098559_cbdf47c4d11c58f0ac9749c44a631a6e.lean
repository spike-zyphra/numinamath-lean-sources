import Mathlib

theorem number_theory_301035 (a : ℕ) (ha : 0 < a) :
    ∃ f : ℕ → ℝ, ∀ x y, 0 < x → 0 < y → x * y > a → f (x + y) = f (x * y - a) := by 
  use (fun _ => (0 : ℝ))
  intro x y hx hy hxya
  all_goals simp