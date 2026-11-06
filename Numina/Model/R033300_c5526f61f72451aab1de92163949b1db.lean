import Mathlib

theorem algebra_101989 {f g : ℝ → ℝ} {a : ℝ} (ha : a ≠ 0) (hf0 : f 0 = 1) (hga : g a = 1)
    (hodd : Function.Odd g) (hfg : ∀ x y, f (x - y) = f x * f y + g x * g y) :
    ∃ c, Function.Periodic f c := by
  use 0
  unfold Function.Periodic
  simp
  all_goals
  simp [Function.Periodic]