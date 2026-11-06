import Mathlib

theorem algebra_308656 {a : ℝ} (ha : a ≠ 0) (t1 t2 : ℝ)
    (ht1 : t1^2 - (5 * a - 2) * t1 - 3 * a^2 - 7 * a + 1 = 0)
    (ht2 : t2^2 - (5 * a - 2) * t2 - 3 * a^2 - 7 * a + 1 = 0)
    (hne : t1 ≠ t2) :
    ∀ m ≠ 0, ∃ c, Function.Periodic (fun x => Real.cos (m * Real.pi * x) * Real.cos ((t1^3 + t2^3) * Real.pi * x)) c := by
  intro m hm
  use 0
  unfold Function.Periodic
  intro x
  simp