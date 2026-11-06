import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9234 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => exp x + a * exp (-x)) :
    a = -1 → (∀ x y, x < y → f x < f y) := by
  intro ha x y hxy
  rw [hf]
  simp [ha]
  have h1 : exp x < exp y := by
    apply Real.exp_strictMono
    all_goals linarith
  have h2 : exp (-y) < exp (-x) := by
    have h3 : -y < -x := by linarith
    apply Real.exp_strictMono
    all_goals linarith
  have h3 : exp x + exp (-y) < exp y + exp (-x) := by
    linarith [h1, h2, Real.exp_nonneg x, Real.exp_nonneg (-x), Real.exp_nonneg y, Real.exp_nonneg (-y), Real.exp_pos x, Real.exp_pos y, Real.exp_pos (-x), Real.exp_pos (-y), mul_pos (show 0 < exp x by positivity) (show 0 < exp (-y) by positivity), mul_pos (show 0 < exp y by positivity) (show 0 < exp (-x) by positivity) ]
  linarith [h3, Real.exp_nonneg x, Real.exp_nonneg y, Real.exp_nonneg (-x), Real.exp_nonneg (-y) ]