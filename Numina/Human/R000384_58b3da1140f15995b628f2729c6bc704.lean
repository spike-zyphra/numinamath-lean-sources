import Mathlib

open Real Set
open scoped BigOperators

/-Given the function $f(x)=\ln (2+x)+\ln (2-x)$, determine whether it is an odd function, an even function, an increasing function, or a decreasing function on the interval $(0,2)$.-/
theorem algebra_9348 {f : ℝ → ℝ} (hf : f = λ x => log (2 + x) + log (2 - x)) :
(∀ x ∈ Set.Ioo (-2) 2, f x = f (-x)) ∧ StrictAntiOn f (Set.Ioo 0 2) := by
-- Split goals and introduce assumptions
  constructor
  · intro x hx
-- Write out $f$ and prove $f$ is even
    simp [hf]; rw [← sub_eq_add_neg]; ring
-- Write out the definition of a decreasing function
  rw [StrictAntiOn]; intro a ha b hb hab; simp at ha hb
  simp [hf]; rw [← log_mul, ← log_mul]; ring_nf
-- Prove that $f$ is decreasing on $(0,2)$ by applying log_lt_log
  apply log_lt_log; simp; rw [show (4:ℝ)=2^2 by ring, sq_lt, sqrt_sq]
  constructor; linarith; linarith; norm_num
  simp; rw [sq_lt, sqrt_sq]; constructor; linarith; assumption
  linarith; linarith; linarith; linarith; linarith