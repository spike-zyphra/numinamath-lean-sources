import Mathlib

theorem algebra_111885 {f : ℝ → ℝ} (hf : ∀ x > 0, f (x / 2015) ≤ Real.logb 2015 x ∧ Real.logb 2015 x ≤ f x - 1) :
    ∀ x > 0, f x = 1 + Real.logb 2015 x := by

  intro x hx
  have h1 := (hf (x * 2015) (by positivity)).1
  have h2 : f x ≤ Real.logb 2015 (x * 2015) := by
    rw [show (x * 2015) / 2015 = x by ring] at h1
    linarith
  have h3 : Real.logb 2015 (x * 2015) = Real.logb 2015 x + 1 := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    norm_num [Real.logb_self_eq_one]
  rw [h3] at h2
  have h4 := (hf x (by positivity)).2
  linarith