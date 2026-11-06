import Mathlib

/-Find all possible values for f(2018), where f is a function from Q to ℝ+. satisfying the following conditions:
f(2) = 1 / 2
for any rational x, if f(x) ≤ 1, then f(x + 1) ≤ 1
f(xy) = f(x)f(y)-/
theorem algebra_291786 {f : ℚ → ℝ} (hf : ∀ x, 0 < f x)
    (h2 : f 2 = 1 / 2) (hinc : ∀ x, f x ≤ 1 → f (x + 1) ≤ 1)
    (hmul : ∀ x y, f (x * y) = f x * f y): false := by
-- we prove that there's no such function--
-- note that f(0) = f(0) * f(2) = 1/2 * f(0), but f(0) > 0, hence there is a contradiction--
  have h0 : f 0 = 0 := by
    have h := hmul 0 2
    norm_num at h
    nlinarith [hf 0, h2]
  have pos0 : 0 < f 0 := hf 0
  rw [h0] at pos0
  linarith
