import Mathlib

theorem algebra_111763 {f : ℝ → ℝ} (hf : ∀ x, f x ≠ 0)
    (h : ∀ a b, f (a * b) = a * f b + b * f a) :
    f 0 = 0 ∧ f 1 = 1 ∧ Odd f ∧
    (∀ n, ∑ i in Finset.range n, (f (2 ^ (-i : ℝ))) / (i + 1) = (1 / 2) ^ n - 1) := by

  have h0' : f 0 = 0 := by
    specialize h 0 0
    norm_num at h
    simpa using h

  have h0_ne : f 0 ≠ 0 := hf 0

  contradiction