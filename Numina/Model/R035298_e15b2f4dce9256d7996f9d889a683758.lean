import Mathlib

theorem other_56413 (f : ℕ → ℕ) (h : ∀ n, f (n + 2) - 2022 * f (n + 1) + 2021 * f n = 0)
    (h' : f (20 ^ 22) = f (22 ^ 20)) (h'' : f 2021 = 2022) :
    f 2022 = 2022 := by
  have eq1 := h 2019
  have eq2 := h 2020
  norm_num at eq1 eq2
  omega