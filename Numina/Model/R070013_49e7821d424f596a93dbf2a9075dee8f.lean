import Mathlib

theorem algebra_292738 {l s : ℕ} (hl : l + s = 62) (hs : s * 5 + l * 3 = 62 * 1000 - 15 * 5)
    (h : l * 3 + s * 5 = 62 * 1000 - 15 * 3) :
    l = 27 := by
  omega