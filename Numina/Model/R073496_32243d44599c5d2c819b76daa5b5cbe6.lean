import Mathlib

theorem number_theory_197278 (R S : ℕ) (hR : R ≤ 2003) (hS : S ≤ 2003)
    (h : ∀ i, i + 6 < 2003 → (R + 19 * i) ≤ S) :
    S = 8 := by
  have h1996 := h 1996 (by norm_num)
  omega