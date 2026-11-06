import Mathlib

theorem algebra_93859 (a b c d e : ℕ) (ha : 0 < a)
    (hmode: e = d)
    (hmedian: d = c + 2 ∧ b < c ∧ a < b) (hmean: (a + b + c + d + e) + 10 = 5 * c): 11 ≤ d := by
  rcases hmedian with ⟨hd, hb, ha⟩
  omega