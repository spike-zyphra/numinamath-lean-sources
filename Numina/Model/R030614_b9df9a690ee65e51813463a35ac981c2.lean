import Mathlib

theorem algebra_16178 : IsLeast {M | ∃ a b c d e : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ a + b + c + d + e = 2010 ∧ Finset.max' {a + b, b + c, c + d, d + e} (Finset.insert_nonempty _ _) = M} 671 := by
  constructor
  · use 669, 1, 670, 1, 669
    simp [Finset.max']
  · intro M hM
    rcases hM with ⟨a, b, c, d, e, ha, hb, hc, hd, he, h1, h2⟩
    simp [Finset.max'] at h2
    omega