import Mathlib

theorem number_theory_29891 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : ∃ k : ℤ, (x ^ 2 - 1) / (y + 1) + (y ^ 2 - 1) / (x + 1) = k) :
    ∃ m1 m2 : ℤ, (x ^ 2 - 1) / (y + 1) = m1 ∧ (y ^ 2 - 1) / (x + 1) = m2 := by
  rcases h with ⟨k, hk⟩
  refine ⟨(x ^ 2 - 1) / (y + 1), (y ^ 2 - 1) / (x + 1), rfl, rfl⟩