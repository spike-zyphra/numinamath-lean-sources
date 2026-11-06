import Mathlib

theorem algebra_277322 {a d : ℤ} (h : d ≠ 0) (n : ℕ) :
    ∃ b c, a + d * (n + 1) = b + c * n := by
  refine ⟨a + d, d, by ring⟩