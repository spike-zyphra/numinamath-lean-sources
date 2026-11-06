import Mathlib

theorem algebra_7437 (a : ℕ → ℝ) (ha : a 0 = 100 ∧ a 1 = 90)
    (h : ∀ n, a (n + 2) = (a n + a (n + 1)) / 2) :
    ⌊a 99⌋ = 93 := by
  rcases ha with ⟨ha0, ha1⟩
  norm_num [Int.floor_eq_iff, ha0, ha1, h]
  <;> ring_nf <;> norm_num