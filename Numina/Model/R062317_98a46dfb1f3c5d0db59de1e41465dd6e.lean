import Mathlib

theorem algebra_4960 {x : ℝ} (hx : x > 0) (h : x ^ 2 = x + 504) :
    ∀ m : ℕ, 0 < m → ∃ k : ℤ, ⌊x * ⌊m * x⌋⌋ + k = ⌊x * m⌋ + 504 * m := by
  intro m hm
  use (⌊x * m⌋ + 504 * m - ⌊x * ⌊m * x⌋⌋)
  simp
  <;> ring_nf <;> simp
  all_goals
    ring_nf <;> simp
    <;> ring_nf <;> norm_num