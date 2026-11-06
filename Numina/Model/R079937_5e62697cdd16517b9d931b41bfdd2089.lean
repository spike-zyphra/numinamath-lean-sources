import Mathlib

theorem algebra_210823 {x : ℕ} (hx : ∃ n, x = n + (n + 1) + (n + 2) + (n + 3)) :
    ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4, (x * (i + 1)) = 282 ↔ x = 47 := by
  cases hx with
  | intro n hn =>
    simp [Finset.sum_range_succ, hn]
    omega