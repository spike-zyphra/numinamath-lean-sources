import Mathlib

theorem algebra_20173 {k : ℝ → ℝ} (hk : k = fun x => (6 * x + 12) * (x - 8)) :
    IsLeast (Set.range k) (-150) := by
  constructor
  · -- First, show that -150 is in the range of k
    use 3
    rw [hk]
    norm_num
  · -- Now, show that -150 is the least such value
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hk] at hx
    simp at hx
    have h1 : (6 * x + 12) * (x - 8) ≥ -150 := by
      nlinarith [sq_nonneg (x - 3)]
    linarith