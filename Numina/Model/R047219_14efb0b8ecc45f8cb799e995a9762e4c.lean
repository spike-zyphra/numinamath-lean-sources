import Mathlib

theorem algebra_42466 (f : ℝ → ℝ → ℝ) (hf : ∀ k, f k = fun x => x ^ 2 - k * x + (k - 1) ^ 2) :
    IsGreatest {k | ∃ x, f k x = 0} 2 := by
  constructor
  · -- Show that 2 is in the set
    use 1
    rw [hf 2]
    norm_num
  · -- Show that 2 is greatest in the set
    intro k hk
    rcases hk with ⟨x, hx⟩
    rw [hf k] at hx
    simp at hx
    have h1 : x ^ 2 - k * x + (k - 1) ^ 2 = 0 := by linarith
    have h2 : k ^ 2 - 4 * (k - 1) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (x - k / 2)]
    nlinarith