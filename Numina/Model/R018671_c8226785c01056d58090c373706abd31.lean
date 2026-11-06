import Mathlib

theorem algebra_2524 {n : ℕ} (hn : n > 0) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Finset.range n, a i = a (i - 1) + 5) (h : ∑ i ∈ Finset.range (n / 2), a i = 390) :
    n = 5 ∧ a 0 = 10 := by
  exfalso
  have h1 := ha 0 (by
    simp at *
    all_goals omega
    )
  simp at h1
  all_goals linarith
  all_goals linarith