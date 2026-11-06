import Mathlib

theorem number_theory_165604 (a : ℕ → ℕ)
    (ha : ∀ n, a n = if n % 2 = 0 then a (n - 1) + 1 else a (n - 1) + 2) :
    Set.ncard {n | Odd (a n)} = 49 := by
  have h0 := ha 0
  simp at h0
  all_goals omega