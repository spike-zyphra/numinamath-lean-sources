import Mathlib

theorem algebra_20727 (a : ℕ → ℕ) (ha : a 0 = 25) (h : ∀ n, a (n + 1) = a n + 4) :
    IsLeast {n | a n > 100} 19 := by
  have h1 : ∀ n, a n = 25 + 4 * n := by
    intro n
    induction n with
    | zero =>
      simp [ha]
    | succ n ih =>
      calc
        a (n + 1) = a n + 4 := h n
        _ = (25 + 4 * n) + 4 := by rw [ih]
        _ = 25 + 4 * (n + 1) := by ring_nf
  constructor
  · -- Show 19 is in the set
    simp [h1]
  · -- Show there is no smaller element in the set
    intro n hn
    have h5 : a n > 100 := by
      simpa using hn
    by_contra h7
    push_neg at h7
    interval_cases n <;> norm_num [h1] at h5 <;> omega