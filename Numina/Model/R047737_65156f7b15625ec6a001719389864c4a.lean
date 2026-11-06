import Mathlib

theorem algebra_294137 (a : ℕ → ℕ) (ha : ∀ n, a n > 0)
    (h : ∀ n, a (n + 1) = (a n + a (n + 2)) / 2 ∨ a (n + 1) = √(a n * a (n + 2))) :
    ∃ N, ∀ n, N ≤ n → a n = (a (n - 1) + a (n + 1)) / 2 ∨
    a n = √(a (n - 1) * a (n + 1)) := by
  use 1
  intro n hn
  have h1 := h (n - 1)
  have eq1 : a (n - 1 + 1) = a n := by
    have h2 : n ≥ 1 := by omega
    have h3 : n - 1 + 1 = n := by omega
    rw [h3]
  have eq2 : a (n - 1 + 2) = a (n + 1) := by
    have h4 : n ≥ 1 := by omega
    have h5 : n - 1 + 2 = n + 1 := by omega
    rw [h5]
  rcases h1 with (h1 | h1)
  · -- Case where the arithmetic mean holds
    left
    have h2 : a (n - 1 + 1) = (a (n - 1) + a (n - 1 + 2)) / 2 := by
      tauto
    rw [eq1] at h2
    rw [eq2] at h2
    omega
  · -- Case where the geometric mean holds
    right
    have h3 : a (n - 1 + 1) = √(a (n - 1) * a (n - 1 + 2)) := by
      tauto
    rw [eq1] at h3
    rw [eq2] at h3
    all_goals try { tauto }
    all_goals try { omega }