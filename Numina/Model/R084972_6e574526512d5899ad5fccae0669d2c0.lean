import Mathlib

theorem number_theory_224945 (a : ℕ → ℕ → ℕ) (ha : ∀ n, a n 0 = n) (h : ∀ n k, a n (k + 1) = a n k + 1) :
    ∃ k, a (10^100) k > 10^100 := by
  have h1 : ∀ n k, a n k = n + k := by
    intro n k
    induction k with
    | zero =>
      simp [ha]
    | succ k ih =>
      calc
        a n (k + 1) = a n k + 1 := h n k
        _ = (n + k) + 1 := by rw [ih]
        _ = n + (k + 1) := by ring
  use 1
  have h2 : a (10^100) 1 = 10^100 + 1 := by 
    apply h1
  linarith [h2]