import Mathlib

def f (n m : ℕ) := if n = 0 then m else f (n - 1) (f (n - 2) m)

theorem number_theory_128609 (a : ℕ → ℕ) (ha : ∀ n, a n = f n (a (n - 1))) (ha0 : a 0 = 1)
    (ha1 : ∀ n, a (n + 1) = a n + a (n - 1)) :
    a 99 = 101 * 2 ^ 98 := by

  have h1 := ha 1
  have h2 := ha1 0
  simp [f] at h1
  simp at h2
  omega