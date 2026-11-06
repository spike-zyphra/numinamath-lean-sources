import Mathlib

theorem number_theory_12552 (a : ℕ → ℕ) (ha : a 1 > 0)
    (h : ∀ n, a (n + 1) = if Even (a n) then a n / 2 else 3 * a n + 1)
    (h' : a 1 + a 2 + a 3 = 29) : a 1 = 5 := by

  have ha2 : a 2 = if Even (a 1) then a 1 / 2 else 3 * a 1 + 1 := by
    specialize h 1
    simpa using h

  have ha3 : a 3 = if Even (a 2) then a 2 / 2 else 3 * a 2 + 1 := by
    specialize h 2
    simpa using h

  have h1 : a 1 ≤ 29 := by
    omega

  have h2 : a 2 ≤ 29 := by
    omega

  have h3 : a 3 ≤ 29 := by
    omega

  interval_cases a 1 <;> norm_num [Nat.even_iff, ha2, ha3] at h' ⊢ <;> omega