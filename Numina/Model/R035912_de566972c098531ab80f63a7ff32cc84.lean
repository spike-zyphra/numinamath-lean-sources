import Mathlib

theorem algebra_129016 (a : ℕ → ℤ) (ha : a 1 > a 0) (ha' : a 1 > 0)
    (h : ∀ r ∈ Finset.Icc 0 98, a (r + 2) = 3 * a (r + 1) - 2 * a r) :
    a 100 > 2 ^ 99 := by
  have h1 : ∀ (n : ℕ), n ≤ 98 → a (n + 2) = 3 * a (n + 1) - 2 * a n := by
    intro n hn
    specialize h n (show n ∈ Finset.Icc 0 98 by simp at *; omega)
    simpa using h
  have h3 : ∀ (n : ℕ), n ≤ 99 → a (n + 1) - a n = 2 ^ n * (a 1 - a 0) := by
    intro n hn
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h4 : n ≤ 99 := by omega
      have h5 : a (n + 2) = 3 * a (n + 1) - 2 * a n := h1 n (by omega)
      have eq1 : a (n + 2) - a (n + 1) = 2 * (a (n + 1) - a n) := by
        linarith
      have eq2 : a (n + 2) - a (n + 1) = 2 ^ (n + 1) * (a 1 - a 0) := by
        have eq3 : a (n + 1) - a n = 2 ^ n * (a 1 - a 0) := ih (by omega)
        rw [eq3] at eq1
        have : a (n + 2) - a (n + 1) = 2 ^ (n + 1) * (a 1 - a 0) := by
          ring_nf at eq1 ⊢
          linarith
        linarith
      simpa using eq2
  have h6 : a 100 = a 0 + (a 1 - a 0) * (2 ^ 100 - 1) := by
    have h8 : ∀ (k : ℕ), k ≤ 100 → a k = a 0 + (a 1 - a 0) * (2 ^ k - 1) := by
      intro k hk
      induction' k using Nat.strongRecOn with k ih
      cases k with
      | zero =>
        simp
      | succ k =>
        cases k with
        | zero =>
          simp
        | succ k =>
          have h12 : a (k + 2) = 3 * a (k + 1) - 2 * a k := h1 k (by omega)
          have h9 : a (k + 1) = a 0 + (a 1 - a 0) * (2 ^ (k + 1) - 1) := by
            apply ih (k + 1)
            all_goals omega
          have h10 : a k = a 0 + (a 1 - a 0) * (2 ^ k - 1) := by
            apply ih k
            all_goals omega
          rw [h12]
          rw [h9, h10]
          cases k with
          | zero =>
            all_goals ring_nf
          | succ k =>
            ring_nf
    specialize h8 100 (by norm_num)
    linarith
  have h7 : a 1 - a 0 ≥ 1 := by omega
  rw [h6]
  nlinarith [show (2 ^ 100 - 1 : ℤ) ≥ 0 by norm_num, show a 1 - a 0 ≥ 1 by omega, show (2 ^ 100 : ℤ) ≥ 0 by norm_num, ha']