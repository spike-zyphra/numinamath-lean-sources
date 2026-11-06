import Mathlib

theorem number_theory_191949 (a: ℕ→ℕ) (ha0: a 0 = 7) (h: ∀n, a (n+1) = (a n)^7): (a 1000) % 10 = 7 := by
  -- Show that for each natural number n, a(2n) % 10 = 7
  have ha1 : ∀ (n : ℕ), (a (2 * n)) % 10 = 7 := by
    intro n
    induction n with
    | zero =>
      -- Base case, n = 0. Then a (2 * 0) = a 0
      rw [show 2 * 0 = (0:ℕ) by omega]
      rw [ha0]
      all_goals norm_num
    | succ n ih =>
      have h1 : a (2 * (n + 1)) = a (2 * n + 2) := by
        ring_nf
      rw [h1]
      have eq1 : a (2 * n + 2) = (a (2 * n + 1)) ^ 7 := by
        specialize h (2 * n + 1)
        simpa using h
      have eq2 : a (2 * n + 1) = (a (2 * n)) ^ 7 := by
        specialize h (2 * n)
        simpa using h
      rw [eq1, eq2]
      have h2 : (a (2 * n)) % 10 = 7 := ih
      have h3 : ((a (2 * n) ) ^ 7 ) ^ 7 % 10 = 7 := by
        norm_num [Nat.pow_mod, h2]
      exact_mod_cast h3
  have h1000 : (a 1000) % 10 = 7 := by
    have h2000 : (a (2 * 500)) % 10 = 7 := ha1 500
    rw [show 2 * 500 = 1000 by omega] at h2000
    exact_mod_cast h2000
  exact h1000