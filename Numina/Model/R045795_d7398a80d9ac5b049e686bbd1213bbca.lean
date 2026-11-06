import Mathlib

theorem number_theory_233405 {a : ℕ → ℤ}
    (ha : ∀ n, a n = 11^(n + 2) + 12^(2 * n + 1)) :
    ∀ n, 133 ∣ a n := by
  intro n
  have h1 : ∀ n : ℕ, 133 ∣ a n := by
    intro n
    induction n with
    | zero =>
      have h2 : a 0 = 133 := by
        rw [ha 0]
        norm_num
      rw [h2]
      all_goals norm_num
    | succ n ih =>
      have h2 : a (n + 1) = 11 * (a n) + 133 * (12 ^ (2 * n + 1)) := by 
        rw [ha (n + 1)]
        rw [ha n]
        ring_nf
      rw [h2]
      omega
  specialize h1 n
  simpa using h1