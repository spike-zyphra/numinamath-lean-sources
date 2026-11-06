import Mathlib

open Real

theorem algebra_290914 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = (a n)^2) :
    ∃ r, ∀ n ≥ 1, log (a n) = log (a 1) * r^(n - 1) := by
  use 2
  intro n hn
  have h1 : ∀ (n : ℕ), n ≥ 1 → log (a n) = log (a 1) * (2 : ℝ) ^ (n - 1) := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        simp [ha1]
      | succ n =>
        have h2 : n + 1 ≥ 1 := by linarith
        have ih' : log (a (n + 1)) = log (a 1) * (2 : ℝ) ^ ((n + 1) - 1) := ih (by linarith)
        have h3 : a (n + 1 + 1) = (a (n + 1)) ^ 2 := by
          specialize han (n + 1) (by linarith)
          simpa using han
        have h4 : log (a (n + 1 + 1)) = 2 * log (a (n + 1)) := by
          rw [h3]
          have h5 : log ((a (n + 1)) ^ 2) = 2 * log (a (n + 1)) := by
            simp [log_pow]
            <;> ring
          linarith [h5]
        rw [h4]
        rw [ih']
        cases n with
        | zero =>
          simp [ha1]
          <;> ring
        | succ n =>
          simp [ha1] at *
          <;> ring
  specialize h1 n hn
  simpa using h1