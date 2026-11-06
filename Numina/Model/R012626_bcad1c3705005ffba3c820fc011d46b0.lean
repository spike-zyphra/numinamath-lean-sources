import Mathlib

theorem algebra_246783 {f : ℕ → ℝ} (hf : ∀ n, f (n + 2) - 2 * f (n + 1) + f n = 1) :
    ∃ a b, ∀ n, f n = (1 / 2) * n ^ 2 + a * n + b := by
  use (f 1 - f 0 - 1 / 2)
  use (f 0)
  intro n
  have h1 (n : ℕ) : f n = (1 / 2) * (↑n : ℝ) ^ 2 + (f 1 - f 0 - 1 / 2) * (↑n : ℝ) + f 0 := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      cases n with
      | zero =>
        simp
      | succ n =>
        cases n with
        | zero =>
          simp
        | succ n =>
          have h1 := ih (n) (by linarith)
          have h2 := ih (n + 1) (by linarith)
          simp [pow_two] at h1 h2 ⊢
          linarith [hf n, h1, h2]
  specialize h1 n
  simpa using h1