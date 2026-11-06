import Mathlib

theorem number_theory_6037 {P : ℕ → Prop} (hP : ∀ n, 0 < n → P n → P (n + 1)) (hP1 : P 1) : ∀ n, 0 < n → P n := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      exact hP1
    | succ n =>
      have h1 : 0 < n + 1 := by linarith
      have h2 : P (n + 1) := ih h1
      have h3 : P ((n + 1) + 1) := hP (n + 1) (by linarith) h2
      exact h3