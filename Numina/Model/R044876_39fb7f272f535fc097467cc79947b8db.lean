import Mathlib

theorem number_theory_115457 {F : ℕ → ℕ} (hF : ∀ n, F (n + 2) = F (n + 1) + F n)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    ∀ n, F n = Nat.fib n := by 
  intro n 
  induction' n using Nat.strongRecOn with n ih 
  cases n with
  | zero =>
    simp [hF0]
  | succ n =>
    cases n with
    | zero =>
      simp [hF1, Nat.fib]
    | succ n =>
      have h1 := ih (n) (by linarith)
      have h2 := ih (n + 1) (by linarith)
      simp [hF, h1, h2, Nat.fib_add_two]
      <;> omega