import Mathlib

def x (n : ℕ) : ℤ := match n with
| 0 => 0
| 1 => 1
| n + 2 => 4 * x (n + 1) - x n

def y (n : ℕ) : ℤ := match n with
| 0 => 1
| 1 => 2
| n + 2 => 4 * y (n + 1) - y n

theorem algebra_271173 (n : ℕ) :
    (y n)^2 = 3 * (x n)^2 + 1 := by

  have h1 : ∀ (n : ℕ), (y n)^2 = 3 * (x n)^2 + 1 ∧ y n * y (n + 1) = 3 * (x n * x (n + 1)) + 2 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      constructor
      · -- Base case n=0
        norm_num [x, y]
      · -- Base case n=0
        norm_num [x, y]
    | succ n =>
      cases n with
      | zero =>
        constructor
        · -- Base case n=1
          norm_num [x, y]
        · -- Base case n=1
          norm_num [x, y]
      | succ n =>
        have h1 := ih (n) (by linarith)
        have h2 := ih (n + 1) (by linarith)
        rcases h1 with ⟨h3, h4⟩
        rcases h2 with ⟨h41, h42⟩
        constructor
        · -- Show (y (n + 2)) ^ 2 = 3 * (x (n + 2)) ^ 2 + 1
          simp [x, y] at *
          nlinarith 
        · -- Show y (n + 2) * y (n + 3) = 3 * (x (n + 2) * x (n + 3)) + 2
          simp [x, y] at *
          nlinarith
  specialize h1 n
  exact h1.1