import Mathlib

noncomputable def x (n : ℕ) : ℤ := match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => 4 * x (n + 1) - x n

noncomputable def y (n : ℕ) : ℤ := match n with
  | 0 => 1
  | 1 => 2
  | n + 2 => 4 * y (n + 1) - y n

theorem algebra_297011 {n : ℕ} : (y n)^2 = 3 * (x n)^2 + 1 := by
  let P (n : ℕ) := (y n) ^ 2 = 3 * (x n) ^ 2 + 1 ∧ (y (n + 1)) * (y n) = 2 + 3 * (x (n + 1)) * (x n)
  have h1 : ∀ (n : ℕ), P n := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [P, y, x]
    | succ n =>
      cases n with
      | zero =>
        simp [P, y, x]
      | succ n =>
        have h3 := (ih n (by linarith)).1
        have h4 := (ih n (by linarith)).2
        have h5 := (ih (n + 1) (by linarith)).1
        have h6 := (ih (n + 1) (by linarith)).2
        simp [P, y, x] at h3 h4 h5 h6 ⊢
        constructor
        · -- First part: proving the main theorem
          nlinarith [h3, h4, h5, h6]
        · -- Second part: proving the lemma
          nlinarith [h3, h4, h5, h6]
  have h2 : (y n) ^ 2 = 3 * (x n) ^ 2 + 1 := (h1 n).1
  exact h2