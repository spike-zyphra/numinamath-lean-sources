import Mathlib

def a : ℕ → ℤ
| 0 => 1
| 1 => 3
| n + 2 => 3 * a (n + 1) - a n

theorem algebra_113608 {n : ℕ} :
    IsSquare (1 + a n * a (n + 2)) ∧
    (∃ m : ℤ, ∏ k ∈ Finset.Icc 2 2020, ⌊(a (k + 1))^2 / a k⌋ * ((a (k + 1))^2 / a k) = m) := by
  constructor
  · -- Show that $1 + a_n a_{n+2}$ is a perfect square
    have h1 : ∀ n : ℕ, 1 + a n * a (n + 2) = (a (n + 1)) ^ 2 := by
      intro n
      induction' n using Nat.strongRecOn with n ih
      cases n with
      | zero =>
        simp [a] at *
        <;> norm_num
      | succ n =>
        cases n with
        | zero =>
          simp [a] at *
          <;> norm_num
        | succ n =>
          have h2 := ih (n) (by linarith)
          simp [a] at h2 ⊢
          nlinarith
    have h2 : ∀ n : ℕ, 1 + a n * a (n + 2) = (a (n + 1)) ^ 2 := h1
    have h3 : IsSquare (1 + a n * a (n + 2)) := by
      rw [h2 n]
      exact ⟨a (n + 1), by ring⟩
    exact h3
  · -- Show that the product is an integer
    refine' ⟨∏ k ∈ Finset.Icc 2 2020, ⌊(a (k + 1))^2 / a k⌋ * ((a (k + 1))^2 / a k), rfl⟩