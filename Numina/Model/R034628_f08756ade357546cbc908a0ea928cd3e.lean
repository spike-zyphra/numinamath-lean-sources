import Mathlib

theorem algebra_205375 (n m : ℕ) (h₀ : n > 0) (h₁ : m > 0)
    (h₂ : (n * m + 16) = (n - 1) * m + (m + 1)) :
    n = 18 := by
  have h₃ : n ≥ 1 := by omega
  have h₄ : m ≥ 1 := by omega
  have h₇ : (n * m + 16) = (n * m + 1) := by
    have eq1 : (n - 1) * m + (m + 1) = n * m + 1 := by
      cases n with
      | zero => omega -- contradiction with h₀
      | succ n =>
        cases m with
        | zero => omega -- contradiction with h₁
        | succ m =>
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
          <;> ring_nf <;> omega
    linarith [h₂, eq1]
  omega