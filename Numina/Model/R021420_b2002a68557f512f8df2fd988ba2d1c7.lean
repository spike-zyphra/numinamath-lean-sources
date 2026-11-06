import Mathlib

def a : ℕ → ℤ
| 0 => 1
| 1 => 1
| n + 2 => 2 * a (n + 1) - a n + 2

theorem algebra_6521 {n} :
    a (n ^ 2 + 1) = a (n + 1) * a n := by
  have h1 : ∀ n, a n = (↑n : ℤ) ^ 2 - (↑n : ℤ) + 1 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [a]
      <;> ring
    | succ n =>
      cases n with
      | zero =>
        simp [a]
        <;> ring
      | succ n =>
        have h2 := ih (n + 1) (by omega)
        have h3 := ih (n) (by omega)
        simp [a, h2, h3]
        <;> ring_nf
        <;> norm_num
        <;> ring
  have h1' : ∀ n, a n = (↑n : ℤ) ^ 2 - (↑n : ℤ) + 1 := h1
  have h10 := h1' (n ^ 2 + 1)
  have h11 := h1' (n + 1)
  have h12 := h1' n
  simp [h10, h11, h12]
  <;> ring_nf
  <;> norm_num
  <;> ring