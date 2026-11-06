import Mathlib

theorem algebra_324341 {a : ℕ → ℝ} (ha1 : a 1 = 1) (ha2 : a 2 = 1)
    (han : ∀ n > 0, a (n + 2) = 3 * a (n + 1) + 18 * a n + 2 ^ n) :
    ∀ n > 0, a n = 6 ^ n / 12 - (-3) ^ n / 5 - 2 ^ n / 20 := by
  intro n hn
  induction' n using Nat.strongRecOn with n ih
  cases' n with n
  · -- contradiction, n > 0
    linarith
  cases' n with n
  · -- n = 1
    simp [ha1]
    <;> ring_nf
    <;> norm_num
  cases' n with n
  · -- n = 2
    simp [ha2]
    <;> ring_nf
    <;> norm_num
  -- recurrence step
  have h1 := ih (n + 1) (by linarith) (by linarith)
  have h2 := ih (n + 2) (by linarith) (by linarith)
  -- a (n + 3) by recurrence
  have eq3 : a (n + 3) = 3 * a (n + 2) + 18 * a (n + 1) + 2 ^ (n + 1) := by
    specialize han (n + 1) (by linarith)
    simpa using han
  simp [eq3, h1, h2]
  <;> ring_nf
  <;> norm_num
  <;> ring_nf <;> norm_num