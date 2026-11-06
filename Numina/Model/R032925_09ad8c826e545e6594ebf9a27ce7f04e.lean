import Mathlib

theorem algebra_137876 {a : ℕ → ℝ} (ha0 : a 0 = 1)
    (han : ∀ n, a (n + 1) = (1 + 4 * a n + Real.sqrt (1 + 24 * a n)) / 16) :
    ∀ n, a n = (1 + 1 / 2 ^ n) / 3 * (1 + 1 / 2 ^ (n + 1)) := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    rw [ha0]
    norm_num
  | succ n => 
    -- We need to prove it for n+1
    have h1 : a n = (1 + 1 / 2 ^ n) / 3 * (1 + 1 / 2 ^ (n + 1)) := ih n (by omega)
    -- Use the recurrence relation to find a_{n+1}
    have eq1 : a (n + 1) = (1 + 4 * a n + Real.sqrt (1 + 24 * a n)) / 16 := han n
    rw [eq1, h1]
    have h2 : 1 + 24 * ((1 + 1 / 2 ^ n) / 3 * (1 + 1 / 2 ^ (n + 1))) = (3 + 2 / (2 : ℝ) ^ n) ^ 2 := by
      field_simp
      ring_nf
    have h3 : Real.sqrt ((1 + 24 * ((1 + 1 / 2 ^ n) / 3 * (1 + 1 / 2 ^ (n + 1))) : ℝ)) = (3 + 2 / (2 : ℝ) ^ n) := by
      rw [h2]
      have h4 : (0 : ℝ) ≤ (3 + 2 / (2 : ℝ) ^ n : ℝ) := by
        positivity
      rw [Real.sqrt_sq (show 0 ≤ (3 + 2 / (2 : ℝ) ^ n : ℝ) by linarith)]
    rw [h3]
    field_simp
    ring_nf
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> tauto