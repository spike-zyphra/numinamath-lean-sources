import Mathlib

def v : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 8 * v (n + 1) - v n

theorem number_theory_197376 :
    ∀ N, ∃ n, n > N ∧ 15 ∣ v n := by
  intro N
  use 15 * (N + 1)
  constructor
  · -- 15 * (N + 1) > N
    nlinarith
  · -- 15 ∣ v (15 * (N + 1))
    have h1 : ∀ n : ℕ, 15 ∣ v (15 * n) := by
      intro n
      induction n with
      | zero =>
        simp [v]
      | succ n ih =>
        have h2 : v (15 * (n + 1)) = v (15 * n + 15) := by
          ring_nf
        rw [h2]
        norm_num [v] at ih ⊢
        <;> omega
    specialize h1 (N + 1)
    simpa using h1