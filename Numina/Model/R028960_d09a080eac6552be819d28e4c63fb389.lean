import Mathlib

theorem algebra_113957 {a : ℕ → ℝ}
    (ha01 : a 0 = 0 ∧ a 1 = 0)
    (han : ∀ n, a (n + 2) = 6 * a (n + 1) - 9 * a n + 2 ^ n + n) :
    ∀ n, a n = (n + 1) / 4 + 2 ^ n + (-5 / 4 + 5 / 12 * n) * 3 ^ n := by
  rcases ha01 with ⟨ha0, ha1⟩
  intro n
  have h1 : ∀ (n : ℕ), a n = (n + 1) / 4 + 2 ^ n + (-5 / 4 + 5 / 12 * n) * 3 ^ n := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      rw [ha0]
      norm_num
    | succ n =>
      cases n with
      | zero =>
        rw [ha1]
        norm_num
      | succ n =>
        have h1 := ih (n) (by linarith)
        have h2 := ih (n + 1) (by linarith)
        have eq1 : a (n + 2) = 6 * a (n + 1) - 9 * a n + 2 ^ n + n := by
          specialize han n
          simpa using han
        rw [eq1]
        rw [h1, h2]
        simp [pow_two, pow_succ]
        ring_nf
  specialize h1 n
  simpa using h1