import Mathlib

theorem algebra_210257 {x : ℕ} (hx : x > 0) (h : 100 * x ^ 2 = 10 * x + 46 * (x - 1)) :
    x = 1 ∨ x = 9 ∨ x = 36 := by
  have h1 : x ≤ 37 := by
    by_contra h2
    push_neg at h2
    have h6 : x ≥ 37 := by
      omega
    have h7 : 100 * x ^ 2 > 10 * x + 46 * (x - 1) := by
      have h8 : x ≥ 37 := by
        omega
      cases x with
      | zero =>
        linarith
      | succ x =>
        cases x with
        | zero =>
          omega
        | succ x =>
          simp [Nat.pow_succ, Nat.mul_add] at h ⊢
          all_goals
            ring_nf at h ⊢
            omega
    omega
  interval_cases x <;> omega