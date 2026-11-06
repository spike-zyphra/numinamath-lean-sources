import Mathlib

theorem number_theory_280508 (n : ℕ) (h : n % 2 = 1) (h' : (n + 2) % 2 = 1) (h'' : (n + 4) % 2 = 1)
    (h''' : n * (n + 2) * (n + 4) = 9177) : n + (n + 2) + (n + 4) = 63 := by
  have h1 : n ≤ 20 := by
    by_contra h2
    push_neg at h2
    have h4 : n ≥ 21 := by linarith
    have h5 : n * (n + 2) * (n + 4) ≥ 21 * 23 * 25 := by
      have h6 : n ≥ 21 := h4
      have h7 :  (n + 2) ≥ 23 := by linarith
      have h8 :  (n + 4) ≥ 25 := by linarith
      have h9 : n * (n + 2) * (n + 4) ≥ 21 * 23 * 25 := by
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        all_goals linarith
      linarith
    nlinarith

  interval_cases n <;> omega