import Mathlib

theorem algebra_194523 {n : ℕ} (hn : n > 0) (h : (482100 * n + 451500) / (n + 1) = 519500 ∧ (482100 * n + 451500) / (n + 2) = 517700) :
    n = 17 := by
  rcases h with ⟨h1, h2⟩
  by_contra h3
  push_neg at h3
  have h3 : n ≤ 1 := by
    by_contra h3
    push_neg at h3
    have h4 : n + 1 ≥ 3 := by
      omega
    have h5 : (482100 * n + 451500) / (n + 1) < 519500 := by
      have h6 : 482100 * n + 451500 < 519500 * (n + 1) := by
        nlinarith [show n ≥ 2 by omega]
      have h7 : (482100 * n + 451500) / (n + 1) < 519500 := by
        apply Nat.div_lt_of_lt_mul
        linarith
      linarith
    omega
  interval_cases n <;> omega