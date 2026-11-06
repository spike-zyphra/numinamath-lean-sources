import Mathlib

theorem algebra_304605 {n : ℕ} (hn : n > 0) (h : (n * 50 + 114) / (n + 1) = 51 ∧ (n * 114 + 50) / (n + 1) = 111) :
    n = 15 := by
  rcases h with ⟨h1, h2⟩
  have h3 : n ≤ 63 := by
    by_contra h4
    push_neg at h4
    have h41 : (n * 50 + 114) / (n + 1) < 51 := by
      have h5 : n + 1 > 0 := by
        omega
      have h6 : n * 50 + 114 < 51 * (n + 1) := by
        omega
      have h7 : (n * 50 + 114) / (n + 1) < 51 := by
        apply Nat.div_lt_of_lt_mul
        linarith
      linarith
    omega
  interval_cases n <;> norm_num at h1 h2 ⊢ <;> all_goals omega