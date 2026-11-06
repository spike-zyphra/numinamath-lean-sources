import Mathlib

/- Suppose that $b$ is a positive integer greater than or equal to $2.$ When $197$ is converted to base $b$, the resulting representation has $4$ digits. What is the number of possible values for $b$? -/
theorem number_theory_15512 :
    Set.ncard {b : ℕ | 2 ≤ b ∧ (Nat.digits b 197).length = 4} = 2 := by
  -- We show that the set of possible values for b is {4, 5}
  have H : {b : ℕ | 2 ≤ b ∧ (Nat.digits b 197).length = 4} = {4, 5} := by
    -- We show both inclusions
    ext b
    simp
    constructor
    . -- If b satisfies the conditions, then b = 4 or b = 5
      intro ⟨h1, h2⟩
      -- b.digits 197 = Nat.log b 197
      rw [Nat.digits_len _ _ h1 (by simp)] at h2
      simp at h2
      -- Nat.log b 197 = 3 ↔ b ^ 3 ≤ 197 ∧ 197 < b ^ 4
      rw [Nat.log_eq_iff (by simp)] at h2
      simp at h2

      -- If b = 4 ∨ b = 5 do not hold, then b ≤ 3 ∨ b ≥ 6
      by_contra! h
      replace h : b ≤ 3 ∨ b ≥ 6 := by omega

      rcases h with h | h
      . -- If b ≤ 3, then b ^ 4 ≤ 81 < 197
        apply_fun (· ^ 4 : ℕ → ℕ) at h
        . beta_reduce at h
          linarith only [h2.2, h]
        . exact pow_left_mono 4
      . -- If b ≥ 6, then b ^ 3 ≥ 216 > 197
        apply_fun (· ^ 3 : ℕ → ℕ) at h
        . beta_reduce at h
          linarith only [h2.1, h]
        . exact pow_left_mono 3
    . -- If b = 4 or b = 5, then b satisfies the conditions
      -- It can be directly computed
      rintro (rfl | rfl)
      . simp
      . simp

  -- The set {4, 5} has two elements
  rw [H, Set.ncard_pair (show 4 ≠ 5 by simp)]
