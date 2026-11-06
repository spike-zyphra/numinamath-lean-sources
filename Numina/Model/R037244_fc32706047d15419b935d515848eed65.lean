import Mathlib

theorem algebra_319938 {α β : ℝ} (hα : α^2 - 4 * α + 1 = 0) (hβ : β^2 - 4 * β + 1 = 0)
    (hαβ : α ≠ β) (n : ℕ) :
    ∃ m : ℤ, α ^ n + β ^ n = m := by
  have h1 : α + β = 4 := by
    have h2 : α^2 - β^2 = 4 * (α - β) := by linarith
    have h3 : α^2 - β^2 = (α - β) * (α + β) := by ring
    rw [h3] at h2
    have h4 : α - β ≠ 0 := by
      intro h
      apply hαβ
      linarith
    have h5 : α + β = 4 := by
      apply (mul_right_inj' h4).mp
      linarith
    exact h5

  have h2 : α * β = 1 := by
    nlinarith [sq_pos_of_ne_zero (show α - β ≠ 0 by
      intro h
      apply hαβ
      linarith
    ), sq_nonneg (α - β), sq_nonneg (α + β - 4)]

  have h3 : ∀ n : ℕ, ∃ m : ℤ, α ^ n + β ^ n = m := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      use 2
      norm_num
    | succ n =>
      cases n with
      | zero =>
        use 4
        norm_num [h1]
      | succ n =>
        have h4 := ih (n) (by linarith)
        have h5 := ih (n + 1) (by linarith)
        rcases h4 with ⟨m1, hm1⟩
        rcases h5 with ⟨m2, hm2⟩
        have eq1 : α ^ (n + 2) + β ^ (n + 2) = 4 * (α ^ (n + 1) + β ^ (n + 1)) - (α ^ n + β ^ n) := by
          have h6 : α ^ (n + 2) = 4 * α ^ (n + 1) - α ^ n := by
            have h7 : α^2 = 4 * α - 1 := by linarith
            calc
              α ^ (n + 2) = α ^ n * α ^ 2 := by ring
              _ = α ^ n * (4 * α - 1) := by rw [h7]
              _ = 4 * α ^ (n + 1) - α ^ n := by ring
          have h7 : β ^ (n + 2) = 4 * β ^ (n + 1) - β ^ n := by
            have h8 : β^2 = 4 * β - 1 := by linarith
            calc
              β ^ (n + 2) = β ^ n * β ^ 2 := by ring
              _ = β ^ n * (4 * β - 1) := by rw [h8]
              _ = 4 * β ^ (n + 1) - β ^ n := by ring
          calc
            α ^ (n + 2) + β ^ (n + 2) = (4 * α ^ (n + 1) - α ^ n) + (4 * β ^ (n + 1) - β ^ n) := by
              rw [h6, h7]
            _ = 4 * (α ^ (n + 1) + β ^ (n + 1)) - (α ^ n + β ^ n) := by
              ring
        use 4 * m2 - m1
        rw [eq1]
        rw [hm1, hm2]
        <;> norm_num
  specialize h3 n
  exact h3