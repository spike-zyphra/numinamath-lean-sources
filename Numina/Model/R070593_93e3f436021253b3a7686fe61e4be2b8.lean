import Mathlib

theorem algebra_306324 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2) (ha2 : a 2 = 1 / 3)
    (han : ∀ n > 0, a (n + 2) = 2 * (n + 2) * a (n + 1) - (n + 2) * (n + 1) * a n +
      (n ^ 2 + 3 * n + 1) / (n + 3)) :
    ∀ n > 0, a n = 1 / (n + 1) := by
  intro n hn
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero => 
    linarith -- zero is excluded by hn
  | succ n => 
    cases n with
    | zero => 
      rw [ha1]
      norm_num
    | succ n => 
      cases n with
      | zero => 
        rw [ha2]
        norm_num
      | succ n => 
        have eq2 : a (n + 3) = 2 * (n + 1 + 2) * a (n + 1 + 1) - (n + 1 + 2) * (n + 1 + 1) * a (n + 1) + ( (n + 1) ^ 2 + 3 * (n + 1) + 1 ) / ( (n + 1) + 3 ) := by 
          specialize han (n + 1) (by linarith)
          simpa using han
        have h1 := ih (n + 2) (by linarith)
        have h2 := ih (n + 1) (by linarith)
        simp [show n + 2 ≥ 0 by linarith] at h1
        simp [show n + 1 ≥ 0 by linarith] at h2
        rw [eq2]
        rw [h1]
        rw [h2]
        field_simp at *
        ring_nf
        <;> field_simp
        <;> ring_nf
        <;> norm_num
        <;> ring_nf
        all_goals
          norm_num
          all_goals nlinarith