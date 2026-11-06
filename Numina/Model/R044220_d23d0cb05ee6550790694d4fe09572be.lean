import Mathlib

theorem algebra_145889 {a b : ℕ} (h : a * b = (a + 2) * (b - 2)) :
    ∃ n, n^2 = a * b + 1 := by 
  by_cases h1 : b < 2
  · -- case b < 2
    have h2 : b = 0 ∨ b = 1 := by
      interval_cases b <;> omega
    rcases h2 with (r | r)
    · -- case b = 0
      have r0 : b = 0 := r
      use 1
      rw [r0]
      all_goals
        ring
    · -- case b = 1
      have r1 : b = 1 := r
      have h4 : a = 0 := by
        rw [r1] at h
        simp at h
        omega
      use 1
      rw [r1, h4]
      all_goals
        ring
  · -- case b ≥ 2
    have eq1 : b ≥ 2 := by omega
    have eq2 : a = b - 2 := by
      cases b with
      | zero =>
        omega
      | succ b =>
        cases b with
        | zero =>
          omega
        | succ b =>
          simp [Nat.mul_add, Nat.mul_sub_left_distrib, mul_add, mul_comm] at h ⊢
          omega
    have h3 : b ≥ 2 := eq1
    use a + 1
    have h6 : b = a + 2 := by
      omega
    rw [h6]
    all_goals
      ring_nf
      <;> omega