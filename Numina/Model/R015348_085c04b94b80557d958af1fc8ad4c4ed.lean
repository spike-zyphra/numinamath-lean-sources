import Mathlib

theorem inequalities_270023 {n : ℕ} (hn : n > 4) (h : (n.choose (n-1)) = (n.choose 1) * (n-1).choose 1) :
    n = 51 := by
  have h1 : n.choose (n - 1) = n := by
    have h2 : n ≥ 1 := by linarith
    have h44 : n.choose (n - 1) = n := by
      have h45 : n > 0 := by linarith
      cases n with
      | zero =>
        linarith
      | succ n =>
        cases n with
        | zero =>
          simp [Nat.choose_zero_right]
        | succ n =>
          simp [Nat.choose_succ_right, Nat.choose_succ_left, mul_comm]
          <;> ring_nf <;> omega
    exact h44
  have h47 : n.choose 1 = n := by
    have h2 : n ≥ 1 := by linarith
    have h49 : n.choose 1 = n := by
      simp [Nat.choose_one_right]
    exact h49
  have h50 : (n - 1).choose 1 = n - 1 := by
    have h2 : n - 1 > 0 := by omega
    have h3 : (n - 1).choose 1 = n - 1 := by
      simp [Nat.choose_one_right]
    exact h3
  rw [h1, h47, h50] at h
  have h6 : n = n * (n - 1) := by
    nlinarith
  have h7 : n * (n - 1) = n := by
    nlinarith
  have h8 : n ≤ 2 := by
    by_contra h9
    push_neg at h9
    have h10 : n * (n - 1) > n := by
      have h11 : n > 2 := by
        omega
      have h12 : n - 1 > 1 := by
        omega
      have h13 : n > 0 := by
        linarith
      have h14 : n * (n - 1) > n * 1 := by
        apply Nat.mul_lt_mul_of_pos_left
        linarith
        linarith
      have h15 : n * 1 = n := by
        ring
      linarith [h14, h15]
    nlinarith
  omega