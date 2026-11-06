import Mathlib

theorem algebra_631543 (n : ℕ) (hn : n > 0) :
    IsSquare (n ^ 4 + 2 * n ^ 3 + 5 * n ^ 2 + 12 * n + 5) → n = 1 ∨ n = 2 := by
  intro h
  -- Define P
  let P := n ^ 4 + 2 * n ^ 3 + 5 * n ^ 2 + 12 * n + 5
  -- h means ∃ k : ℕ, P = k*k
  rcases h with ⟨k, hP⟩
  -- Define A = n^2 + n + 2
  let A := n^2 + n + 2
  -- Show P = A^2 + 8*n + 1
  have h1 : P = A^2 + 8*n + 1 := by
    simp only [P, A]
    ring
  unfold P at h1
  -- Substitute this into P = k*k
  rw [h1] at hP
  -- Since n : ℕ and n > 0, we have n ≥ 1
  have h2 : n ≥ 1 := Nat.one_le_of_lt hn
  -- Thus 8*n + 1 > 0
  have h3 : 8*n + 1 > 0 := by positivity
  -- So k*k = A^2 + 8*n + 1 > A^2
  have h4 : k*k > A^2 := by nlinarith
  rw [pow_two, gt_iff_lt] at h4
  -- Since k, A are ℕ, k*k > A^2 implies k > A. So k ≥ A + 1
  have h5 : k ≥ A + 1 := Nat.succ_le_of_lt (Nat.mul_self_lt_mul_self_iff.mp h4)
  -- Then k*k ≥ (A + 1)^2
  have h6 : k ^ 2 ≥ (A + 1)^2 := Nat.pow_le_pow_of_le_left h5 2
  -- Substitute P for k*k in P ≥ (A+1)^2
  simp [pow_two, ← hP, ← h1, add_pow, add_mul, mul_add] at h6
  -- Now we get 8*n + 1 ≥ 2*A + 1
  have h7 : 8*n + 1 ≥ 2*A + 1 := by nlinarith
  -- From 8*n + 1 ≥ 2*A + 1, we get 8*n ≥ 2*A (Nat.le_of_add_le_add_right)
  have h8 : 8*n ≥ 2*A := Nat.le_of_add_le_add_right h7
  -- Substitute A = n^2+n+2 into 8*n ≥ 2*A
  simp only [A, mul_add, mul_comm 2 n, ←mul_assoc] at h8
  -- For $n \ge 1$ :
  rcases Nat.eq_or_lt_of_le h2 with rfl | hn_ge_2'
  · -- Case n = 1:
    left; rfl
  · -- Case n ≥ 2:
    have h_ident : 2 * n ^ 2 + 4 = 2 * ((n - 1) * (n - 2)) + 6 * n := by
      by_cases hn0 : n = 2
      · simp [hn0]
      · have : n > 2 := by omega
        simp [Nat.mul_sub, Nat.sub_mul, Nat.sub_sub, show n + (n * 2 - 2) = 3 * n - 2 by omega,
          ← mul_assoc]
        rw [show 2 * n * n - (6 * n - 4) + 6 * n =  6 * n + (2 * n * n - (6 * n - 4)) by omega,
          ← Nat.add_sub_assoc (by nlinarith), Nat.add_sub_sub_cancel (by omega), pow_two, ← mul_assoc]
    -- Since $2 \ne 0$, we must have $(n-1)*(n-2) = 0$.
    have h9 : (n-1)*(n-2) = 0 := by nlinarith
    -- $(n-1)*(n-2) = 0$ implies $n-1=0$ or $n-2=0$.
    rcases Nat.mul_eq_zero.mp h9 with h9 | h9
    · -- Case n-1 = 0: Then n = 1.
      left
      omega
    · -- Case n-2 = 0: Then n = 2.
      right
      exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp h9) hn_ge_2'