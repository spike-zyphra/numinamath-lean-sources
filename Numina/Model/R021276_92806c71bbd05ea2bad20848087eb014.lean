import Mathlib

theorem number_theory_106714 (n : ℕ) :
    (n + 1) ∣ (n ^ 2 + 1) ↔ n = 0 ∨ n = 1 := by
  constructor
  · -- Assume (n + 1) divides (n^2 + 1), prove n = 0 ∨ n = 1
    intro h
    have h3 : (n + 1) ∣ (2 : ℕ) := by
      have h4 : (n + 1) ∣ (n ^ 2 + 1) := h
      have h5 : (n + 1) ∣ (n + 1) * (n + 1) := by
        apply dvd_mul_right
      -- From $n+1 | n^2 +1$ and $n+1 | (n+1)^2$, we get $n+1 | (n+1)^2 - (n^2+1)$ which is $2n$
      have h6 : (n + 1) ∣ ((n + 1) * (n + 1) - (n ^ 2 + 1)) := by
        apply Nat.dvd_sub'
        · exact h5
        · exact h4
      -- Simplify the expression to $2n$
      have h6' : (n + 1) * (n + 1) - (n ^ 2 + 1) = 2 * n := by
        cases n with
        | zero =>
          omega
        | succ n =>
          simp [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
          <;> ring_nf
          <;> omega
      rw [h6'] at h6
      -- Now we have $n+1$ divides $2n$
      -- So $n+1 | 2(n+1)$
      have h8 : (n + 1) ∣ (2 * n) := h6
      have h9 : (n + 1) ∣ (2 * (n + 1) ) := by
        use 2
        all_goals ring
      -- Subtract: $n+1 | 2(n+1) - 2n$ means $n+1$ divides $2$
      have h10 : (n + 1) ∣ (2 * (n + 1) - 2 * n) := by
        apply Nat.dvd_sub'
        · exact h9
        · exact h8
      -- Simplify the expression to 2
      have h11 : 2 * (n + 1) - 2 * n = 2 := by
        cases n with
        | zero =>
          omega
        | succ n =>
          omega
      rw [h11] at h10
      exact h10
    -- Now we have that $n+1$ divides $2$
    -- So $n+1$ must be 1 or 2
    have h5 : (n + 1) ≤ 2 := by
      exact Nat.le_of_dvd (by norm_num) h3
    have h6 : n ≤ 1 := by
      omega
    -- Now prove $n = 0$ or $n = 1$
    interval_cases n <;> try { tauto }
  · -- Assume n = 0 ∨ n = 1, prove (n + 1) ∣ (n ^ 2 + 1)
    rintro (h | h)
    · -- n = 0
      rw [h]
      all_goals norm_num
    · -- n = 1
      rw [h]
      all_goals norm_num