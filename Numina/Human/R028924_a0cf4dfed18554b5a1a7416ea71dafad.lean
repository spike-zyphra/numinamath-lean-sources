import Mathlib

/- The sequence $a_0,a_1,a_2,\cdots$ is a strictly increasing arithmetic sequence of positive integers such that
$$
2^{a_7}=2^{27} \cdot a_7.
$$
 What is the minimum possible value of $a_2$?
$\textbf{(A)}\ 8 \qquad \textbf{(B)}\ 12 \qquad \textbf{(C)}\ 16 \qquad \textbf{(D)}\ 17 \qquad \textbf{(E)}\ 22$ -/
-- theorem algebra_95524 (a : ℕ → ℕ) (h₀ : ∃ d, 0 < d ∧ ∀ n, a n = a 0 + d * n)
--     (h₁ : 0 < a 0) (h₂ : 2 ^ a 7 = 2 ^ 27 * a 7) :
--     a 2 ≥ 12 := by sorry

theorem algebra_95524 :
    IsLeast { a₂ |
        ∃ a : ℕ → ℕ, a₂ = a 2 ∧ ∃ d, 0 < d ∧ (∀ n, a n = a 0 + d * n)
          ∧ 0 < a 0 ∧ 2 ^ a 7 = 2 ^ 27 * a 7 } 12 := by
  -- To see that a_2 = 12 is the minimum possible value, we show that it satisfies the relation
  -- given by giving such an arithmetic sequence, and then showing that a_2 ≥ 12.
  rw [IsLeast]
  constructor
  · -- To show that a_2 = 12 is satisfiable, we note that a_n = 4 + 4n works.
    rw [Set.mem_setOf]
    use fun n ↦ 4 + 4 * n, rfl, 4
    simp
  · rw [mem_lowerBounds]
    intro x hx
    rw [Set.mem_setOf] at hx
    obtain ⟨a, rfl, d, hd_pos, ha_eq, ha₀_pos, ha₇⟩ := hx
    have (n : ℕ) : 1 ≤ a n := by
      rw [ha_eq]
      omega
    -- To show that a_2 ≥ 12, we first notice that a_7 = 32
    -- This is because a_7 = 2^(a_7 - 32) is a power of two, and when a_7 > 32 meaning a_7 ≥ 64,
    -- The exponential term grows quicker than the linear term
    have ha₇' : a 7 = 32 := by
      have h₁ : 2 ^ 27 ≤ 2 ^ a 7 := by
        simp [ha₇, this]
      rw [Nat.pow_le_pow_iff_right one_lt_two] at h₁
      have h₂ : a 7 * 2 ^ 27 = 2 ^ (a 7 - 27 + 27) := by
        rw [mul_comm, ← ha₇, Nat.sub_add_cancel h₁]
      have : a 7 = 2 ^ (a 7 - 27) := by
        simp [pow_add] at h₂
        exact h₂
      obtain ⟨b, hb⟩ : ∃ b, a 7 = 2 ^ b := ⟨_, this⟩
      have hb5 : 5 ≤ b := by
        by_contra!
        replace this : b ≤ 4 := Nat.le_of_lt_succ this
        have : a 7 ≤ 2 ^ 4 := by rw [hb]; gcongr; decide
        omega
      have hb_aux (b : ℕ) (hb : 6 ≤ b) : 2 ^ b < 2 ^ (2 ^ b - 27) := by
        induction' b, hb using Nat.le_induction with b hb ih
        · decide
        · have := Nat.pow_le_pow_right zero_lt_two hb
          calc
            2 ^ (b + 1) = 2 ^ b * 2 := by rw [pow_add, pow_one]
            _ < 2 ^ (2 ^ b - 27) * 2 := by gcongr
            _ = 2 ^ (2 ^ b - 27 + 1) := by omega
            _ = 2 ^ (2 ^ b - 26) := by
              congr
              omega
            _ < _ := by
              apply Nat.pow_lt_pow_right (by decide)
              omega
      have : ¬(6 ≤ b) := by
        intro hb6
        specialize hb_aux b hb6
        rw [← hb] at hb_aux
        omega
      rw [hb, ← eq_of_le_of_not_lt hb5 this]
      decide

    -- Now that a_7 = a_0 + 7d = 32, we see that d ≤ 4
    -- Then it suffices to check that for all d = 0, ..., 4, we have 12 ≤ a_2.
    rw [ha_eq] at ha₇' ⊢
    have : d ≤ 4 := by linarith
    interval_cases d <;> omega