import Mathlib

theorem number_theory_110685 : {n : ℕ | n > 0 ∧ 40 * n = (∑ i in Finset.range n, i)} = {81} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n is in the set
    intro h
    rcases h with ⟨hn_pos, h_eq⟩
    have h1 : n > 0 := hn_pos
    have eq1 : 40 * n = (∑ i in Finset.range n, i) := by
      exact h_eq
    have eq2 : n = 81 := by
      have eq3 : ∀ n : ℕ, ∑ i in Finset.range n, i = n * (n - 1) / 2 := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          cases n with
          | zero =>
            all_goals simp
          | succ n =>
            simp [Nat.add_assoc, mul_add, Nat.mul_comm, Nat.mul_assoc, Nat.add_mul, Nat.mul_add]
            <;> ring_nf
            <;> omega
      -- Use the formula for the sum of a range
      have eq4 : (∑ i in Finset.range n, i) = n * (n - 1) / 2 := by
        apply eq3
      rw [eq4] at eq1
      have h4 : n ≤ 81 := by
        by_contra h
        push_neg at h
        have h5 : n ≥ 82 := by omega
        have eq6 : n * (n - 1) / 2 > 40 * n := by
          have h6 : n ≥ 82 := h5
          have eq7 : n * (n - 1) ≥ 80 * n + (n - 1) := by
            cases n with
            | zero =>
              all_goals omega
            | succ n =>
              cases n with
              | zero =>
                all_goals omega
              | succ n =>
                simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_assoc, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.mul_zero]
                nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((n + 1 : ℕ)), sq_nonneg ((n + 2 : ℕ))]
          have h8 : n * (n - 1) / 2 > 40 * n := by
            omega
          omega
        omega
      interval_cases n <;> try omega
    linarith
  · -- Assume n = 81
    intro h
    rw [h]
    constructor
    · norm_num
    · native_decide