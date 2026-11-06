import Mathlib

open Real

theorem algebra_327068 {n : ℕ} (hn : 0 < n) :
    ∑ k in Finset.Icc 1 n, k / (k ^ 4 + k ^ 2 + 1) =
    (∑ k in Finset.Icc 1 n, k) / (n ^ 2 + n + 1) := by

  have h1 : ∀ k : ℕ, k ≥ 1 → k / (k ^ 4 + k ^ 2 + 1) = 0 := by
    intro k hk
    have h2 : k ^ 4 + k ^ 2 + 1 > k := by
      have h3 : k ≥ 1 := by linarith
      have h4 : k ^ 2 ≥ k := by
        nlinarith [sq_nonneg (k : ℕ), sq_nonneg ((k : ℕ) - (1 : ℕ))]
      have h5 : k ^ 4 ≥ k ^ 2 := by
        nlinarith [sq_nonneg (k ^ 2 : ℕ), sq_nonneg ((k ^ 2 : ℕ) - (k : ℕ)), h4]
      have h6 : k ^ 4 + k ^ 2 + 1 > k := by
        have h7 : k ^ 4 + k ^ 2 ≥ k := by
          nlinarith [h4, h5]
        omega
      omega
    simp [h2]

  have h2 : ∑ k in Finset.Icc 1 n, k / (k ^ 4 + k ^ 2 + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have h1' : i ≥ 1 := by
      have h11 : i ∈ Finset.Icc (1 : ℕ) n := by
        simpa using hi
      simp at h11 ⊢
      omega
    specialize h1 i h1'
    simpa using h1

  have h3 : (∑ k in Finset.Icc 1 n, k) / (n ^ 2 + n + 1) = 0 := by
    have h4 : n ^ 2 + n + 1 > (∑ k in Finset.Icc 1 n, k) := by
      have h5 : ∑ k in Finset.Icc 1 n, k = n * (n + 1) / 2 := by
        have h11 : ∀ (n : ℕ), ∑ k in Finset.Icc 1 n, k = n * (n + 1) / 2 := by
          intro n
          induction n with
          | zero =>
            simp
          | succ n ih =>
            rw [Finset.sum_Icc_succ_top (by linarith)]
            rw [ih]
            cases n with
            | zero =>
              all_goals simp
            | succ n =>
              simp [Nat.mul_comm, Nat.add_assoc]
              <;> ring_nf <;> omega
        specialize h11 n
        exact h11
      rw [h5]
      have h6 : n ^ 2 + n + 1 > n * (n + 1) / 2 := by
        by_contra h
        push_neg at h
        have h6 : n ^ 2 + n + 1 ≤ n * (n + 1) / 2 := by omega
        have h7 : 2 * (n ^ 2 + n + 1) ≤ n * (n + 1) := by
          omega
        nlinarith [sq_nonneg ((n : ℕ) : ℝ), sq_nonneg ((n + 1 : ℕ) : ℝ)]
      omega
    simp [h4]

  rw [h2, h3]
  all_goals omega