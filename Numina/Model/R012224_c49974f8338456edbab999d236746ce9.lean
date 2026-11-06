import Mathlib


open BigOperators Complex Filter Finset Real TopologicalSpace Topology

theorem number_theory_91314 (n : ℕ) (hn : 3 ≤ n) :
∃ x y : ℤ, 0 < x ∧ 0 < y ∧ 2^n = 7 * x^2 + y^2 := by
  have h1 : n ≥ 3 := by linarith
  by_cases h : (n : ℕ) % 2 = 1
  · -- If n is odd, then n % 2 = 1.
    have h2 : ∃ k : ℕ, n = 2 * k + 1 := by
      have : n % 2 = 1 := by omega
      have h3 : n ≥ 3 := by omega
      have : ∃ k, n = 2 * k + 1 := by
        use (n - 1) / 2
        omega
      assumption
    rcases h2 with ⟨k, hk⟩
    have hk1 : k ≥ 1 := by
      omega
    use (2 : ℤ) ^ (k - 1 : ℕ)
    use (2 : ℤ) ^ (k - 1 : ℕ)
    constructor
    · -- Show x > 0
      have h3 : (2 : ℤ) ^ (k - 1 : ℕ) > 0 := by
        apply pow_pos
        all_goals omega
      linarith
    constructor
    · -- Show y > 0
      have h3 : (2 : ℤ) ^ (k - 1 : ℕ) > 0 := by
        apply pow_pos
        all_goals omega
      linarith
    · -- Show 2^n = 7 * x^2 + y^2
      rw [hk]
      have h4 : k ≥ 1 := by
        omega
      have h5 : (2 : ℤ) ^ (2 * k + 1 : ℕ) = 7 * ((2 : ℤ) ^ (k - 1 : ℕ)) ^ 2 + ((2 : ℤ) ^ (k - 1 : ℕ)) ^ 2 := by
        have h10 : (2 : ℤ) ^ (2 * k + 1 : ℕ) = 8 * ((2 : ℤ) ^ (k - 1 : ℕ)) ^ 2 := by
          have h11 : (2 : ℤ) ^ (2 * k + 1 : ℕ) = (2 : ℤ) ^ (2 * (k - 1) + 3 : ℕ) := by
            have h10 : k ≥ 1 := h4
            cases k with
            | zero =>
              omega
            | succ m =>
              simp [Nat.mul_add, Nat.add_mul, pow_succ, pow_zero, mul_add, mul_assoc]
              all_goals ring_nf
          have h13 : (2 : ℤ) ^ (2 * (k - 1) + 3 : ℕ) = 8 * ((2 : ℤ) ^ (k - 1 : ℕ)) ^ 2 := by
            have h10 : k ≥ 1 := h4
            cases k with
            | zero =>
              omega
            | succ m =>
              simp [Nat.mul_add, Nat.add_mul, pow_succ, pow_zero, mul_add, mul_assoc]
              all_goals ring_nf
          rw [h11, h13]
        have h14 : 7 * ((2 : ℤ) ^ (k - 1 : ℕ)) ^ 2 + ((2 : ℤ) ^ (k - 1 : ℕ)) ^ 2 = 8 * ((2 : ℤ) ^ (k - 1 : ℕ)) ^ 2 := by
          ring
        rw [h14] at *
        linarith [h10]
      linarith [h5]
  · -- If n is even, then n % 2 = 0.
    have h2 : n % 2 = 0 := by omega
    have h2 : ∃ k : ℕ, n = 2 * k + 4 := by
      have h4 : n % 2 = 0 := by omega
      have h5 : n ≥ 4 := by
        by_contra h
        push_neg at h
        have h3 : n < 4 := by omega
        interval_cases n <;> omega
      have h6 : ∃ k, n = 2 * k + 4 := by
        use (n - 4) / 2
        omega
      assumption
    rcases h2 with ⟨k, hk⟩
    use (2 : ℤ) ^ k
    use (3 : ℤ) * (2 : ℤ) ^ k
    constructor
    · -- Show x > 0
      have h3 : (2 : ℤ) ^ k > 0 := by
        apply pow_pos
        all_goals omega
      linarith
    constructor
    · -- Show y > 0
      have h4 : (2 : ℤ) ^ k > 0 := by
        apply pow_pos
        all_goals omega
      have h5 : (3 : ℤ) * (2 : ℤ) ^ k > 0 := by
        positivity
      linarith
    · -- Show 2^n = 7 * x^2 + y^2
      rw [hk]
      have h6 : (2 : ℤ) ^ (2 * k + 4 : ℕ) = 7 * ((2 : ℤ) ^ k) ^ 2 + ((3 : ℤ) * (2 : ℤ) ^ k) ^ 2 := by
        ring_nf
      linarith [h6]