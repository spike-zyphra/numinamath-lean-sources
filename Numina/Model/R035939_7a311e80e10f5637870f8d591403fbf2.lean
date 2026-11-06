import Mathlib

theorem number_theory_235030 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : (2 : ℤ) * p ^ 3 - q ^ 2 = 2 * (p + q) ^ 2) : (p, q) = (3, 2) := by
  have h1 : (2 : ℤ) * p ^ 3 = q ^ 2 + 2 * (p + q) ^ 2 := by
    linarith

  by_cases hq2 : q % 2 = 1
  · -- Assume q is odd
    have h2 : q % 2 = 1 := hq2
    have h3 : (q : ℤ) % 2 = 1 := by
      omega
    have h4 : ((q : ℤ) ^ 2) % 2 = 1 := by
      simp [pow_two, Int.mul_emod, h3]
    have h5 : ((q ^ 2 + 2 * (p + q) ^ 2) : ℤ) % 2 = 1 := by
      omega
    have h6 : ((2 : ℤ) * p ^ 3) % 2 = 0 := by
      simp [Int.mul_emod]
    omega
  · -- q is even
    have h2 : q % 2 = 0 := by
      omega
    have h3 : q = 2 := by
      by_cases h4 : q > 2
      · -- If q > 2, then q must be odd, but q is even
        have h5 : q % 2 = 0 := h2
        have h7 : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by linarith) (by linarith)
        tauto
      · -- q ≤ 2
        interval_cases q <;> try tauto
    -- Now we can substitute q = 2 into the equation
    have h8 : (2 : ℤ) * p ^ 3 = (4 : ℤ) + 2 * (p + 2) ^ 2 := by
      rw [show (q : ℤ) = 2 by exact_mod_cast (show q = 2 by exact h3)] at h1
      linarith
    have h9 : p = 3 := by
      have eq3 : 2 * (p : ℤ) ^ 3 = 4 + 2 * (p + 2) ^ 2 := by
        linarith
      have eq4 : p ≤ 3 := by
        by_contra h10
        push_neg at h10
        have h11 : p > 3 := by linarith
        have h12 : 2 * (p : ℤ) ^ 3 > 4 + 2 * (p + 2) ^ 2 := by
          nlinarith [sq_pos_of_pos (show (p : ℤ) > 0 by nlinarith), sq_nonneg (p - 3 : ℤ), sq_nonneg (p : ℤ)]
        nlinarith
      interval_cases p <;> try { omega }
    -- Now we know p = 3, q = 2.
    simp [h9, h3]