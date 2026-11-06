import Mathlib

/- 16*. Prove that the polynomial \(x^{12}-x^{7}-x^{5}+1\) cannot take negative values for any \(x\). -/
theorem algebra_292410 : ∀ x : ℝ, x^12 - x^7 - x^5 + 1 ≥ 0 := by
  intro x

  -- First, prove that if u >= 1, then u ^ (k + 1) - 1 is nonnegative
  -- for all natural numbers k.
  have g1 {k : ℕ} {u : ℝ} (hu : u ≥ 1) : u ^ (k + 1) - 1 ≥ 0 := by
    induction k with
    | zero => simp; exact hu
    | succ n ih => calc
                     _ = u * (u ^ (n + 1) - 1) + (u - 1) := by ring
                     _ ≥ u * (u ^ (n + 1) - 1) + 0 := by suffices u - 1 ≥ 0 by exact (add_le_add_iff_left _).mpr this
                                                         linarith
                     _ = u * (u ^ (n + 1) - 1) := by rw [add_zero]
                     _ ≥ 0 := by have : u ≥ 0 := by linarith
                                 exact Left.mul_nonneg this ih

  -- Thn, prove that if u <= 1, then u ^ (2 * k + 1) - 1 is nonpositive
  -- for all natural numbers k.
  have g2 {k : ℕ} {u : ℝ} (hu : u ≤ 1) : u ^ (2 * k + 1) - 1 ≤ 0 := by
    -- Divide into two cases: u ≥ -1 and u ≤ -1.
    by_cases h : u ≥ -1
    -- First case is by induction on k
    . induction k with
      | zero => simp; exact hu
      | succ n ih =>  have : u ^ 2 ≤ 1 := by rw [sq_le_one_iff_abs_le_one, abs_le]
                                             exact ⟨ h, hu ⟩
                      calc
                        _ = u ^ 2 * (u ^ (2 * n + 1) - 1) + (u ^ 2 - 1) := by ring
                        _ ≤ u ^ 2 * (u ^ (2 * n + 1) - 1) + 0 := add_le_add_left (tsub_nonpos.mpr this) _
                        _ = u ^ 2 * (u ^ (2 * n + 1) - 1) := by rw [add_zero]
                        _ ≤ 0 := by exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) ih

    -- Second case is by algebra
    . have : -u ≥ 1 := by linarith
      by_cases hk : k ≥ 1
      -- Consider first the case when k >= 1
      . rw [← neg_le_neg_iff]
        rw [← ge_iff_le]
        calc
          _ = -u * u ^ (2 * k) + 1 := by ring
          _ = (-u) * (((-u) ^ 2) ^ k - 1) + ((- u) + 1) := by ring
          _ ≥ (-u) * (((-u) ^ 2) ^ k - 1) + 0 := by suffices -u + 1 ≥ 0 by exact (add_le_add_iff_left _).mpr this
                                                    linarith
          _ ≥ (-u) * (((-u) ^ 2) ^ k - 1) := by rw [add_zero]
          _ ≥ 0 := by have : ∃ m : ℕ, k = m + 1 := by exact Nat.exists_eq_add_of_le' hk
                      rcases this with ⟨ m, hm ⟩
                      rw [hm]
                      have t1 : -u ≥ 0 := by linarith
                      have t2 :((-u) ^ 2) ^ (m + 1) - 1 ≥ 0 := g1 ((one_le_sq_iff t1).mpr this)

                      exact Left.mul_nonneg t1 t2
          _ ≥ -0 := by simp

      -- The case when k = 0 is trivial.
      . simp at hk
        rw [hk]
        simp; exact hu

  -- Divide into two cases: x ≥ 1 and x ≤ 1.
  by_cases h : x ≥ 1
  . calc
      _ = (x ^ 5 - 1) * (x ^ 7 - 1) := by ring
      _ ≥ 0 := by exact mul_nonneg (g1 h) (g1 h)
  . calc
      _ = -(x ^ (2 * 2 + 1)  - 1) * -(x ^ (2 * 3 + 1) - 1) := by ring
      _ ≥ 0 := by have h' : x ≤ 1 := by simp at h; exact le_of_lt h
                  have t1 : -(x ^ (2 * 2 + 1) - 1) ≥ 0 := by rw [← neg_zero, ge_iff_le, neg_le_neg_iff]; exact g2 h'
                  have t2 : -(x ^ (2 * 3 + 1) - 1) ≥ 0 := by rw [← neg_zero, ge_iff_le, neg_le_neg_iff]; exact g2 h'
                  exact Left.mul_nonneg t1 t2
  done