import Mathlib

theorem algebra_169972 (t : ℕ) (ht : t > 0) (h : ∑ i ∈ Finset.range t, (50 + 5 * i) = 40 * t + 135) :
    t = 6 := by
  have h3 : ∑ i in Finset.range t, (50 + 5 * i) = (t : ℕ) * (95 + 5 * t) / 2 := by
    have h : ∀ (n : ℕ), ∑ i in Finset.range n, (50 + 5 * i) = (n : ℕ) * (95 + 5 * n) / 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring_nf
        omega
    apply h t

  rw [h3] at h
  have h4 : t ≤ 7 := by
    by_contra h2
    push_neg at h2
    have h7 : t > 7 := by linarith
    have h4 : (t : ℕ) * (95 + 5 * t) = 2 * (40 * t + 135) := by
      have h5 : (t : ℕ) * (95 + 5 * t) % 2 = 0 := by
        have h7 : (t : ℕ) * (95 + 5 * t) % 2 = 0 := by
          have h8 : (t : ℕ) % 2 = 0 ∨ (t : ℕ) % 2 = 1 := by omega
          rcases h8 with (h8 | h8)
          · -- If t is even
            simp [Nat.mul_mod, Nat.add_mod, h8]
          · -- If t is odd
            simp [Nat.mul_mod, Nat.add_mod, h8]
            all_goals omega
        omega
      omega
    exfalso
    nlinarith [h7, sq_nonneg (t : ℕ), sq_nonneg ((t : ℕ) - 6 : ℤ)]
  interval_cases t <;> omega