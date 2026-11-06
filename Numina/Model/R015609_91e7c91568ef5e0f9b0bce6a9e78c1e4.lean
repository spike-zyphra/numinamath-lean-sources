import Mathlib

theorem inequalities_189965 (x : ℕ) (hx : x > 0) :
    (0.3 : ℝ) ^ (∑ i ∈ Finset.range x, (2 * i + 2)) > 0.3 ^ 72 ↔
    x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by
  constructor
  · -- Assume $0.3^{2+4+6+\ldots+2x} > 0.3^{72}$, prove $x = 1 \lor x = 2 \lor \dots \lor x = 7$
    intro h
    have h1 : ∀ x : ℕ, ∑ i ∈ Finset.range x, (2 * i + 2) = x ^ 2 + x := by
      intro x
      induction x with
      | zero =>
        simp
      | succ x ih =>
        rw [Finset.sum_range_succ, ih]
        ring_nf
    have h2 : ∑ i ∈ Finset.range x, (2 * i + 2) = x ^ 2 + x := h1 x
    have h3 : (0.3 : ℝ) ^ (x ^ 2 + x : ℕ) > (0.3 : ℝ) ^ (72 : ℕ) := by
      rw [h2] at h
      simpa using h
    have h4 : x ≤ 7 := by
      by_contra h'
      push_neg at h'
      have h5 : x ≥ 8 := by
        omega
      have h6 : x ^ 2 + x ≥ 72 := by
        nlinarith [show x ≥ 8 from by omega]
      have h7 : (0.3 : ℝ) ^ (x ^ 2 + x : ℕ) ≤ (0.3 : ℝ) ^ (72 : ℕ) := by
        have h8 : (x ^ 2 + x : ℕ) ≥ (72 : ℕ) := by
          have h9 : x ^ 2 + x ≥ 72 := h6
          omega
        have h9 : (0.3 : ℝ) ^ ((x ^ 2 + x : ℕ) : ℕ) ≤ (0.3 : ℝ) ^ ((72 : ℕ) : ℕ) := by
          have h10 : (0.3 : ℝ) < (1 : ℝ) := by norm_num
          have h11 : (x ^ 2 + x : ℕ) ≥ (72 : ℕ) := h8
          have h12 : (0.3 : ℝ) ^ ((x ^ 2 + x : ℕ) : ℕ) ≤ (0.3 : ℝ) ^ ((72 : ℕ) : ℕ) := by
            apply pow_le_pow_of_le_one
            all_goals
              try norm_num
              try omega
          linarith
        simpa using h9
      linarith
    have h9 : x ≤ 7 := h4
    have h10 : x ≥ 1 := by linarith
    interval_cases x <;> norm_num at h3 ⊢ <;> tauto
  · -- Assume $x = 1 \lor x = 2 \lor \dots \lor x = 7$, prove $0.3^{2+4+6+\ldots+2x} > 0.3^{72}$
    intro h
    have h1 : ∀ x : ℕ, ∑ i ∈ Finset.range x, (2 * i + 2) = x ^ 2 + x := by
      intro x
      induction x with
      | zero =>
        simp
      | succ x ih =>
        rw [Finset.sum_range_succ, ih]
        ring_nf
    have h2 : ∑ i ∈ Finset.range x, (2 * i + 2) = x ^ 2 + x := h1 x
    rw [h2]
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals norm_num