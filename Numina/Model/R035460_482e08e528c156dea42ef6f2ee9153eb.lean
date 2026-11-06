import Mathlib

theorem inequalities_58402 : {m : ℝ | ∀ x, m * x ^ 2 - 6 * m * x + 5 * m + 1 > 0} = {m : ℝ | 0 ≤ m ∧ m < 1 / 4} := by
  ext m 
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume that $mx^2 - 6mx + 5m + 1 > 0$ for all real $x$
    intro h
    have h1 : 0 ≤ m := by
      by_contra h1
      push_neg at h1
      have h4 : ∃ x : ℝ, m * x ^ 2 - 6 * m * x + 5 * m + 1 = 0 := by
        have h3 : 16 * m ^ 2 - 4 * m > 0 := by
          nlinarith
        use (6 * m + Real.sqrt (16 * m ^ 2 - 4 * m  ) ) / (2 * m)
        field_simp [(show m ≠ 0 by linarith)]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        <;> nlinarith
      rcases h4 with ⟨x, hx⟩
      have h5 := h x
      nlinarith
    have h2 : m < 1 / 4 := by
      by_contra h2
      push_neg at h2
      have h4 := h 3
      nlinarith
    constructor <;> linarith
  · -- Assume that $0 \le m \land m < \frac{1}{4}$
    rintro ⟨hm1, hm2⟩
    intro x
    by_cases h3 : m = 0
    · -- m = 0
      rw [h3]
      nlinarith
    · -- m > 0
      have h4 : m > 0 := by
        by_contra h4
        push_neg at h4
        have : m = 0 := by nlinarith
        tauto
      nlinarith [sq_nonneg (m * x - 3 * m), sq_nonneg (x - 3), sq_nonneg (m), sq_nonneg ((m) - 1 / 4), sq_nonneg (x - 3), sq_nonneg ((x - 3) * (m)), sq_nonneg ((x -3) * (m -0))]