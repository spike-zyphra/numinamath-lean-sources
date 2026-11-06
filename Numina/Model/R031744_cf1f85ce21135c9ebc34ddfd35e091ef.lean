import Mathlib

theorem algebra_21425 : {t : ℝ | 4 * t - 2 ≠ 0 ∧ t * (2 * t - 3) / (4 *t - 2) ≤ 0} =
    Set.Iic 0 ∪ Set.Ioc (1 / 2) (3 / 2) := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ioc]
  constructor
  · -- First, prove the forward direction: if $t$ satisfies the inequality, then $t \in (-\infty, 0] \cup (\frac{1}{2}, \frac{3}{2}]$.
    rintro ⟨h1, h2⟩
    by_cases h6 : (4 * t - 2 : ℝ) > 0
    · -- Case where 4t-2 > 0
      have h7 : t * (2 * t - 3) ≤ 0 := by
        have h8 : t * (2 * t - 3) / (4 * t - 2) ≤ 0 := h2
        apply (div_nonpos_iff).mp at h8
        cases h8 with
        | inl h9 =>
          nlinarith
        | inr h10 =>
          nlinarith
      have h8 : t ≤ 3 / 2 := by nlinarith [sq_nonneg (t - 3 / 2), sq_nonneg (t - 0)]
      right
      constructor <;> linarith
    · -- Case where 4t-2 ≤ 0
      by_cases h7 : (4 * t - 2 : ℝ) < 0
      · -- Case where 4t-2 < 0
        have h8 : t * (2 * t - 3) ≥ 0 := by
          have h9 : t * (2 * t - 3) / (4 * t - 2) ≤ 0 := h2
          apply (div_nonpos_iff).mp at h9
          cases h9 with
          | inl h10 =>
            nlinarith
          | inr h11 =>
            nlinarith
        have h9 : t ≤ 0 := by nlinarith [sq_nonneg (t - 0), sq_nonneg (t - 3 / 2)
        ]
        left
        linarith
      · -- Case where 4t-2 = 0
        have h10 : (4 * t - 2 : ℝ) = 0 := by nlinarith
        contradiction
  · -- Now, prove the reverse direction: if $t \in (-\infty, 0] \cup (\frac{1}{2}, \frac{3}{2}]$, then $t$ satisfies the inequality.
    rintro (h | h)
    · -- Case where t ∈ (-∞, 0]
      have h1 : t ≤ 0 := by linarith
      constructor
      · -- Show $4 * t - 2 ≠ 0$
        by_contra h2
        have h3 : t = 1 / 2 := by nlinarith
        nlinarith
      · -- Show $\frac{t * (2 * t - 3) / (4 * t - 2)} \le 0$
        have h2 : 4 * t - 2 < 0 := by nlinarith
        have h3 : t * (2 * t - 3) ≥ 0 := by nlinarith [sq_nonneg (t - 0), sq_nonneg (t - 3 / 2)]
        have h4 : t * (2 * t - 3) / (4 * t - 2) ≤ 0 := by
          apply div_nonpos_of_nonneg_of_nonpos
          · -- Show $t \cdot (2t - 3) \le 0$
            linarith
          · -- Show $4t - 2 < 0$
            linarith
        exact h4
    · -- Case where t ∈ (∪, 3/2]
      rcases h with ⟨h1, h2⟩
      constructor
      · -- Show $4 * t - 2 ≠ 0$
        by_contra h3
        have h4 : t = 1 / 2 := by nlinarith
        nlinarith
      · -- Show $\frac{t * (2 * t - 3)}{(4 * t - 2)} \le 0$
        have h3 : 4 * t - 2 > 0 := by nlinarith
        have h4 : t * (2 * t - 3) ≤ 0 := by nlinarith [sq_nonneg (t - 0), sq_nonneg (t - 3 / 2)]
        have h5 : t * (2 * t - 3) / (4 * t - 2) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · -- Show $t * (2 * t - 3) ≤ 0$
            linarith
          · -- Show $4 * t - 2 ≥ 0$
            linarith
        exact h5