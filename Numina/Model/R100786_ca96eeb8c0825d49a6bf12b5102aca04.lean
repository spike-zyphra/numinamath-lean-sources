import Mathlib

theorem algebra_124379 (a b : ℕ) : a * (a + 5) = b * (b + 1) ↔ (a, b) = (0, 0) ∨ (a, b) = (1, 2) := by
  constructor
  · -- Forward direction: if $a \cdot (a + 5) = b \cdot (b + 1)$, then $(a, b) \in \{(0, 0), (1, 2)\}$
    intro h
    have h1 : a ≤ b + 1 := by nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a + b + 2 : ℤ)]
    have h2 : a + 4 ≥ b := by nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a + b + 2 : ℤ)]
    have h3 : a ≤ 2 := by
      by_cases h4 : a > 2
      · -- Assume a > 2, prove contradiction
        have h5 : a ≥ 3 := by omega
        have h6 : b ≥ 3 := by nlinarith [h, h5]
        have h7 : b ≤ a + 1 := by nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a + b + 2 : ℤ)]
        have h8 : a ≤ 4 := by nlinarith [h, h7, h5, h6]
        interval_cases a <;> interval_cases b <;> omega
      omega
    have h4 : b < 6 := by
      nlinarith [h, h3]
    have h5 : a < 3 := by
      omega
    interval_cases a <;> interval_cases b <;> simp [Prod.ext_iff] at *
    <;> tauto
  · -- Backward direction: if $(a, b) \in \{(0, 0), (1, 2)\}$, then $a \cdot (a + 5) = b \cdot (b + 1)$
    rintro (h | h)
    · -- Case (0, 0)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Case (1, 2)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num