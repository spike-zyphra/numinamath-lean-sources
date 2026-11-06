import Mathlib

/-
Find all integers satisfying the equation $2^{x} \cdot(4-x)=2 x+4$.
-/
theorem algebra_240748 : {x : ℤ | (2:ℝ) ^ x * (4 - x) = 2 * x + 4} = {0, 1, 2} := by
  ext x
  simp
  constructor
  . intro h
    -- prove $x\ne 4$, so $2^x = \frac{2x+4}{4-x}$
    have x_ne_4: x ≠ 4 := by
      intro x_eq_4
      rw [x_eq_4] at h
      norm_num at h
    -- so $2^x = \frac{2x+4}{4-x}$
    have h1 :(2:ℝ) ^ x = (2 * ↑x + 4) / (4 - ↑x) := by
      rw [eq_div_iff_mul_eq]
      exact h
      norm_cast
      rw [sub_eq_zero]
      exact Ne.symm x_ne_4
    -- $0<2^x$ means $0 < \frac{2x+4}{4-x}$
    have h2 : 0 < (2:ℝ) ^ x := by
      apply zpow_pos
      norm_num
    -- prove $x\in (-2,4)$ by $0 < \frac{2x+4}{4-x}$
    have h3 : x ∈ Finset.Ioo (-2:ℤ) 4 := by
      rw [Finset.mem_Ioo]
      rw [h1, div_pos_iff] at h2
      match h2 with
      | Or.inl h2 =>
        constructor
        . have := h2.1
          norm_cast at this
          linarith only [this]
        . have := h2.2
          norm_cast at this
          linarith only [this]
      | Or.inr h2 =>
        exfalso
        linarith only [h2]
    -- check every number in $(-2,4)$
    fin_cases h3
    . simp at h1; norm_num at h1
    . simp
    . simp
    . simp
    . simp at h1; norm_num at h1
  . intro h
    -- check every number in {0, 1, 2}
    match h with
    | Or.inl h =>
      rw [h]
      norm_num
    | Or.inr (Or.inl h) =>
      rw [h]
      norm_num
    | Or.inr (Or.inr h) =>
      rw [h]
      norm_num
