import Mathlib

open Set Real

theorem inequalities_324755 {N M : Set ℝ}
    (hN : N = {x | (1 / 2 : ℝ) ^ x ≤ 1}) (hM : M = {x | x ^ 2 - 6 * x + 8 ≤ 0}) :
    N ∩ M = {x | 2 ≤ x ∧ x ≤ 4} := by
  ext x
  simp [hN, hM]
  constructor
  · -- Assume $x \in N \cap M$, need to show $2 \leq x \land x \leq 4$.
    rintro ⟨hx1, hx2⟩
    constructor
    · -- Solving $x^2 - 6x + 8 \leq 0$ gives $2 \leq x \leq 4$, so $2 \leq x$.
      nlinarith [hx2]
    · -- Solving $x^2 - 6x + 8 \leq 0$ gives $2 \leq x \leq 4$, so $x \leq 4$.
      nlinarith [hx2]
  · -- Assume $2\leq x \land x \leq 4$, need to show $x \in N \cap M$.
    rintro ⟨hx1, hx2⟩
    constructor
    · -- Show $(1/2)^x \leq 1$.
      -- This is equivalent to showing $x \geq 0$, which is true since $2 \leq x$.
      have h4 : 0 ≤ x := by linarith
      have h3 : (1 / 2 : ℝ) ^ x ≤ 1 := by
        have h4' : 0 ≤ x := by linarith
        have h5 : (1 / 2 : ℝ) ^ x ≤ (1 / 2 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_ge
          all_goals linarith
        have h6 : (1 / 2 : ℝ) ^ (0 : ℝ) = 1 := by
          norm_num
        linarith [h6, h5]
      linarith
    · -- Show $x^2 - 6 x + 8 \leq 0$.
      nlinarith [hx1, hx2]