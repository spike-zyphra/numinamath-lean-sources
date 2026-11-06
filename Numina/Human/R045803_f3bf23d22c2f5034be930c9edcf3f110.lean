import Mathlib

/- The ratio of $x+2$ to $2x+2$ is equal to the ratio of $4x+3$ to $7x+3$.  What is the product of all real x which satisfy this statement? -/
theorem algebra_11391
    (s : Set ℝ)
    (hs : s = {x : ℝ | (x + 2) / (2 * x + 2) = (4 * x + 3) / (7 * x + 3)}) :
    s.Finite ∧ ((fin : s.Finite) → fin.toFinset.prod id = 0) := by

  have : ∀ x : ℝ, (x + 2) / (2 * x + 2) = (4 * x + 3) / (7 * x + 3) ↔ x = 0 ∨ x = 3 := by
    intro x
    constructor
    . intro h
      have t1 : 2 * x + 2 ≠ 0 := by
        by_contra! h_contra
        simp [h_contra] at h
        rcases div_eq_zero_iff.mp h.symm <;> linarith
      have t2 : 7 * x + 3 ≠ 0 := by
        by_contra! h_contra
        simp [h_contra] at h
        rcases h <;> linarith

      -- We are given that $\frac{x+2}{2x+2} = \frac{4x+3}{7x+3}$. Cross multiplying, we find $(x+2)(7x+3) = (2x+2)(4x+3)$.
      apply_fun fun t => t * (2 * x + 2) * (7 * x + 3) at h
      field_simp at h

      -- Multiplying out each side by the distributive property yields $7x^{2}+3x+14x+6 = 8x^{2}+6x+8x+6$. Simplifying, we find $x^{2}=3x$,
      have : x ^ 2 = 3 * x := by linarith

      -- so $x = 0, 3$.
      simp only [pow_two, mul_eq_mul_right_iff] at this
      rw [or_comm] at this
      exact this
    -- Checking our two answers, we find that indeed $\frac{2}{2} = \frac{3}{3}$, and also that $\frac{5}{8} = \frac{15}{24}$. 
    . intro h
      rcases h with h | h
      <;> rw [h] <;> norm_num

  simp only [this, show {x : ℝ | x = 0 ∨ x = 3} = {0, 3} by rfl] at hs
  simp_all
