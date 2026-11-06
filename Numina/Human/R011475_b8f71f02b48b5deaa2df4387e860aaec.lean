import Mathlib

/-Given ${{a}^{2}}-a=7$, then the value of the algebraic expression $\frac{a-1}{a+2}\centerdot \frac{{{a}^{2}}-4}{{{a}^{2}}-2a+1}\div \frac{1}{{{a}^{2}}-1}$ is ( ).

A: $3$

B: $\frac{7}{2}$

C: $4$

D: $5$-/
theorem algebra_625221
    {a : ℝ}
    (h : a^2 - a = 7) :
    ((a - 1) / (a + 2)) * ((a^2 - 4) / (a^2 - 2 * a + 1)) / (1 / (a^2 - 1)) = 5 := by
  -- First of all, let's show that the denominators are not 0.
  have h1 : a ≠ -2 := by
    by_contra h2
    have h3 : a ^ 2 - a = 7 := h
    rw [h2] at h3
    norm_num at h3
  have h2 : a ≠ 1 := by
    by_contra h3
    have h4 : a ^ 2 - a = 7 := h
    rw [h3] at h4
    norm_num at h4
  have h3 : a ≠ -1 := by
    by_contra h4
    have h5 : a ^ 2 - a = 7 := h
    rw [h4] at h5
    norm_num at h5
  have h4 : a + 2 ≠ 0 := by
    intro h5
    apply h1
    linarith
  have h5 : a^2 - 2 * a + 1 ≠ 0 := by
    have h6 : a ≠ 1 := h2
    have h7 : a^2 - 2 * a + 1 = (a - 1) ^ 2 := by ring
    rw [h7]
    have h8 : (a - 1) ^ 2 ≠ 0 := by
      apply pow_ne_zero 2
      intro h9
      apply h6
      linarith
    exact h8
  have h6 : a^2 - 1 ≠ 0 := by
    have h7 : a ≠ 1 := h2
    have h8 : a ≠ -1 := h3
    have h9 : a^2 - 1 = (a - 1) * (a + 1) := by ring
    rw [h9]
    have h10 : (a - 1) * (a + 1) ≠ 0 := by
      apply mul_ne_zero
      · intro h11
        apply h7
        linarith
      · intro h12
        apply h8
        linarith
    exact h10
  -- Then we can use field_simp to get $\frac{a-1}{a+2}\cdot \frac{a^2-4}{a^2-2a+1}\div \frac{1}{a^2-1}$
  -- $=\frac{a-1}{a+2}\cdot \frac{(a+2)(a-2)}{(a-1)^2}\cdot (a+1)(a-1)$
  -- $=(a+1)(a-2)$
  have eq1 : ((a - 1) / (a + 2)) * ((a^2 - 4) / (a^2 - 2 * a + 1)) / (1 / (a^2 - 1)) = (a - 2) * (a + 1) := by
    have h7 : a + 2 ≠ 0 := h4
    have h8 : a^2 - 2 * a + 1 ≠ 0 := h5
    have h9 : a^2 - 1 ≠ 0 := h6
    field_simp [h7, h8, h9]
    ring
  rw [eq1]
  -- and the answer is easy to find:
  have h10 : (a - 2) * (a + 1) = 5 := by
    have h11 : a^2 - a = 7 := h
    nlinarith [sq_nonneg (a - 1)]
  linarith [h10]