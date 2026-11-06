import Mathlib

/- If $(2x+5)(x-3)=14$, find the sum of the possible values of $x$. -/
theorem algebra_18798:
  ∑ᶠ x ∈ {x:ℝ | (2*x+5)*(x-3)=14}, x = 1/2 := by
  -- (2x+5)(x-3)=14, simplifies to 2x^2-x-29=0
  have h1(x:ℝ): (2*x+5)*(x-3)=14 → 2*x^2-x-29 = 0 := by
    intro h
    have hh1: 2*x^2-x-29 = (2*x+5)*(x-3)-14 := by ring
    rw [h] at hh1
    simp [hh1]
  -- solve the equation, find out two roots.
  have h2(x:ℝ)(eq': 2*x^2-x-29=0):
    x = 1/4 + √233/4 ∨ x = 1/4 - √233/4 := by
    have eq: 2*(x*x) + (-1)*x + (-29) = 0 := by
      rw [← eq']; ring
    have hh1: discrim (2:ℝ) (-1) (-29) = √233 * √233 := by
      rw [discrim]; norm_num
    have hh2: (2:ℝ) ≠ 0 := by norm_num
    have hh3 := (quadratic_eq_zero_iff hh2 hh1 x).mp eq
    rcases hh3 with hh | hh
    <;> rw [hh] <;> field_simp <;> ring_nf <;> simp
  -- two roots are 1/4 + √233/4 and 1/4 - √233/4
  have h3: {x:ℝ | (2*x+5)*(x-3)=14} = {1/4 + √233/4, 1/4 - √233/4} := by
    ext x; simp
    constructor <;> intro h
    · have hh1 := h1 x h
      have hh2 := h2 x hh1
      simp at hh2; simp [hh2]
    · rcases h with hx | hx
      <;> rw [hx] <;> field_simp
      <;> ring_nf <;> field_simp <;> ring
  -- sum of the roots is 1/2
  have h4: (1/4 + √233/4) + (1/4 - √233/4) = 1/2 := by ring
  have h5: 1/4 + √233/4 ≠ 1/4 - √233/4 := by
    by_contra! hc
    have hh1: √233/4 = 0 := by
      linarith [hc]
    have hh2: √233 = 0 := by
      linarith [hh1]
    have hh3: (233:ℝ) = 0 := by
      rw [← mul_zero 0, ← hh2]; simp
    norm_num at hh3
  rw [h3, ← h4]
  apply finsum_mem_pair h5
