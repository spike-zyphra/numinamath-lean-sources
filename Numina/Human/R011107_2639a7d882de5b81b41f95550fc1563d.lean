import Mathlib

/-
958*. Solve the inequality in integers
$$
\frac{1}{\sqrt{x-2 y+z+1}}+\frac{2}{\sqrt{2 x-y+3 z-1}}+\frac{3}{\sqrt{3 y-3 x-4 z+3}}>x^{2}-4 x+3
$$
-/
theorem inequalities_115829 :
    {(x, y, z) : ℤ × ℤ × ℤ | 1 / √(x - 2 * y + z + 1 : ℝ) + 2 / √(2 * x - y + 3 * z - 1 : ℝ) + 3 / √(3 * y - 3 * x - 4 * z + 3 : ℝ) > x ^ 2 - 4 * x + 3 ∧
      x - 2 * y + z + 1 > 0 ∧ 2 * x - y + 3 * z - 1 > 0 ∧ 3 * y - 3 * x - 4 * z + 3 > 0} = {(3, 1, -1)} := by
  ext ⟨x, y, z⟩
  constructor <;> intro h
  · -- note that 1 + 1 + 1 ≤ x - 2 * y + z + 1 + 2 * x - y + 3 * z - 1 + 3 * y - 3 * x - 4 * z + 3 = 3
    simp only [Set.mem_setOf_eq, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    have h₂ : x - 2 * y + z + 1 ≥ 1 := by exact h₂
    have h₃ : 2 * x - y + 3 * z - 1 ≥ 1 := by exact h₃
    have h₄ : 3 * y - 3 * x - 4 * z + 3 ≥ 1 := by exact h₄
    have heq : 3 = (x - 2 * y + z + 1) + (2 * x - y + 3 * z - 1) + (3 * y - 3 * x - 4 * z + 3) := by ring
    have h₂ : x - 2 * y + z + 1 = 1 := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h
      · linarith only [h, h₂]
      · have : 3 < (x - 2 * y + z + 1) + (2 * x - y + 3 * z - 1) + (3 * y - 3 * x - 4 * z + 3) := by linarith only [h, h₃, h₄]
        linarith only [heq, this]
    -- Therefore, we have $$ \begin{array}{l} x - 2 y + z + 1 = 1, \ 2 x - y + 3 z - 1 = 1, \ 3 y - 3 x - 4 z + 3 = 1 . \end{array} $$
    have h₃ : 2 * x - y + 3 * z - 1 = 1 := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h
      · linarith only [h, h₃]
      · have : 3 < (x - 2 * y + z + 1) + (2 * x - y + 3 * z - 1) + (3 * y - 3 * x - 4 * z + 3) := by linarith only [h, h₂, h₄]
        linarith only [heq, this]
    have h₄ : 3 * y - 3 * x - 4 * z + 3 = 1 := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h
      · linarith only [h, h₄]
      · have : 3 < (x - 2 * y + z + 1) + (2 * x - y + 3 * z - 1) + (3 * y - 3 * x - 4 * z + 3) := by linarith only [h, h₂, h₃]
        linarith only [heq, this]
    norm_cast at h₁
    -- Then 1 / 1 + 2 / 1 + 3 / 1 > x ^ 2 - 4 * x + 3
    rw [h₂, h₃, h₄] at h₁
    norm_num at h₁
    have : (x - 2 : ℝ) ^ 2 < √7 ^ 2 := by norm_num; nlinarith only [h₁]
    apply sq_lt_sq.mp at this
    simp [abs] at this
    have hx₁ : 2 - √7 < x := by linarith only [this.2]
    have hx₂ : x < 2 + √7 := by linarith only [this.1]
    have hx₁ : -1 < (x : ℝ) := by
      apply lt_trans  ?_ hx₁
      norm_num
      apply lt_of_pow_lt_pow_left₀ (n := 2)
      all_goals norm_num
    have hx₂ : x < (5 : ℝ) := by
      apply lt_trans hx₂
      apply add_lt_of_lt_sub_left
      norm_num
      apply lt_of_pow_lt_pow_left₀ (n := 2)
      all_goals norm_num
    -- we obtain that 0 ≤ x ≤ 4
    norm_cast at hx₁ hx₂
    simp at hx₁
    -- since x + 2 = 5 * y, we have 5 ∣ x + 2, which implies x = 3
    have : x + 2 = 5 * y := by linarith only [h₂, h₃, h₄]
    have hxdvd : 5 ∣ x + 2 := by use y
    interval_cases x
    any_goals norm_num at hxdvd
    simp
    constructor
    all_goals linarith only [h₂, this]
  · -- Verify the reverse direction
    simp at h
    simp [h.1, h.2.1, h.2.2]
    norm_num
