import Mathlib

/- 4. Let real numbers $a, b, c$ satisfy $\left\{\begin{array}{l}a^{2}-b c-8 a+7=0 \\ b^{2}+c^{2}+b c-6 a+6=0,\end{array} \quad a\right.$, the range of values for $a$ is -/
theorem algebra_258910 (a: ℝ) : (∃ (b c : ℝ), a^2 - b * c - 8 * a + 7 = 0 ∧ b^2 + c^2 + b * c - 6 * a + 6 = 0) ↔ 1 ≤ a ∧ a ≤ 9 := by
  constructor <;> rintro h
    -- left to right
  . obtain ⟨b, c, h₀, h₁⟩ := h
    -- epxress bc and b^2+c^2 in terms of a
    have hbc: b*c = a^2 - 8*a + 7 := by linarith
    have hbc' : b^2 + c^2 = 6*a-6 - a^2 + 8*a - 7 := by linarith
    -- as (b-c)^2 is nonengative, plug in bc and b^2 + c^2  there
    have hbc_bound: 0 ≤ (b-c)^2 := by exact sq_nonneg (b - c)
    ring_nf at hbc_bound
    rw [hbc, add_assoc, hbc'] at hbc_bound
    -- the inequality becoems 3*(a-5)^2 ≤ 48, from which we get 1 ≤ a ≤ 9
    convert_to 0 ≤ 48 - 3*(a-5)^2 at hbc_bound
    . ring
    . have: (a-5)^2 ≤ 4^2 := by linarith
      have:= abs_le_of_sq_le_sq' this (by norm_num)
      constructor <;> linarith
    -- right to left, first ocnvert 1 ≤ a ≤ 9 to (a-5)^2 ≤ 16
  . have : -4 ≤ a-5 ∧ a-5 ≤ 4 := by constructor <;> linarith
    have : |a-5| ≤ 4 := by exact abs_le.mpr this
    have : |a-5|^2 ≤ 4^2 := by refine (sq_le_sq₀ ?_ ?_).mpr this <;> simp
    norm_num at this
    ring_nf at this
    have ha' : 0 ≤ 48 - 3*(a-5)^2 := by
      ring_nf
      linarith
    -- no use two following values for b, c, the fact taht (a-5)^2 ≤ 16 means the square roots are well defined, now plug in and prove
    use ((a-1) + √(48-3*(a-5)^2))/2, ((a-1) - √(48-3*(a-5)^2))/2
    ring_nf
    have ha': 0 ≤ (-27 + (a * 30 - a ^ 2 * 3)) := by
      convert ha' using 1
      ring
    simp [ha']
    ring