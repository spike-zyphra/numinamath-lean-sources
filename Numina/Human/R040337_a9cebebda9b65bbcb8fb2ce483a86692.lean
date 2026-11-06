import Mathlib

/- Find all values of $x$ with $0 \leq x<2 \pi$ that satisfy $\sin x+\cos x=\sqrt{2}$. -/
theorem algebra_611017: {x : ℝ | x ∈ Set.Ico 0 (2 * Real.pi) ∧ Real.sin x + Real.cos x = Real.sqrt 2} = {Real.pi / 4} := by
  ext x
  simp
  constructor
  . intro ⟨hx_range, h⟩

    -- prove $sin(x + \frac\pi 4) = 1$
    have := Real.sin_add x (Real.pi / 4)
    rw [
      Real.sin_pi_div_four,
      Real.cos_pi_div_four,
      <-add_mul,
      h,
      <-mul_div_assoc,
      Real.mul_self_sqrt (by norm_num),
      div_self (by norm_num),
      -- prove $\frac\pi 4 = \frac\pi 2 + 2k\pi$
      Real.sin_eq_one_iff
    ] at this
    obtain ⟨k, hk⟩ := this
    replace hk : x = (1 / 4 + 2 * k) * Real.pi := by linear_combination -hk
    -- prove $-\frac 1 8 \le k \lt \frac 7 8$
    rw [hk] at hx_range
    simp [Real.pi_nonneg, Real.pi_pos] at hx_range
    have range_1 : - 1 / 8 ≤ (k:ℝ) := by
      have := hx_range.1
      simp [Real.pi_nonneg, not_le_of_lt Real.pi_pos] at this
      linear_combination this / 2
    have range_2 : (k:ℝ) < 7 / 8 := by
      have := hx_range.2
      simp [Real.pi_nonneg, not_le_of_lt Real.pi_pos] at this
      linear_combination this / 2
    -- so $k = 0$
    have range_1' : - 1 < (k:ℝ) := by linarith
    have range_2' : (k:ℝ) < 1 := by linarith
    norm_cast at range_1' range_2'
    simp at range_1'
    rw [show (-1:ℤ) = 0 - 1 by ring] at range_1'
    replace range_1':= Int.le_of_sub_one_lt range_1'
    rw [show (1:ℤ) = 0 + 1 by ring] at range_2'
    replace range_2':= Int.le_of_lt_add_one range_2'
    have hk_eq_0 : k = 0 := le_antisymm range_2' range_1'
    rw [hk_eq_0] at hk

    -- simplify with $k = 0$
    rw [hk]
    ring_nf
  . intro hx
    rw [hx]
    constructor
    -- prove $0 \le \frac\pi 4 < 2\pi$
    . constructor
      . exact div_nonneg Real.pi_nonneg (by norm_num)
      . apply lt_of_sub_pos
        ring_nf
        exact mul_pos Real.pi_pos (by norm_num)
    -- prove $\sin \frac\pi 4 + \cos \frac\pi 4 = \sqrt 2$
    . rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
      ring
