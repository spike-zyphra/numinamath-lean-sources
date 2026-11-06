import Mathlib

theorem algebra_10195: IsGreatest {k : ℝ | ∃ x y, x ≠ y ∧ x^2 + k * x + 5 = 0 ∧ y^2 + k * y + 5 = 0 ∧ |x - y| = Real.sqrt 61} 9 := by
  constructor
  · -- Let's prove 9 is attainable.
    use (-9 + Real.sqrt 61) / 2, (-9 - Real.sqrt 61) / 2
    constructor
    · -- Show that $\frac{-9 + \sqrt{61}}{2} \neq \frac{-9 - \sqrt{61}}{2}$
      by_contra h
      have h1 : Real.sqrt 61 = 0 := by linarith
      have h2 : Real.sqrt 61 > 0 := by positivity
      linarith
    constructor
    · -- Show that $x^2 + 9x + 5 = 0$
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (61 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (61 : ℝ) by norm_num)]
    constructor
    · -- Show that $y^2 + 9 y + 5 = 0$
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (61 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (61 : ℝ) by norm_num)]
    · -- Show that $|x - y| = \sqrt{61}$
      have h : ((-9 + Real.sqrt 61) / 2 : ℝ) - ((-9 - Real.sqrt 61) / 2 : ℝ) = Real.sqrt 61 := by ring
      rw [h]
      simp
  · -- Let's prove that 9 is greatest
    intro k hk
    rcases hk with ⟨x, y, hxy, hx, hy, habs⟩
    have h3 : (x - y) * (x + y + k) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Contradiction case: x - y = 0 implies x = y
      exfalso
      apply hxy
      linarith
    · -- Case where $x + y + k = 0$ holds
      have h31 : x + y = -k := by linarith
      have h41 : (x - y) ^ 2 = 61 := by
        have h51 : |x - y| = Real.sqrt 61 := habs
        have h61 : (x - y) ^ 2 = 61 := by
          calc
            (x - y) ^ 2 = (x - y) ^ 2 := by rfl
            _ = ( |x - y| ) ^ 2 := by rw [sq_abs]
            _ = (Real.sqrt 61) ^ 2 := by rw [h51]
            _ = (61 : ℝ) := Real.sq_sqrt (by norm_num)
        linarith
      have h81 : x * y = 5 := by
        nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
          intro h'
          apply hxy
          linarith
        ), sq_nonneg (x - y), sq_nonneg (x + y + k)]
      have h71 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
        nlinarith
      rw [h31, h81] at h71
      nlinarith [sq_nonneg k]