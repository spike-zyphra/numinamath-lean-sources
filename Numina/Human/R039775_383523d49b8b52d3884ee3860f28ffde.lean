import Mathlib

/- Find the value of $x$ that satisfies $\frac{\sqrt{3x+5}}{\sqrt{6x+5}}=\frac{\sqrt{5}}{3}$. Express your answer as a common fraction. -/
theorem algebra_10196 (x : ℝ) :
    Real.sqrt (3 * x + 5) / Real.sqrt (6 * x + 5) = Real.sqrt 5 / 3 ↔ x = 20 / 3 := by
  constructor

  · -- Forward direction: equation holds → x = 20/3
    intro eq
    have pos0 : Real.sqrt (6 * x + 5) ≠ 0 := by
      simp
      by_contra h
      have h1 : √(3 * x + 5) / 0 = 0 := div_zero (√(3 * x + 5))
      rw [h, h1] at eq
      have h2 : √5 / 3 ≠ 0 := by norm_num
      rw [eq] at h2
      have h3 : √5 / 3 = √5 / 3 := by rfl
      exact (h2 h3)
    have pos1 : 0 < 3 * x + 5 := by   -- Prove 3x + 5 >= 0
      have h : Real.sqrt (3 * x + 5) = (Real.sqrt 5 / 3) * Real.sqrt (6 * x + 5) := by
        rw [div_eq_iff] at eq
        exact eq
        exact pos0
      have h1 : √5 / 3 ≠ 0 := by norm_num
      have h2 : √5 / 3 * √(6 * x + 5) ≠ 0 := mul_ne_zero h1 pos0
      rw [← h] at h2
      rw [Real.sqrt_ne_zero'] at h2
      exact h2
    have pos2 : 0 ≤ 6 * x + 5 := by  -- Prove 6x + 5 > 0
      have h : Real.sqrt (3 * x + 5) = (Real.sqrt 5 / 3) * Real.sqrt (6 * x + 5) := by
        rw [div_eq_iff] at eq
        exact eq
        exact pos0
      have h1 : √5 / 3 ≠ 0 := by norm_num
      have h2 : Real.sqrt (6 * x + 5) = Real.sqrt (3 * x + 5) / (Real.sqrt 5 / 3) := by
        rw [mul_comm (√5 / 3), ← div_eq_iff] at h
        exact h.symm
        exact h1
      have h3 : 0 < (√5 / 3) := by norm_num
      have h4 : 0 < √(3 * x + 5) / (√5 / 3) := div_pos_iff.mpr (Or.inl ⟨Real.sqrt_pos.mpr pos1, h3⟩)
      rw [← h2, Real.sqrt_pos] at h4
      exact h4.le
    have step1 : Real.sqrt (3 * x + 5) * 3 = Real.sqrt 5 * Real.sqrt (6 * x + 5) := by
      rw [div_eq_iff, div_mul_eq_mul_div] at eq  -- Rewrite using division identities
      rw [eq]  -- Substitute the given equation
      norm_num  -- Simplify numerical expressions
      exact pos0
    have step2 : (Real.sqrt (3 * x + 5) * 3)^2 = (Real.sqrt 5 * Real.sqrt (6 * x + 5))^2 := by rw [step1]  -- Square both sides
    rw [mul_pow, mul_pow] at step2  -- Expand powers of products
    norm_num at step2  -- Simplify numerical expressions
    rw [Real.sq_sqrt, Real.sq_sqrt, mul_comm, mul_add, mul_add, ← mul_assoc 9, ← mul_assoc 5] at step2  -- Simplify square roots and multiplications
    norm_num at step2  -- Simplify numerical expressions
    linarith [step2]  -- Solve linear arithmetic problems
    linarith; linarith
  · -- Reverse direction: x = 20/3 → equation holds
    intro h
    rw [h]  -- Substitute x = 20/3
    have : 3 * (20 / 3) + 5 = (25 : ℝ) := by norm_num
    have : 6 * (20 / 3) + 5 = (45 : ℝ) := by norm_num
    simp_all
    have : √25 / √45 = √5 / 3 := by
      calc
      √25 / √45 = √(5 * 5) / √(5 * 3 * 3) := by norm_num  -- Simplify square roots
      _ = √5 * √5 / (√5 * √3 * √3) := by simp
      _ = √5 * √5 / √5 / (√3 * √3) := by ring
      _ = √5 / 3 := by norm_num
    exact this
