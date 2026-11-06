import Mathlib

theorem inequalities_53895 : { abs (a^2 - b^2) / (a^2 + b^2) | (a : ℝ) (b : ℝ) (h : a * b / (a^2 + b^2) = 1 / 4) } = { Real.sqrt 3 / 2 } := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume there exist a, b such that abs (a^2 - b^2) / (a^2 + b^2) = x and a * b / (a^2 + b^2) = 1 / 4, prove that x = Real.sqrt 3 / 2
    rintro ⟨a, b, h_eq, hx⟩
    have h1 : a^2 + b^2 > 0 := by
      by_contra h2
      push_neg at h2
      have h2' : a^2 + b^2 = 0 := by linarith [sq_nonneg a, sq_nonneg b, h2]
      have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h2']
      have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h2']
      rw [ha, hb] at h_eq
      norm_num [ha, hb] at h_eq
      all_goals linarith
    have h2 : 4 * a * b = a^2 + b^2 := by
      have hne : a^2 + b^2 ≠ 0 := by linarith [h1]
      field_simp at h_eq
      nlinarith
    have h3 : (a^2 - b^2) ^ 2 = (3 / 4) * (a^2 + b^2) ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg (a^2 - b^2), h2, h1]
    have h4 : abs (a^2 - b^2) = (Real.sqrt 3 / 2) * (a^2 + b^2) := by
      have h5 : (a^2 - b^2) ^ 2 = (3 / 4) * (a^2 + b^2) ^ 2 := h3 
      have h6 : abs (a^2 - b^2) = Real.sqrt ((a^2 - b^2) ^ 2) := by 
        rw [Real.sqrt_sq_eq_abs]
      rw [h6]
      have h7 : Real.sqrt ((a^2 - b^2) ^ 2) = Real.sqrt (( (3 / 4) * (a^2 + b^2) ^ 2 )) := by
        rw [h5]
      rw [h7]
      have h8 : Real.sqrt (( (3 / 4) * (a^2 + b^2) ^ 2 )) = Real.sqrt (3 / 4) * Real.sqrt ((a^2 + b^2) ^ 2) := by
        rw [Real.sqrt_mul (by positivity)]
      rw [h8]
      have h9 : Real.sqrt ((a^2 + b^2) ^ 2) = a^2 + b^2 := Real.sqrt_sq (by linarith [h1, sq_nonneg (a^2 + b^2)])
      have h10 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h9, h10]
      <;> ring_nf <;> norm_num
      all_goals nlinarith
    have h5 : abs (a^2 - b^2) / (a^2 + b^2) = Real.sqrt 3 / 2 := by
      rw [h4]
      field_simp [h1]
      <;> nlinarith
    rw [h5] at hx
    all_goals linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · -- Assume x = Real.sqrt 3 / 2, prove there exist a, b such that abs (a^2 - b^2) / (a^2 + b^2) = x and a * b / (a^2 + b^2) = 1 / 4
    intro hx
    rw [hx]
    use (Real.sqrt 3 + 1) / 2, (Real.sqrt 3 - 1) / 2
    constructor
    · -- Show that $\frac{|a^2 - b^2|}{a^2 + b^2} = \frac{\sqrt{3}}{2}$
      have h1 : ((Real.sqrt 3 + 1) / 2: ℝ) ^ 2 + ((Real.sqrt 3 - 1) / 2: ℝ) ^ 2 = 2 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have h2 : ((Real.sqrt 3 + 1) / 2: ℝ) ^ 2 - ((Real.sqrt 3 - 1) / 2: ℝ) ^ 2 = Real.sqrt 3 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have h3 : abs (((Real.sqrt 3 + 1) / 2: ℝ) ^ 2 - ((Real.sqrt 3 - 1) / 2: ℝ) ^ 2) = Real.sqrt 3 := by
        rw [h2]
        all_goals norm_num [abs_of_pos, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]
      rw [h3, h1]
      all_goals field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- Show that $\frac{ab}{a^2 + b^2} = \frac{1}{4}$
      have h1 : ((Real.sqrt 3 + 1) / 2: ℝ) * ((Real.sqrt 3 - 1) / 2: ℝ) = 1 / 2 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have h2 : ((Real.sqrt 3 + 1) / 2: ℝ) ^ 2 + ((Real.sqrt 3 - 1) / 2: ℝ) ^ 2 = 2 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have h3 : ((Real.sqrt 3 + 1) / 2: ℝ) * ((Real.sqrt 3 - 1) / 2: ℝ) / (((Real.sqrt 3 + 1) / 2: ℝ) ^ 2 + ((Real.sqrt 3 - 1) / 2: ℝ) ^ 2) = 1 / 4 := by
        rw [h1, h2]
        all_goals norm_num
      simpa using h3