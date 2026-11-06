import Mathlib

theorem algebra_3353 {a b c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0)
    (P Q : ℝ → ℝ) (hP : P = fun x => a * x ^ 2 + b * x + c)
    (hQ : Q = fun x => -a * x ^ 2 + b * x + c) :
    ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ P x1 * Q x1 = 0 ∧ P x2 * Q x2 = 0 := by
  by_cases h : b ^ 2 - 4 * a * c > 0
  · -- If b^2 - 4ac > 0, then P(x) has two distinct real roots.
    have h1 : b ^ 2 - 4 * a * c > 0 := h
    use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a),
      (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
    constructor
    · -- Show x1 ≠ x2
      by_contra h3
      have h2 : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by linarith
      have h3 : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) := by
        field_simp [show a ≠ 0 by exact ha] at h2 ⊢
        linarith
      have h4 : Real.sqrt (b ^ 2 - 4 * a * c) = 0 := by linarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c)]
      have h5 : b ^ 2 - 4 * a * c = 0 := by
        calc
          b ^ 2 - 4 * a * c = (Real.sqrt (b ^ 2 - 4 * a * c)) ^ 2 := by rw [Real.sq_sqrt]; nlinarith
          _ = 0 ^ 2 := by rw [show Real.sqrt (b ^ 2 - 4 * a * c) = (0 : ℝ) by linarith]
          _ = (0 : ℝ) := by norm_num
      linarith
    constructor
    · -- Show P x1 * Q x1 = 0
      have hx1 : P ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) = 0 := by
        rw [hP]
        simp
        field_simp [show a ≠ 0 by exact ha]
        nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sq_sqrt (show 0 ≤ (b ^ 2 - 4 * a * c : ℝ) by nlinarith)]
      have h0 : P ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) * Q ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) = 0 := by
        rw [show P ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) = 0 by exact hx1]
        norm_num
      linarith
    · -- Show P x2 * Q x2 = 0
      have hx2 : P ((-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) = 0 := by
        rw [hP]
        simp
        field_simp [show a ≠ 0 by exact ha]
        nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sq_sqrt (show 0 ≤ (b ^ 2 - 4 * a * c : ℝ) by nlinarith)]
      have h0 : P ((-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) * Q ((-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) = 0 := by
        rw [show P ((-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) = 0 by exact hx2]
        norm_num
      linarith
  · -- b^2 - 4ac ≤ 0
    have h2 : b ^ 2 - 4 * a * c ≤ 0 := by linarith
    have h3 : b ^ 2 + 4 * a * c > 0 := by
      by_cases h4 : b ^ 2 - 4 * a * c < 0
      · -- b^2 - 4ac < 0
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hc, sq_nonneg (b), sq_nonneg (a * c)]
      · -- b^2 - 4ac = 0
        have h5 : b ^ 2 - 4 * a * c = 0 := by linarith
        nlinarith [sq_nonneg (b), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hc]
    use (-b + Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a)), 
      (-b - Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a))
    constructor
    · -- Show x1 ≠ x2
      by_contra h3
      have h2 : (-b + Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a)) = (-b - Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a)) := by linarith
      have h3 : (-b + Real.sqrt (b ^ 2 + 4 * a * c)) = (-b - Real.sqrt (b ^ 2 + 4 * a * c)) := by
        field_simp [show a ≠ 0 by exact ha] at h2 ⊢
        linarith
      have h4 : Real.sqrt (b ^ 2 + 4 * a * c) = 0 := by linarith [Real.sqrt_nonneg (b ^ 2 + 4 * a * c)]
      have h5 : b ^ 2 + 4 * a * c = 0 := by
        calc
          b ^ 2 + 4 * a * c = (Real.sqrt (b ^ 2 + 4 * a * c)) ^ 2 := by rw [Real.sq_sqrt]; nlinarith
          _ = 0 ^ 2 := by rw [show Real.sqrt (b ^ 2 + 4 * a * c) = (0 : ℝ) by linarith]
          _ = (0 : ℝ) := by norm_num
      linarith
    constructor
    · -- Show P x1 * Q x1 = 0
      have hx1 : Q ((-b + Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a))) = 0 := by
        rw [hQ]
        simp
        field_simp [show a ≠ 0 by exact ha]
        nlinarith [Real.sqrt_nonneg (b ^ 2 + 4 * a * c), Real.sq_sqrt (show 0 ≤ (b ^ 2 + 4 * a * c : ℝ) by nlinarith)]
      have h0 : P ((-b + Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a))) * Q ((-b + Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a))) = 0 := by
        rw [show Q ((-b + Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a))) = 0 by exact hx1]
        norm_num
      linarith
    · -- Show P x2 * Q x2 = 0
      have hx2 : Q ((-b - Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a))) = 0 := by
        rw [hQ]
        simp
        field_simp [show a ≠ 0 by exact ha]
        nlinarith [Real.sqrt_nonneg (b ^ 2 + 4 * a * c), Real.sq_sqrt (show 0 ≤ (b ^ 2 + 4 * a * c : ℝ) by nlinarith)]
      have h0 : P ((-b - Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a))) * Q ((-b - Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a))) = 0 := by
        rw [show Q ((-b - Real.sqrt (b ^ 2 + 4 * a * c)) / (2 * (-a))) = 0 by exact hx2]
        norm_num
      linarith