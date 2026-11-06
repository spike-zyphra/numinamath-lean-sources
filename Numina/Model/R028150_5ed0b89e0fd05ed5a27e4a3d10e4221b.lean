import Mathlib

theorem algebra_298131 (k : ℝ) :
    (∃ x y, x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 1 2 ∧ x^2 - k * x - k + 3 = 0 ∧ y^2 - k * y - k + 3 = 0) ↔
    2 < k ∧ k < 7 / 3 := by
  constructor
  · -- Assume that there exists such x and y.
    rintro ⟨x, y, hx, hy, h1, h2⟩
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    have h3 : x^2 - k * x - k + 3 = 0 := h1
    have h4 : y^2 - k * y - k + 3 = 0 := h2
    have h5 : (x - y) * (x + y - k) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h5) with
    | inl h =>
      exfalso
      nlinarith
    | inr h =>
      -- Now it follows that x + y = k.
      have hk : k = x + y := by linarith
      have hk1 : 2 < k := by
        nlinarith
      have hk2 : k < 7 / 3 := by
        nlinarith [sq_pos_of_pos (show 0 < y - 1 by linarith), sq_pos_of_pos (show 0 < 2 - y by linarith), sq_pos_of_pos (show 0 < 1 - x by linarith), sq_pos_of_pos (show 0 < x by linarith)]
      constructor <;> linarith
  · -- Show the existence of two roots in the open intervals (0,1) and (1,2).
    rintro ⟨hk1, hk2⟩
    have h1 : 0 < (k - Real.sqrt (k^2 + 4 * (k - 3))) / 2 := by
      have h2 : Real.sqrt (k ^ 2 + 4 * (k - 3)) < k := by
        nlinarith [Real.sqrt_nonneg (k ^ 2 + 4 * (k - 3)), Real.sq_sqrt (show 0 ≤ k ^ 2 + 4 * (k - 3) by nlinarith)]
      nlinarith [Real.sqrt_nonneg (k^2 + 4 * (k - 3)), Real.sq_sqrt (show 0 ≤ k ^ 2 + 4 * (k - 3) by nlinarith)]
    have h2 : (k - Real.sqrt (k^2 + 4 * (k - 3))) / 2 < 1 := by
      nlinarith [Real.sqrt_nonneg (k^2 + 4 * (k - 3)), Real.sq_sqrt (show 0 ≤ k ^ 2 + 4 * (k - 3) by nlinarith)]
    have h3 : 1 < (k + Real.sqrt (k^2 + 4 * (k - 3)) ) / 2 := by
      nlinarith [Real.sqrt_nonneg (k^2 + 4 * (k - 3)), Real.sq_sqrt (show 0 ≤ k ^ 2 + 4 * (k - 3) by nlinarith)]
    have h4 : (k + Real.sqrt (k^2 + 4 * (k - 3)) ) / 2 < 2 := by
      nlinarith [Real.sqrt_nonneg (k^2 + 4 * (k - 3)), Real.sq_sqrt (show 0 ≤ k ^ 2 + 4 * (k - 3) by nlinarith)]
    use (k - Real.sqrt (k^2 + 4 * (k - 3))) / 2
    use (k + Real.sqrt (k^2 + 4 * (k - 3))) / 2
    constructor
    · -- Show that x ∈ (0, 1)
      constructor
      · -- Show that 0 < x
        nlinarith
      · -- Show that x < 1
        nlinarith
    constructor
    · -- Show that y ∈ (1, 2)
      constructor
      · -- Show that 1 < y
        nlinarith
      · -- Show that y < 2
        nlinarith
    constructor
    · -- Show that x^2 -k*x -k +3=0
      nlinarith [Real.sqrt_nonneg (k ^ 2 + 4 * (k - 3)), Real.sq_sqrt (show 0 ≤ k ^ 2 + 4 * (k - 3) by nlinarith)]
    · -- Show that y^2 -k*y -k +3=0
      nlinarith [Real.sqrt_nonneg (k ^ 2 + 4 * (k - 3)), Real.sq_sqrt (show 0 ≤ k ^ 2 + 4 * (k - 3) by nlinarith)]