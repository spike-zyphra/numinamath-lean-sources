import Mathlib

theorem algebra_15352 :
    (fun x : ℝ => x^2 + 5 * x + 6 ) '' {x : ℝ | x^2 - 5 * x + 6 < 0} = Set.Ioo 20 30
    := by
  have h1 : {x : ℝ | x^2 - 5 * x + 6 < 0} = Set.Ioo (2 : ℝ) (3 : ℝ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · -- Assume h : x^2 - 5 * x + 6 < 0
      intro h
      have h2 : x ^ 2 - 5 * x + 6 < (0 : ℝ) := by linarith
      constructor
      · -- Show that 2 < x
        nlinarith [sq_pos_of_pos (show (0 : ℝ) < x - 2 by nlinarith)]
      · -- Show that x < 3
        nlinarith [sq_pos_of_pos (show (0 : ℝ) < 3 - x by nlinarith)]
    · -- Assume h : 2 < x ∧ x < 3
      rintro ⟨h1, h2⟩
      have h3 : x ^ 2 - 5 * x + 6 < (0 : ℝ) := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3)]
      linarith
  rw [h1]
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- First, prove the forward direction: if y is in the image, then y ∈ (20, 30)
    rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    constructor
    · -- Show that 20 < x ^ 2 + 5 * x + 6
      nlinarith [sq_pos_of_pos (show (0 : ℝ) < x - 2 by linarith), sq_nonneg (x - 3)]
    · -- Show that x ^ 2 + 5 * x + 6 < 30
      nlinarith [sq_pos_of_pos (show (0 : ℝ) < 3 - x by linarith), sq_nonneg (x - 2)]
  · -- Now prove the reverse: if y ∈ (20, 30), then there exists x ∈ (2, 3) s.t. f(x) = y
    rintro ⟨hy1, hy2⟩
    use (-5 + Real.sqrt (1 + 4 * y)) / 2
    constructor
    · -- Show that x ∈ (2, 3)
      constructor
      · -- Show that 2 < (-5 + Real.sqrt (1 + 4 * y)) / 2
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 1 + 4 * y by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + 4 * y : ℝ) by linarith)]
      · -- Show that (-5 + Real.sqrt (1 + 4 * y)) / 2 < 3
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 1 + 4 * y by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + 4 * y : ℝ) by linarith)]
    · -- Show that ((-5 + Real.sqrt (1 + 4 * y)) / 2)^2 + 5 * ((-5 + Real.sqrt (1 + 4 * y)) / 2) + 6 = y
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 1 + 4 * y by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + 4 * y : ℝ) by linarith)]