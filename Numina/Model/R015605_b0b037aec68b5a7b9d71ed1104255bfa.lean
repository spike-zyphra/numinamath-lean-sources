import Mathlib

open Real Set

theorem algebra_12681 : range (fun x => (x ^ 2 + 2 * x + 3) / (x ^ 2 + 4 * x + 5)) = {y | 2 - sqrt 2 ≤ y ∧ y ≤ 2 + sqrt 2} := by
  ext y
  simp only [mem_range, Set.mem_setOf_eq]
  constructor
  · -- First direction: if y in range then bounds
    rintro ⟨x, hx⟩
    have h1 : x ^ 2 + 4 * x + 5 > 0 := by
      nlinarith [sq_nonneg (x + 2)]
    have eq1 : (x ^ 2 + 2 * x + 3) = y * (x ^ 2 + 4 * x + 5) := by
      field_simp [h1] at hx ⊢
      nlinarith
    have eq2 : (y - 1) * x^2 + (4 * y - 2) * x + (5 * y - 3) = 0 := by
      nlinarith
    have h4 : (4 * y - 2) ^ 2 - 4 * (y - 1) * (5 * y - 3) ≥ 0 := by
      nlinarith [sq_nonneg ((y - 1) * x + (2 * y - 1)), sq_nonneg (x * (y - 1) + (2 * y - 1)), sq_nonneg (x * (y - 1) - (2 * y - 1)), sq_nonneg (x), sq_nonneg (x + 2), sq_nonneg (y - 2)]
    have h5 : (4 * y - 2) ^ 2 - 4 * (y - 1) * (5 * y - 3) = -4 * (y - 2) ^ 2 + 8 := by
      nlinarith
      <;> ring_nf
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h6 : (y - 2) ^ 2 ≤ (2 : ℝ) := by
      nlinarith [h4, h5, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show that 2 - sqrt 2 ≤ y
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (y - 2)]
    · -- Show that y ≤ 2 + sqrt 2
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (y - 2)]
  · -- Second direction: invert (mem interval implies y in range)
    rintro ⟨hy1, hy2⟩
    by_cases h3 : y - 1 = 0
    · -- Case y = 1
      have hy : y = 1 := by linarith
      use -1
      norm_num [hy]
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Case y ≠ 1
      have h30 : (y - 1) ≠ 0 := by
        intro h31
        apply h3
        linarith
      have h11 : (4 * y - 2) ^ 2 - 4 * (y - 1) * (5 * y - 3) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (y - 2), sq_nonneg (y * (y - 2) - 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h30 : ∃ x : ℝ, (y - 1) * x^2 + (4 * y - 2) * x + (5 * y - 3) = 0 := by
        have h23 : ( (4 * y - 2) ^ 2 - 4 * (y - 1) * (5 * y - 3) ) ≥ 0 := h11
        use (- (4 * y - 2) + Real.sqrt ((4 * y - 2) ^ 2 - 4 * (y - 1) * (5 * y - 3)) ) / (2 * (y - 1))
        field_simp [h30]
        <;> nlinarith [Real.sqrt_nonneg ((4 * y - 2) ^ 2 - 4 * (y - 1) * (5 * y - 3)), Real.sq_sqrt (show (0 : ℝ) ≤ ((4 * y - 2) ^ 2 - 4 * (y - 1) * (5 * y - 3)) by nlinarith [h11, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]), sq_nonneg (y - 1), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rcases h30 with ⟨x, hx⟩
      use x
      have h1 : x ^ 2 + 4 * x + 5 > 0 := by
        nlinarith [sq_nonneg (x + 2)]
      field_simp [h1]
      nlinarith [h11]
      <;> try nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      <;> try nlinarith
      <;> try tauto
      <;> try linarith [h11, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]