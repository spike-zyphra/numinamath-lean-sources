import Mathlib

open BigOperators Real Set


lemma lemma_1 (b : ℝ) : b^2 ≤ 3 / 2 ↔ b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := by
  simp only [mem_Icc]
  constructor
  ·
    intro h
    have h1 : -sqrt 6 / 2 ≤ b := by
      have h2 : b ^ 2 ≤ (3 / 2 : ℝ) := by linarith
      have h3 : sqrt (3 / 2 : ℝ) = sqrt 6 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      have h4 : -sqrt (3 / 2 : ℝ) ≤ b := by
        nlinarith [Real.sqrt_nonneg (3 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 / 2 : ℝ) by norm_num)]
      rw [h3] at h4
      linarith
    have h2 : b ≤ sqrt 6 / 2 := by
      have h2 : b ^ 2 ≤ (3 / 2 : ℝ) := by linarith
      have h3 : sqrt (3 / 2 : ℝ) = sqrt 6 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      have h4 : b ≤ sqrt (3 / 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (3 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 / 2 : ℝ) by norm_num)]
      rw [h3] at h4
      linarith
    constructor
    ·
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    ·
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  ·
    rintro ⟨h1, h2⟩
    have h3 : sqrt 6 ^ 2 = (6 : ℝ) := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (b)]


theorem algebra_298102 {b : ℝ} :
  (∀ m : ℝ, ∃ x y, x^2 + 2 * y^2 = 3 ∧ y = m * x + b) ↔
  b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := by
  constructor
  · -- Assume that for all m, there is an intersection point
    intro h
    have h1 : b ^ 2 ≤ 3 / 2 := by
      have h2 := h 0
      rcases h2 with ⟨x, y, h_eq1, h_eq2⟩
      have h_eq3 : y = b := by
        nlinarith
      rw [h_eq3] at h_eq1
      nlinarith [sq_nonneg x]
    have h2 : b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := by
      have h3 : b ^ 2 ≤ 3 / 2 := h1
      apply (lemma_1 b).mp
      linarith
    exact h2
  · -- Assume \( b \in \left[-\frac{\sqrt{6}}{2}, \frac{\sqrt{6}}{2}\right] \).
    intro h
    have h1 : b ^ 2 ≤ 3 / 2 := by
      have h2 : b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := h
      have h3 : -sqrt 6 / 2 ≤ b := by
        have h4 : b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := h
        simp only [mem_Icc] at h4
        linarith [h4.1]
      have h4 : b ≤ sqrt 6 / 2 := by
        have h5 : b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := h
        simp only [mem_Icc] at h5
        linarith [h5.2]
      have h5 : sqrt 6 ^ 2 = (6 : ℝ) := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg 6, sq_nonneg b, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    intro m
    have h3 : ∃ x : ℝ, (1 + 2 * m ^ 2) * x ^ 2 + 4 * m * b * x + (2 * b ^ 2 - 3) = 0 := by
      have h4 : (24 * m ^ 2 - 8 * b ^ 2 + 12) ≥ 0 := by
        nlinarith [h1]
      use (-4 * m * b + Real.sqrt (24 * m ^ 2 - 8 * b ^ 2 + 12)) / (2 * (1 + 2 * m ^ 2))
      field_simp
      nlinarith [Real.sqrt_nonneg (24 * m ^ 2 - 8 * b ^ 2 + 12), Real.sq_sqrt (show 0 ≤ (24 * m ^ 2 - 8 * b ^ 2 + 12 : ℝ) by linarith [h4]
      )
      ]
    rcases h3 with ⟨x, hx⟩
    use x
    use m * x + b
    constructor
    · -- Show that x^2 + 2 * y^2 = 3
      nlinarith [hx]
    · -- Show that y = m * x + b
      rfl