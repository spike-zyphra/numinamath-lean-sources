import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_195544 :
  {b : ℝ | ∀m, {(x, y) : ℝ×ℝ | x^2 + 2 * y^2 = 3} ∩ {(x, y) : ℝ×ℝ | y = m * x + b} ≠ ∅ } =
  Icc (-sqrt 6 / 2) (sqrt 6 / 2) := by
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- First direction: if b such that all m satisfy the intersection, then b in the interval
    intro h
    have h1 : ∀m : ℝ, {(x, y) : ℝ×ℝ | x^2 + 2 * y^2 = 3} ∩ {(x, y) : ℝ×ℝ | y = m * x + b} ≠ ∅ := h
    
    have h2 : b ≤ sqrt 6 / 2 := by
      by_contra h
      push_neg at h
      have h6' : ∃x y, x^2 + 2 * y^2 = 3 ∧ y = b := by
        have h5 := h1 0
        have h7 : {(x, y) : ℝ×ℝ | x^2 + 2 * y^2 = 3} ∩ {(x, y) : ℝ×ℝ | y = (0 : ℝ) * x + b} ≠ ∅ := h5
        have h9 : {(x, y) : ℝ×ℝ | x^2 + 2 * y^2 = 3} ∩ {(x, y) : ℝ×ℝ | y = (0 : ℝ) * x + b} = {(x, y) | x^2 + 2 * y^2 = 3 ∧ y = b} := by
          ext ⟨x, y⟩
          simp 
        have h6 := h7
        rw [h9] at h6
        have : ∃ x y, x^2 + 2 * y^2 = 3 ∧ y = b := by
          by_contra h
          push_neg at h
          have h2 : {(x, y) | x^2 + 2 * y^2 = 3 ∧ y = b} = ∅ := by
            ext ⟨x, y⟩
            simp
            all_goals aesop
          rw [h2] at h6
          simp at h6
        assumption
      rcases  h6' with ⟨x, y, h20, h21⟩
      have h4 : x^2 + 2 * y^2 = 3 := h20
      have h5 : y = b := by nlinarith
      rw [show y = b by linarith] at h4
      have h6 : x^2 = 3 - 2 * b^2 := by
        nlinarith
      have h7 : b ^ 2 ≤ (3 / 2 : ℝ) := by
        nlinarith [sq_nonneg x]
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    
    have h3 : b ≥ -sqrt 6 / 2 := by
      by_contra h
      push_neg at h
      have h6' : ∃x y, x^2 + 2 * y^2 = 3 ∧ y = b := by
        have h5 := h1 0
        have h7 : {(x, y) : ℝ×ℝ | x^2 + 2 * y^2 = 3} ∩ {(x, y) : ℝ×ℝ | y = (0 : ℝ) * x + b} ≠ ∅ := h5
        have h9 : {(x, y) : ℝ×ℝ | x^2 + 2 * y^2 = 3} ∩ {(x, y) : ℝ×ℝ | y = (0 : ℝ) * x + b} = {(x, y) | x^2 + 2 * y^2 = 3 ∧ y = b} := by
          ext ⟨x, y⟩
          simp 
        have h6 := h7
        rw [h9] at h6
        have : ∃ x y, x^2 + 2 * y^2 = 3 ∧ y = b := by
          by_contra h
          push_neg at h
          have h2 : {(x, y) | x^2 + 2 * y^2 = 3 ∧ y = b} = ∅ := by
            ext ⟨x, y⟩
            simp
            all_goals aesop
          rw [h2] at h6
          simp at h6
        assumption
      rcases  h6' with ⟨x, y, h20, h21⟩
      have h4 : x^2 + 2 * y^2 = 3 := h20
      have h5 : y = b := by nlinarith
      rw [show y = b by linarith] at h4
      have h6 : x^2 = 3 - 2 * b^2 := by
        nlinarith
      have h8 : b ^ 2 ≤ (3 / 2 : ℝ) := by
        nlinarith [sq_nonneg x]
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    constructor <;> linarith
  · -- Reverse direction: if b in the interval then all m satisfy the intersection
    rintro ⟨hb1, hb2⟩
    intro m
    have h1 :  {(x, y) : ℝ×ℝ | x^2 + 2 * y^2 = 3} ∩ {(x, y) : ℝ×ℝ | y = m * x + b} ≠ ∅ := by
      have h2 : ∃ x : ℝ, ∃ y : ℝ, x^2 + 2 * y^2 = 3 ∧ y = m * x + b := by
        have h3 : b ^ 2 ≤ (3 / 2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (b ^ 2 - 3 / 2), sq_nonneg (b - sqrt 6 / 2), sq_nonneg (b + sqrt 6 / 2)]
        use (-4 * m * b + Real.sqrt ((4 * m * b) ^ 2 - 4 * (1 + 2 * m ^ 2) * (2 * b ^ 2 - 3))) / (2 * (1 + 2 * m ^ 2))
        use m * ((-4 * m * b + Real.sqrt ((4 * m * b) ^ 2 - 4 * (1 + 2 * m ^ 2) * (2 * b ^ 2 - 3)) ) / (2 * (1 + 2 * m ^ 2)) ) + b
        constructor
        · -- Show that the point is in the ellipse
          field_simp
          ring_nf
          rw [Real.sq_sqrt (by
            nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (b ^ 2 - 3 / 2), sq_nonneg (b - sqrt 6 / 2), sq_nonneg (b + sqrt 6 / 2)]
          )]
          <;> nlinarith
        · -- Show that the point is on the line
          ring_nf
      simp [Set.ext_iff] at *
      tauto
    simpa using h1