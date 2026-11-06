import Mathlib

theorem algebra_246316 (a b c : ℝ) :
    max (max ((a + b + c)^2 - 9 * a * b) ((a + b + c)^2 - 9 * b * c)) ((a + b + c)^2 - 9 * c * a) ≥ 0 := by
  by_contra h
  push_neg at h
  have h1 : (a + b + c) ^ 2 - 9 * a * b < 0 := by
    have h2 : (a + b + c) ^ 2 - 9 * a * b ≤ max (max ((a + b + c) ^ 2 - 9 * a * b) ((a + b + c) ^ 2 - 9 * b * c)) ((a + b + c) ^ 2 - 9 * c * a) := by
      simp [le_max_iff]
      <;> try { linarith }
    linarith 
  have h2 : (a + b + c) ^ 2 - 9 * b * c < 0 := by
    have h3 : (a + b + c) ^ 2 - 9 * b * c ≤ max (max ((a + b + c) ^ 2 - 9 * a * b) ((a + b + c) ^ 2 - 9 * b * c)) ((a + b + c) ^ 2 - 9 * c * a) := by
      simp [le_max_iff]
      <;> try { linarith }
    linarith 
  have h3 : (a + b + c) ^ 2 - 9 * c * a < 0 := by
    have h4 : (a + b + c) ^ 2 - 9 * c * a ≤ max (max ((a + b + c) ^ 2 - 9 * a * b) ((a + b + c) ^ 2 - 9 * b * c)) ((a + b + c) ^ 2 - 9 * c * a) := by
      simp [le_max_iff]
      <;> try { linarith }
    linarith 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a / 2 - b / 2 - c / 2), sq_nonneg (-a / 2 + b / 2 - c / 2), sq_nonneg (-a / 2 - b / 2 + c / 2)]