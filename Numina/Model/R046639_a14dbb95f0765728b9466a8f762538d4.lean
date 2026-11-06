import Mathlib

theorem algebra_248579 {a b c d : ℝ}
  (ha : a ≠ b)
  (h1 : 3 * c - 2 * d ≠ 0)
  (h2 : 3 * c + 2 * d ≠ 0)
  (h3 : a ^ 2 + b ^ 2 ≠ 0)
  (h4 : a - b - c ≠ 0)
  (h5 : a + b + c ≠ 0)
  (h6 : a + b - c ≠ 0)
  (h7 : a - b + c ≠ 0) :
  (3 * a ^ 4 * c + 2 * a ^ 4 * d - 3 * b ^ 4 * c - 2 * b ^ 4 * d) /
    ((9 * c ^ 2 * (a - b) - 4 * d ^ 2 * (a - b)) * ((a + b) ^ 2 - 2 * a * b)) =
    (a + b) / (3 * c - 2 * d) ∧
  (a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * a * c + 2 * b * c) /
    (a ^ 2 - b ^ 2 - c ^ 2 - 2 * b * c) =
    (a + b + c) / (a - b - c) ∧
  (a ^ 2 - 3 * a * b + a * c + 2 * b ^ 2 - 2 * b * c) /
    (a ^ 2 - b ^ 2 + 2 * b * c - c ^ 2) =
    (a - 2 * b) / (a + b - c) := by 

  constructor
  · -- Prove the first equality
    have eq1 : (3 * a ^ 4 * c + 2 * a ^ 4 * d - 3 * b ^ 4 * c - 2 * b ^ 4 * d) =
      (3 * c + 2 * d) * (a - b) * (a + b) * (a ^ 2 + b ^ 2) := by
      ring
    have eq2 : (9 * c ^ 2 * (a - b) - 4 * d ^ 2 * (a - b)) * ((a + b) ^ 2 - 2 * a * b) =
        (a - b) * (3 * c - 2 * d) * (3 * c + 2 * d) * (a ^ 2 + b ^ 2) := by
      ring_nf
    rw [eq1, eq2]
    have h8 : a - b ≠ 0 := by
      intro h'
      apply ha
      linarith
    have h9 : a ^ 2 + b ^ 2 ≠ 0 := h3
    have h10 : 3 * c + 2 * d ≠ 0 := h2
    field_simp [(show (a - b : ℝ) ≠ 0 by assumption), 
      (show (3 * c - 2 * d : ℝ) ≠ 0 by assumption), 
      (show (3 * c + 2 * d : ℝ) ≠ 0 by assumption), 
      (show (a ^ 2 + b ^ 2 : ℝ) ≠ 0 by assumption)]
    <;> ring
  constructor
  · -- Prove the second equality
    have eq1 : (a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * a * c + 2 * b * c) = (a + b + c) ^ 2 := by
      ring
    have eq2 : (a ^ 2 - b ^ 2 - c ^ 2 - 2 * b * c) = (a - b - c) * (a + b + c) := by 
      ring
    rw [eq1, eq2]
    have h11 : a + b + c ≠ 0 := h5
    have h12 : a - b - c ≠ 0 := h4
    field_simp [(show (a + b + c : ℝ) ≠ 0 by assumption), 
      (show (a - b - c : ℝ) ≠ 0 by assumption)]
    <;> ring
  · -- Prove the third equality
    have eq1 : (a ^ 2 - 3 * a * b + a * c + 2 * b ^ 2 - 2 * b * c) = (a - 2 * b) * (a - b + c) := by 
      ring
    have eq2 : (a ^ 2 - b ^ 2 + 2 * b * c - c ^ 2) = (a - b + c) * (a + b - c) := by 
      ring
    rw [eq1, eq2]
    have h13 : a - b + c ≠ 0 := h7
    have h14 : a + b - c ≠ 0 := h6
    field_simp [(show (a - b + c : ℝ) ≠ 0 by assumption), 
      (show (a + b - c : ℝ) ≠ 0 by assumption)]
    <;> ring