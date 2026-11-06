import Mathlib

theorem algebra_307 (a b c : ℝ) (h : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    (2 * a - b - c) / (a ^ 2 - a * b - a * c + b * c) +
    (2 * b - c - a) / (b ^ 2 - b * c - a * b + a * c) +
    (2 * c - a - b) / (c ^ 2 - a * c - b * c + a * b) = 0 := by

  have h11 : a ^ 2 - a * b - a * c + b * c = (a - b) * (a - c) := by
    ring
  have h22 : b ^ 2 - b * c - a * b + a * c = (b - a) * (b - c) := by
    ring
  have h33 : c ^ 2 - a * c - b * c + a * b = (c - b) * (c - a) := by
    ring
  have h1 : a - b ≠ 0 := by
    intro h1
    apply h.left
    linarith
  have h2 : b - c ≠ 0 := by
    intro h2
    apply h.right.left
    linarith
  have h3 : a - c ≠ 0 := by
    intro h3
    apply h.right.right
    linarith
  have h4 : b - a ≠ 0 := by
    intro h4
    apply h1
    linarith
  have h5 : c - b ≠ 0 := by
    intro h5
    apply h2
    linarith
  have h6 : c - a ≠ 0 := by
    intro h6
    apply h3
    linarith

  have eq1 : (2 * a - b - c) / (a ^ 2 - a * b - a * c + b * c) = (2 * a - b - c) / ((a - b) * (a - c)) := by
    rw [h11]
  have eq2 : (2 * b - c - a) / (b ^ 2 - b * c - a * b + a * c) = (2 * b - c - a) / ((b - a) * (b - c)) := by
    rw [h22]
  have eq3 : (2 * c - a - b) / (c ^ 2 - a * c - b * c + a * b) = (2 * c - a - b) / ((c - b) * (c - a)) := by
    rw [h33]
  rw [eq1, eq2, eq3]

  have eq4 : (2 * a - b - c) / ((a - b) * (a - c)) = 1 / (a - c) + 1 / (a - b) := by
    field_simp [(show a - b ≠ 0 by tauto), (show a - c ≠ 0 by tauto)]
      <;> ring
  have eq5 : (2 * b - c - a) / ((b - a) * (b - c)) = 1 / (b - c) + 1 / (b - a) := by
    field_simp [(show b - a ≠ 0 by tauto), (show b - c ≠ 0 by tauto)]
      <;> ring
  have eq6 : (2 * c - a - b) / ((c - b) * (c - a)) = 1 / (c - b) + 1 / (c - a) := by
    field_simp [(show c - b ≠ 0 by tauto), (show c - a ≠ 0 by tauto)]
      <;> ring
  rw [eq4, eq5, eq6]

  field_simp [(show a - b ≠ 0 by tauto), (show b - a ≠ 0 by tauto),
              (show a - c ≠ 0 by tauto), (show c - a ≠ 0 by tauto),
              (show b - c ≠ 0 by tauto), (show c - b ≠ 0 by tauto)]
  <;> ring