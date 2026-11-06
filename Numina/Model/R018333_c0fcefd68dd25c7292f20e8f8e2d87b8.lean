import Mathlib

theorem algebra_146013 (x : ℝ) (hx : x ≠ -3 ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3 ∧ x ≠ 4) :
    ((x ^ 2 - 4 * x) / (5 * x - 5)) * ((x ^ 3 + 1) / (x ^ 2 + x) - 1) *
    ((1 - (3 * x - 3) / (x ^ 2 + x - 6)) * ((6 / (x + 3)) - (1 / (x - 2))) ^ (-1 : ℤ) - 1) ^ (-1 : ℤ) = x - 1 := by
  rcases hx with ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  have h5x5 : 5 * x - 5 ≠ 0 := by
    intro h
    apply hx4
    linarith
  have h5x6 : x * (x + 1) ≠ 0 := by
    apply mul_ne_zero
    · exact hx3
    · intro h
      apply hx2
      linarith
  have h5x7 : (x + 3) * (x - 2) ≠ 0 := by
    apply mul_ne_zero
    · intro h
      apply hx1
      linarith
    · intro h
      apply hx5
      linarith
  have h5x8 : x + 3 ≠ 0 := by
    intro h
    apply hx1
    linarith
  have h5x9 : x - 2 ≠ 0 := by
    intro h
    apply hx5
    linarith
  have h5x10 : x - 3 ≠ 0 := by
    intro h
    apply hx6
    linarith
  have h1 : (x ^ 2 - 4 * x) / (5 * x - 5) = x * (x - 4) / (5 * (x - 1)) := by
    have h5 : 5 * x - 5 = 5 * (x - 1) := by ring
    rw [h5]
    <;> ring
  have h2 : (x ^ 3 + 1) / (x ^ 2 + x) - 1 = (x - 1) ^ 2 / x := by
    have h5 : x ^ 2 + x = x * (x + 1) := by ring
    rw [h5]
    field_simp [(show x ≠ 0 by assumption), (show x + 1 ≠ 0 by intro h; apply hx2; linarith)]
    ring
  have h5 : 1 - (3 * x - 3) / (x ^ 2 + x - 6) = ((x - 3) * (x + 1)) / ((x + 3) * (x - 2)) := by
    have h6 : x ^ 2 + x - 6 = (x + 3) * (x - 2) := by ring
    rw [h6]
    field_simp [(show (x + 3) * (x - 2) ≠ 0 by assumption)]
    ring
  have h6 : ((6 / (x + 3)) - (1 / (x - 2))) ^ (-1 : ℤ) = ((x + 3) * (x - 2)) / (5 * (x - 3)) := by
    have h7 : ((6 / (x + 3)) - (1 / (x - 2))) = (5 * (x - 3)) / ((x + 3) * (x - 2)) := by
      field_simp [(show x + 3 ≠ 0 by assumption), (show x - 2 ≠ 0 by assumption)]
      ring
    rw [h7]
    rw [zpow_neg_one]
    field_simp [(show (x + 3) * (x - 2) ≠ 0 by assumption), (show x - 3 ≠ 0 by assumption)]
    <;> ring
  have h7 : (1 - (3 * x - 3) / (x ^ 2 + x - 6)) * ((6 / (x + 3)) - (1 / (x - 2))) ^ (-1 : ℤ) - 1 = (x - 4) / 5 := by
    rw [h5, h6]
    field_simp [(show (x + 3) * (x - 2) ≠ 0 by assumption), (show x - 3 ≠ 0 by assumption)]
    ring
  have h8 : ((1 - (3 * x - 3) / (x ^ 2 + x - 6)) * ((6 / (x + 3)) - (1 / (x - 2))) ^ (-1 : ℤ) - 1) ^ (-1 : ℤ) = 5 / (x - 4) := by
    rw [h7]
    rw [zpow_neg_one]
    field_simp [(show x - 4 ≠ 0 by intro h; apply hx7; linarith)]
  rw [h1, h2, h8]
  field_simp [(show x ≠ 0 by assumption), (show x - 1 ≠ 0 by intro h; apply hx4; linarith), (show x - 4 ≠ 0 by intro h; apply hx7; linarith)]
  ring