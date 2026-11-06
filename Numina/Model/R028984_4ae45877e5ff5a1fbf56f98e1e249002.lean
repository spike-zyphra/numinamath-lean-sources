import Mathlib

theorem algebra_7434 {k : ℝ} (hk : k > 1) (A B : ℝ × ℝ)
    (hA : A.1 = -2 * k / (k - 1)) (hB : B.2 = 2 * k)
    (hAB : (1 / 2) * |A.1| * |B.2| = 9) :
    k = 3 ∨ k = 3 / 2 := by

  have h1 : k - 1 > 0 := by linarith
  have hA1_neg : A.1 < 0 := by
    rw [hA]
    apply div_neg_of_neg_of_pos
    · -- -2*k < 0 when k > 0
      nlinarith
    · -- k - 1 > 0 from hk: k > 1
      linarith
  have hA1_abs : |A.1| = -A.1 := by
    rw [abs_of_neg hA1_neg]

  have hB2_pos : B.2 > 0 := by
    rw [hB]
    nlinarith
  have hB2_abs : |B.2| = B.2 := by
    rw [abs_of_pos hB2_pos]

  rw [hA1_abs, hB2_abs] at hAB
  rw [hA, hB] at hAB
  have eq1 : (1 / 2) * (-(-2 * k / (k - 1))) * (2 * k) = 2 * k ^ 2 / (k - 1) := by
    field_simp [(show k - 1 ≠ 0 by linarith)]
    <;> ring
  have eq2 : 2 * k ^ 2 / (k - 1) = 9 := by
    linarith [hAB, eq1]

  have eq3 : 2 * k ^ 2 = 9 * (k - 1) := by
    have h4 : k - 1 > 0 := h1
    field_simp [(show k - 1 ≠ 0 by linarith)] at eq2 ⊢
    nlinarith
  have eq6 : 2 * k ^ 2 - 9 * k + 9 = 0 := by linarith
  have eq7 : (k - 3) * (k - 3 / 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 eq7) with h8 h9
  · -- Case k - 3 = 0, so k = 3
    left
    linarith
  · -- Case k - 3/2 = 0, so k = 3/2
    right
    linarith