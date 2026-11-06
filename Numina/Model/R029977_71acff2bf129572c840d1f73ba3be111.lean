import Mathlib


lemma lemma_1 (a : ℝ) (ha : a ≠ 0) (h : a / 3 - 3 / a = 4) :
    a ^ 2 / 9 + 9 / a ^ 2 = 18 := by
  have h1 : a / 3 - 3 / a = 4 := h
  have h2 : (a / 3 - 3 / a) ^ 2 = 16 := by
    rw [h1]
    norm_num
  have h3 : (a / 3 - 3 / a) ^ 2 = a ^ 2 / 9 - 2 + 9 / a ^ 2 := by
    field_simp
    ring
  rw [h3] at h2
  linarith


theorem algebra_213290 {a : ℝ} (ha : a ≠ 0) (h : a / 3 - 3 / a = 4) :
    (a^12 + 729^2) / (729 * a^6) = 5778 := by
  have h1 : a ^ 2 / 9 + 9 / a ^ 2 = 18 := by
    apply lemma_1 a ha h

  have eq1 : (a ^ 12 + 729 ^ 2) / (729 * a ^ 6) = a ^ 6 / 729 + 729 / a ^ 6 := by
    field_simp
    ring
  rw [eq1]

  have h2 : a ^ 6 / 729 + 729 / a ^ 6 = (a ^ 2 / 9 + 9 / a ^ 2) ^ 3 - 3 * (a ^ 2 / 9 + 9 / a ^ 2) * ( (a ^ 2 / 9:ℝ ) * (9 / a ^ 2) ) := by
    field_simp
    ring

  have h3 : (a ^ 2 / 9:ℝ ) * (9 / a ^ 2) = 1 := by
    field_simp
    <;> nlinarith
  
  rw [h2]
  rw [h3]
  rw [h1]
  all_goals
    norm_num