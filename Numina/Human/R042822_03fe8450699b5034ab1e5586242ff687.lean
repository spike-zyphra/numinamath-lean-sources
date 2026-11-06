import Mathlib

theorem algebra_303046 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a + b + c = a * b * c) :
    ((1 - b ^ 2) * (1 - c ^ 2)) / (b * c) + ((1 - a ^ 2) * (1 - c ^ 2)) / (a * c) +
    ((1 - a ^ 2) * (1 - b ^ 2)) / (a * b) = 4 := by
-- have the same denominator
  have eq1 : ((1 - b^2) * (1 - c^2)) / (b * c) + ((1 - a^2) * (1 - c^2)) / (a * c) +
    ((1 - a^2) * (1 - b^2)) / (a * b) = 
    (a * (1 - b^2) * (1 - c^2) + b * (1 - a^2) * (1 - c^2) + c * (1 - a^2) * (1 - b^2)) / (a * b * c) := by 
    field_simp [mul_ne_zero_iff.2 (⟨ha, hb⟩), mul_ne_zero_iff.2 (⟨ha, hc⟩), mul_ne_zero_iff.2 (⟨hb, hc⟩)]
    ring
--easy to simplify
  have eq2 : a * (1 - b^2) * (1 - c^2) + b * (1 - a^2) * (1 - c^2) + c * (1 - a^2) * (1 - b^2) = 4 * (a * b * c) := by 
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      h]

  rw [eq1]
  have h2 : a * b * c ≠ 0 := by 
    apply mul_ne_zero
    apply mul_ne_zero
    · exact ha
    · exact hb
    · exact hc
  field_simp [h2]
  linarith [eq2]