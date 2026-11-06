import Mathlib

theorem algebra_188896 (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a * (b + c) = 36) (h2 : b * (a + c) = 50) (h3 : c * (a + b) = 56) :
    a * b * c = 105 := by
  have eq1 : a * b + a * c = 36 := by
    linarith
  have eq2 : a * b + b * c = 50 := by
    linarith
  have eq3 : a * c + b * c = 56 := by
    linarith
  have h4 : a * b + a * c + b * c = 71 := by
    linarith [eq1, eq2, eq3]
  have hbc : b * c = 35 := by
    linarith [eq1, h4]
  have hac : a * c = 21 := by
    linarith [eq2, h4]
  have hab : a * b = 15 := by
    linarith [eq3, h4]
  have h5 : a * b * c ≥ 0 := by
    apply mul_nonneg 
    apply mul_nonneg 
    all_goals
    assumption
  have h8 : (a * b * c) ^ 2 = 11025 := by
    calc
      (a * b * c) ^ 2 = (a * b) * (a * c) * (b * c) := by
        ring_nf
        <;> nlinarith
      _ = 15 * 21 * 35 := by
        rw [hab, hac, hbc]
        all_goals nlinarith
      _ = 11025 := by norm_num
  nlinarith [sq_nonneg (a * b * c), h8]