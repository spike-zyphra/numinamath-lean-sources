import Mathlib

theorem inequalities_220028 (a b c A B C k : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hak : a + A = k) (hbk : b + B = k) (hck : c + C = k) :
    a * B + b * C + c * A ≤ k ^ 2 := by

  have h1 : A = k - a := by linarith
  have h2 : B = k - b := by linarith
  have h3 : C = k - c := by linarith

  rw [h1, h2, h3]

  nlinarith [sq_nonneg (k - a - b), sq_nonneg (k - b - c), sq_nonneg (k - c - a),
    sq_nonneg (a + b + c - k), 
    mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
    mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith),
    mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
    mul_nonneg (show 0 ≤ k - a by nlinarith) (show 0 ≤ k - b by nlinarith),
    mul_nonneg (show 0 ≤ k - b by nlinarith) (show 0 ≤ k - c by nlinarith),
    mul_nonneg (show 0 ≤ k - c by nlinarith) (show 0 ≤ k - a by nlinarith)
  ]