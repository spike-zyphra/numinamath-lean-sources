import Mathlib

theorem algebra_182317 {a b k : ℕ} (ha : a > 0) (hb : b > 0)
    (h1 : 5 * a + 3 * b = k * a) (h2 : 4 * a + 6 * b = k * b) :
    k = 9 ∧ a < b := by
  have eq3 : 3 * b ^ 2 = a * b + 4 * a ^ 2 := by
    have h5 : (k : ℕ) * (a : ℕ) = 5 * a + 3 * b := by linarith
    have h6 : (k : ℕ) * (b : ℕ) = 4 * a + 6 * b := by linarith
    nlinarith [h1, h2, mul_pos (show 0 < a by linarith) (show 0 < b by linarith)]
  have h8 : k = 9 := by
    have h4 : a > 0 := ha
    have h5 : b > 0 := hb
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, h1, h2, mul_pos (show 0 < a by linarith) (show 0 < b by linarith)]
  have h9 : a < b := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, h1, h2, mul_pos (show 0 < a by linarith) (show 0 < b by linarith)]
  exact ⟨h8, h9⟩