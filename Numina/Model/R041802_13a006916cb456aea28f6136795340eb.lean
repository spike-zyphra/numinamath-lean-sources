import Mathlib

theorem algebra_604692 : IsGreatest {a : ℝ | (∃ x y z : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = 1 ∧ a = (x - y * z) ^ 2 + (y - z * x) ^ 2 + (z - x * y) ^ 2)} 1 := by
  constructor
  · -- Show 1 is in the set
    use 0, 0, 1
    norm_num
  · -- Show that for all a in the set, a ≤ 1
    intro a ha
    rcases ha with ⟨x, y, z, hx0, h1, h2, h3, ha⟩
    have h4 : (x - y * z) ^ 2 + (y - z * x) ^ 2 + (z - x * y) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x - 0), sq_nonneg (y - x), sq_nonneg (z - y),
        mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y - x by linarith),
        mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z - y by linarith),
        mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ 1 - z by linarith),
        mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith),
        mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith),
        mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ 1 - z by linarith)]
    nlinarith