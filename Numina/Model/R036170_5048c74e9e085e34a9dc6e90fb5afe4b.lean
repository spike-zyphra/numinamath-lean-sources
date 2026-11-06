import Mathlib
open Real

theorem inequalities_601402 (x y z : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) (hz : z ≤ 0)
    (h : x^2 + y^2 + z^2 ≤ 3) :
    27 + 36 * x * y * z ≥ 7 * (x + y + z) * (y * z + z * x + x * y) ∧
    (27 + 36 * x * y * z = 7 * (x + y + z) * (y * z + z * x + x * y) ↔ x = 1 ∧ y = 1 ∧ z = 1) := by
  constructor
  · -- First part: inequality
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z + 1),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      mul_nonneg (show 0 ≤ -x by linarith) (show 0 ≤ -y by linarith), 
      mul_nonneg (show 0 ≤ -x by linarith) (show 0 ≤ -z by linarith), 
      mul_nonneg (show 0 ≤ -y by linarith) (show 0 ≤ -z by linarith)
    ]
  · -- Second part, the equality
    constructor
    · -- Forward direction: equality  means x=1 ∧ y=1 ∧ z=1
      intro he
      have h1 : x ≤ 0 := by linarith
      have h2 : y ≤ 0 := by linarith
      have h3 : z ≤ 0 := by linarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
        sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z + 1), 
        sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (z - 0),
        mul_nonneg (show 0 ≤ -x by linarith) (show 0 ≤ -y by linarith), 
        mul_nonneg (show 0 ≤ -x by linarith) (show 0 ≤ -z by linarith), 
        mul_nonneg (show 0 ≤ -y by linarith) (show 0 ≤ -z by linarith)
      ]
    · -- Backward direction: x=1 ∧ y=1 ∧ z=1 means  equality
      rintro ⟨rfl, rfl, rfl⟩
      norm_num