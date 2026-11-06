import Mathlib

theorem algebra_53874 {a b c d b1 b2 : ℤ} (h : a * d - b * c ≠ 0)
    (hb1 : (a * d - b * c) ∣ b1) (hb2 : (a * d - b * c) ∣ b2) :
    ∃ x y, a * x + b * y = b1 ∧ c * x + d * y = b2 := by
  rcases hb1 with ⟨m, hm⟩
  rcases hb2 with ⟨n, hn⟩
  use m * d - n * b
  use n * a - m * c
  constructor
  · -- Prove the first equation: a * x + b * y = b1
    rw [show b1 = (a * d - b * c) * m by linarith]
    ring
  · -- Prove the second equation: c * x + d * y = b2
    rw [show b2 = (a * d - b * c) * n by linarith]
    ring