import Mathlib

theorem algebra_298112 {a b c : ℝ} (ha : a ≠ 0) (A B C D : ℝ × ℝ)
    (hA : A.1 ^ 2 * a + b * A.1 + c = A.2) (hB : B.1 ^ 2 * a + b * B.1 + c = B.2)
    (hC : C.1 ^ 2 * a + b * C.1 + c = C.2) (hD : D.1 ^ 2 * a + b * D.1 + c = D.2)
    (hABCD : A.1 + D.1 = B.1 + C.1) :
    (A.1 - D.1) * (B.2 - C.2) = (A.2 - D.2) * (B.1 - C.1) := by
  have eq1 : A.2 - D.2 = a * (A.1 - D.1) * (A.1 + D.1) + b * (A.1 - D.1) := by
    have h1 : A.1 ^ 2 * a + b * A.1 + c = A.2 := by linarith
    have h2 : D.1 ^ 2 * a + b * D.1 + c = D.2 := by linarith
    calc
      A.2 - D.2 = (A.1 ^ 2 * a + b * A.1 + c) - (D.1 ^ 2 * a + b * D.1 + c) := by linarith
      _ = a * (A.1 ^ 2 - D.1 ^ 2) + b * (A.1 - D.1) := by ring_nf
      _ = a * ((A.1 - D.1) * (A.1 + D.1)) + b * (A.1 - D.1) := by
        rw [show A.1 ^ 2 - D.1 ^ 2 = (A.1 - D.1) * (A.1 + D.1) by ring]
      _ = a * (A.1 - D.1) * (A.1 + D.1) + b * (A.1 - D.1) := by ring
  have eq2 : B.2 - C.2 = a * (B.1 - C.1) * (B.1 + C.1) + b * (B.1 - C.1) := by
    have h1 : B.1 ^ 2 * a + b * B.1 + c = B.2 := by linarith
    have h2 : C.1 ^ 2 * a + b * C.1 + c = C.2 := by linarith
    calc
      B.2 - C.2 = (B.1 ^ 2 * a + b * B.1 + c) - (C.1 ^ 2 * a + b * C.1 + c) := by linarith
      _ = a * (B.1 ^ 2 - C.1 ^ 2) + b * (B.1 - C.1) := by ring_nf
      _ = a * ((B.1 - C.1) * (B.1 + C.1)) + b * (B.1 - C.1) := by
        rw [show B.1 ^ 2 - C.1 ^ 2 = (B.1 - C.1) * (B.1 + C.1) by ring]
      _ = a * (B.1 - C.1) * (B.1 + C.1) + b * (B.1 - C.1) := by ring
  have h1 : A.1 + D.1 = B.1 + C.1 := hABCD
  rw [eq1, eq2]
  -- rewrite $B_1 + C_1 = A_1 + D_1$
  have h3 : B.1 + C.1 = A.1 + D.1 := by linarith
  rw [h3]
  ring