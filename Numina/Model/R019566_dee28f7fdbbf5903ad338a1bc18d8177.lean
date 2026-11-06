import Mathlib

theorem algebra_185436 (p q : ℝ) :
    ∃ a b c d e f : ℝ,
      (X^2 + a*X + b) * (X^2 + c*X + d) =
      X^4 + p*X^2 + q := by
  by_cases h1 : p ^ 2 - 4 * q ≥ 0
  · -- If p^2 - 4*q >= 0, let b and d be real roots of t^2 - p t + q =0.
    have h2 : ∃ s : ℝ, s ≥ 0 ∧ s ^ 2 = p ^ 2 - 4 * q := by
      use Real.sqrt (p ^ 2 - 4 * q)
      constructor
      · apply Real.sqrt_nonneg
      · rw [Real.sq_sqrt]
        linarith
    rcases h2 with ⟨s, hs1, hs2⟩
    use 0
    use (p + s) / 2
    use 0
    use (p - s) / 2
    use 0
    use 0
    have h3 : (p + s) / 2 + (p - s) / 2 = p := by
      ring
    have h4 : ((p + s) / 2) * ((p - s) / 2) = q := by
      nlinarith
    have eq1 : (X ^ 2 + (0 : ℝ) * X + ((p + s) / 2)) * (X ^ 2 + (0 : ℝ) * X + ((p - s) / 2)) = X^4 + p * X^2 + q := by
      calc
        (X ^ 2 + (0 : ℝ) * X + ((p + s) / 2)) * (X ^ 2 + (0 : ℝ) * X + ((p - s) / 2))
          = (X^2 + ((p + s) / 2)) * (X^2 + ((p - s) / 2)) := by ring
        _ = X^4 + ( ((p + s) / 2) + ((p - s) / 2) ) * X ^ 2 + ((p + s) / 2) * ((p - s) / 2) := by ring
        _ = X^4 + p * X^2 + q := by
          rw [h3, h4]
          <;> nlinarith
    simpa using eq1
  · -- If p^2 - 4*q < 0
    push_neg at h1
    have h5 : p ^ 2 < 4 * q := by linarith
    have h5' : Real.sqrt q ≥ 0 := by apply Real.sqrt_nonneg
    have h5'' : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (by nlinarith)
    have h6 : 2 * Real.sqrt q - p > 0 := by
      nlinarith [sq_nonneg (p + 2 * Real.sqrt q), sq_nonneg (Real.sqrt q), sq_nonneg (p - 2 * Real.sqrt q), Real.sqrt_nonneg q, sq_nonneg (p - 2 * Real.sqrt q)]
    use Real.sqrt (2 * Real.sqrt q - p)
    use Real.sqrt q
    use -Real.sqrt (2 * Real.sqrt q - p)
    use Real.sqrt q
    use 0
    use 0
    have h5''' : (Real.sqrt (2 * Real.sqrt q - p)) ^ 2 = 2 * Real.sqrt q - p := Real.sq_sqrt (by linarith)
    have eq1 : (X ^ 2 + (Real.sqrt (2 * Real.sqrt q - p) : ℝ) * X + (Real.sqrt q : ℝ)) * (X ^ 2 + (-Real.sqrt (2 * Real.sqrt q - p) : ℝ) * X + (Real.sqrt q : ℝ)) = X^4 + p * X^2 + q := by
      calc
        (X ^ 2 + (Real.sqrt (2 * Real.sqrt q - p) : ℝ) * X + (Real.sqrt q : ℝ)) * (X ^ 2 + (-Real.sqrt (2 * Real.sqrt q - p) : ℝ) * X + (Real.sqrt q : ℝ))
          = (X ^ 2 + (Real.sqrt q : ℝ)) ^ 2 - ( (Real.sqrt (2 * Real.sqrt q - p) : ℝ) * X ) ^ 2 := by ring
        _ = (X^4 + (2 * (Real.sqrt q : ℝ) ) * X^2 + ( (Real.sqrt q : ℝ) ) ^ 2 ) - ( (Real.sqrt (2 * Real.sqrt q - p) : ℝ) ^ 2 * X ^ 2 ) := by ring
        _ = X^4 + p * X ^ 2 + q := by
          rw [h5''']
          rw [h5'']
          <;> nlinarith [Real.sqrt_nonneg (2 * Real.sqrt q - p), Real.sqrt_nonneg q]
    simpa using eq1