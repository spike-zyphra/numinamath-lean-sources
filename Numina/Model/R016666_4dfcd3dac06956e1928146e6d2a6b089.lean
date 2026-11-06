import Mathlib

theorem number_theory_185162 {A B : ℕ} (hA : A < 100000000) (hB : B < 100000000)
    (hAB : A = 10 * B + (B % 10)) (hB1 : Nat.Coprime B 12) (hB2 : B > 44444444) :
    A = 14444446 ∨ A = 99999998 := by
  -- From the equation $A = 10 * B + (B % 10)$ we have $A \geq 10 * B$ because $B % 10 \geq 0$.
  have h1 : A ≥ 10 * B := by 
    omega
  have h2 : B < 10000000 := by
    by_contra h
    push_neg at h
    have h3 : 10 * B ≥ 10 * 10000000 := by
      nlinarith
    have h4 : A ≥ 100000000 := by
      linarith [h1, h3]
    omega
  omega