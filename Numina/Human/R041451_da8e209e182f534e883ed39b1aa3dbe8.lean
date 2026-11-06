import Mathlib

theorem algebra_275744 (P Q R S : ℝ × ℝ)
    (hP : P = (2, 1)) (hR : R = (P + Q) / 2) (hS : S = (Q + R) / 2)
    (hS1 : S = (14, 7)) : Q = (18, 9) := by
  rw [hP] at hR
  rw [hR] at hS
  rw [hS1] at hS
  have eq1 := congr_arg Prod.fst hS
  have eq2 := congr_arg Prod.snd hS
  simp at eq1 eq2
  have Q1 : Q.1 = 18 := by linarith
  have Q2 : Q.2 = 9 := by linarith
  exact Prod.ext Q1 Q2