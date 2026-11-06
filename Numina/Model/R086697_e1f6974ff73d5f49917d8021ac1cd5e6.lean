import Mathlib

theorem algebra_265778 (P Q : ℝ × ℝ) (hP : P.2 = 5 * P.1 + 3) (hQ : Q = (3, -2)) :
    ∃ M, M = ((P.1 + Q.1) / 2, (P.2 + Q.2) / 2) ∧ M.2 = 5 * M.1 - 7 := by 
  use ((P.1 + Q.1) / 2, (P.2 + Q.2) / 2)
  constructor
  · -- Show that M is indeed the midpoint
    rfl
  · -- Now we need to prove that M.2 = 5 * M.1 - 7
    rw [hQ] at *
    simp [hP]
    <;> ring_nf <;> linarith