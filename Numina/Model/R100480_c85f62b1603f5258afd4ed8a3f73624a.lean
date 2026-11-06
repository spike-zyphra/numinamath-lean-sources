import Mathlib

def A (x : ℤ) := ∃ n : ℕ, n > 0 ∧ x = 2 * n - 1
def B (x : ℤ) := ∃ y : ℤ, A y ∧ x = 3 * y - 1

theorem number_theory_327801 :
    {x | A x} ∩ {x | B x} = ∅ := by
  ext x
  simp [A, B]
  <;> omega -- the arithmetic conditions lead to a contradiction which omega can find