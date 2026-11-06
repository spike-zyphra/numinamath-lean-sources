import Mathlib

theorem algebra_107159 (a : ℕ → ℕ) (ha : ∀ n, a (n + 2) = a n + a (n + 1))
    (ha0 : a 0 ≠ 0) (ha1 : a 1 ≠ 0) (h7 : a 6 = 42) (h9 : a 8 = 110) :
    a 3 = 10 := by
  have eq1 : a 2 = a 0 + a 1 := by
    apply ha 0
  have eq2 : a 3 = a 1 + a 2 := by
    apply ha 1
  have eq3 : a 4 = a 2 + a 3 := by
    apply ha 2
  have eq4 : a 5 = a 3 + a 4 := by
    apply ha 3
  have eq5 : a 6 = a 4 + a 5 := by
    apply ha 4
  have eq6 : a 7 = a 5 + a 6 := by
    apply ha 5
  have eq7 : a 8 = a 6 + a 7 := by
    apply ha 6
  rw [eq1] at eq2
  rw [eq2] at eq3
  rw [eq3] at eq4
  rw [eq4] at eq5
  rw [eq5] at h7
  rw [eq6] at eq7
  rw [eq7] at h9
  omega