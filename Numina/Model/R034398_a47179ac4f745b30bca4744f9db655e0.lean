import Mathlib

def f (x : ℕ → ℕ) (n : ℕ) := (5 * x n + 2) % 19

theorem number_theory_5101 (x : ℕ → ℕ) (hx0 : x 0 = 6) (hxn : ∀ n, x (n + 1) = f x n) :
    x 9 = 6 ∧ (∀ n, x (n + 9) = x n) := by
  have hx1 : x 1 = (5 * x 0 + 2) % 19 := by
    simp [hxn, f]
  have hx2 : x 2 = (5 * x 1 + 2) % 19 := by
    simp [hxn, f]
  have hx3 : x 3 = (5 * x 2 + 2) % 19 := by
    simp [hxn, f]
  have hx4 : x 4 = (5 * x 3 + 2) % 19 := by
    simp [hxn, f]
  have hx5 : x 5 = (5 * x 4 + 2) % 19 := by
    simp [hxn, f]
  have hx6 : x 6 = (5 * x 5 + 2) % 19 := by
    simp [hxn, f]
  have hx7 : x 7 = (5 * x 6 + 2) % 19 := by
    simp [hxn, f]
  have hx8 : x 8 = (5 * x 7 + 2) % 19 := by
    simp [hxn, f]
  have hx9 : x 9 = (5 * x 8 + 2) % 19 := by
    simp [hxn, f]
  have hx1' : x 1 = 13 := by
    simp [hx1, hx0]
  have hx2' : x 2 = 10 := by
    simp [hx2, hx1']
  have hx3' : x 3 = 14 := by
    simp [hx3, hx2']
  have hx4' : x 4 = 15 := by
    simp [hx4, hx3']
  have hx5' : x 5 = 1 := by
    simp [hx5, hx4']
  have hx6' : x 6 = 7 := by
    simp [hx6, hx5']
  have hx7' : x 7 = 18 := by
    simp [hx7, hx6']
  have hx8' : x 8 = 16 := by
    simp [hx8, hx7']
  have hx9' : x 9 = 6 := by
    simp [hx9, hx8']
  constructor
  · exact hx9'
  · -- prove period length is 9
    intro n
    have eq1 : ∀ (n : ℕ), x (n + 9) = x n := by
      intro n
      induction n with
      | zero =>
        simp [hx9', hx0]
      | succ n ih =>
        have eq2 : x (n + 1 + 9) = x (n + 1) := by
          simp [hxn, f] at ih ⊢
          <;> omega
        simpa using eq2
    specialize eq1 n
    simpa using eq1