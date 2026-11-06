import Mathlib

theorem algebra_124675 {a1 a2 b1 b2 : ℤ} (P1 P2 : ℤ → ℤ)
    (hP1 : P1 = fun x => x^2 + a1 * x + b1)
    (hP2 : P2 = fun x => x^2 + a2 * x + b2)
    (ha1 : a1 ≠ a2)
    (hmn : ∃ m n : ℤ, m ≠ n ∧ P1 m = P2 n ∧ P2 m = P1 n) :
    Even (a1 - a2) := by
  rcases hmn with ⟨m, n, hmn1, hp1, hp2⟩
  have eq1 : m ^ 2 + a1 * m + b1 = n ^ 2 + a2 * n + b2 := by
    simp [hP1, hP2] at hp1
    linarith
  have eq2 : m ^ 2 + a2 * m + b2 = n ^ 2 + a1 * n + b1 := by
    simp [hP1, hP2] at hp2
    linarith
  -- Add the two equations together
  -- m^2 + a1*m + b1 + m^2 + a2*m + b2 = n^2 + a2*n + b2 + n^2 + a1*n + b1
  -- 2*m^2 + (a1 + a2)*m + (b1 + b2) = 2*n^2 + (a1 + a2)*n + (b1 + b2)
  -- 2*m^2 + (a1 + a2)*m = 2*n^2 + (a1 + a2)*n
  have eq3 : 2 * (m ^ 2) + (a1 + a2) * m = 2 * (n ^ 2) + (a1 + a2) * n := by
    linarith [eq1, eq2]
  -- Rearranged:
  -- 2*m^2 - 2*n^2 + (a1 + a2)*(m - n) = 0
  -- = 2*(m - n)*(m + n) + (a1 + a2)*(m - n) = 0
  -- = (m - n)*(2*(m + n) + (a1 + a2)) = 0
  have eq4 : (m - n) * (2 * (m + n) + (a1 + a2)) = 0 := by
    ring_nf at eq3 ⊢
    linarith
  cases' (mul_eq_zero.mp eq4) with h h'
  · -- Case where h : m - n = 0
    exfalso
    apply hmn1
    omega
  · -- Case where h' : 2*(m + n) + (a1 + a2) = 0
    have eq5 : (a1 + a2) % 2 = 0 := by
      omega
    have eq6 : (a1 - a2) % 2 = 0 := by
      omega
    exact ⟨(a1 - a2) / 2, by omega⟩