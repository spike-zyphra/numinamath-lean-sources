import Mathlib

theorem algebra_8649 {a1 a2 b1 b2 : ℤ} {P1 P2 : ℤ → ℤ}
    (hp1 : P1 = fun x => x ^ 2 + a1 * x + b1)
    (hp2 : P2 = fun x => x ^ 2 + a2 * x + b2)
    (ha1 : a1 ≠ a2)
    (hm : ∃ m n : ℤ, m ≠ n ∧ P1 m = P2 n ∧ P2 m = P1 n) :
    Even (a1 - a2) := by
  rcases hm with ⟨m, n, hmn, hp1m, hp2m⟩
  have eq1 : m ^ 2 + a1 * m + b1 = n ^ 2 + a2 * n + b2 := by
    rw [hp1] at hp1m
    rw [hp2] at hp1m
    simpa using hp1m
  have eq2 : m ^ 2 + a2 * m + b2 = n ^ 2 + a1 * n + b1 := by
    rw [hp1] at hp2m
    rw [hp2] at hp2m
    simpa using hp2m
  have eq3 : (a1 + a2) = -2 * (m + n) := by
    have h : (m - n) * (2 * (m + n) + (a1 + a2)) = 0 := by
      linarith
    cases' (mul_eq_zero.1 h) with h1 h2
    · -- m - n = 0
      exfalso
      exact hmn (by linarith)
    · -- 2(m + n) + (a1 + a2) = 0
      linarith
  have eq6 : (a1 - a2) * (m + n) = 2 * (b2 - b1) := by
    have h1 : m ^ 2 + a1 * m + b1 = n ^ 2 + a2 * n + b2 := by exact_mod_cast eq1
    have h2 : m ^ 2 + a2 * m + b2 = n ^ 2 + a1 * n + b1 := by exact_mod_cast eq2
    linarith
  have eq4 : (a1 - a2) * (m + n) % 2 = 0 := by
    rw [eq6]
    omega
  have eq5 : (a1 + a2) % 2 = 0 := by
    rw [eq3]
    omega
  have h8 : (a1 - a2) % 2 = 0 := by
    by_cases h : (m + n) % 2 = 1
    · -- m + n is odd
      omega
    · -- m + n is even
      have h7 : (m + n) % 2 = 0 := by
        omega
      omega
  exact ⟨(a1 - a2) / 2, by omega⟩