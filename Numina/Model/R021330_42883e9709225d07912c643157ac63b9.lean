import Mathlib

theorem algebra_67902 {a1 a2 b1 b2 : ℤ} (P1 P2 : ℤ → ℤ)
    (hP1 : P1 = fun x => x ^ 2 + a1 * x + b1)
    (hP2 : P2 = fun x => x ^ 2 + a2 * x + b2)
    (ha1 : a1 ≠ a2)
    (hm : ∃ m n : ℤ, m ≠ n ∧ P1 m = P2 n ∧ P2 m = P1 n) :
    Even (a1 - a2) := by 
  rcases hm with ⟨m, n, hmn, hm1, hn1⟩
  have eq1 : m ^ 2 + a1 * m + b1 = n ^ 2 + a2 * n + b2 := by 
    have h1 : P1 m = m ^ 2 + a1 * m + b1 := by simp [hP1]
    have h2 : P2 n = n ^ 2 + a2 * n + b2 := by simp [hP2]
    rw [h1] at hm1
    rw [h2] at hm1
    linarith
  have eq2 : m ^ 2 + a2 * m + b2 = n ^ 2 + a1 * n + b1 := by 
    have h3 : P2 m = m ^ 2 + a2 * m + b2 := by simp [hP2]
    have h4 : P1 n = n ^ 2 + a1 * n + b1 := by simp [hP1]
    rw [h3] at hn1
    rw [h4] at hn1
    linarith
  -- Subtract eq2 from eq1 to obtain equation for difference
  have eq3 : a1 + a2 = -2 * (m + n) := by
    have eq4 : 2 * (m ^ 2 - n ^ 2) + (a1 + a2) * (m - n) = 0 := by 
      nlinarith
    have hmn' : m - n ≠ 0 := by
      intro h
      apply hmn
      omega
    have eq5 : (m - n) * (2 * (m + n) + (a1 + a2)) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp eq5) with eq6 eq7
    · -- m - n = 0, but m ≠ n
      exfalso 
      apply hmn
      linarith
    · -- 2 * (m + n) + (a1 + a2) = 0
      linarith
  have h9 : Even (a1 + a2) := by
    have : (a1 + a2) % 2 = 0 := by 
      omega
    exact ⟨(a1 + a2) / 2, by omega⟩
  have : Even (a1 - a2) := by
    have h10 : (a1 - a2) % 2 = 0 := by
      have h11 : (a1 + a2) % 2 = 0 := by 
        omega
      omega
    exact ⟨(a1 - a2) / 2, by omega⟩
  assumption