import Mathlib

theorem algebra_281833 (e d r : ℕ → ℚ)
    (start : e 0 = 3000 ∧ d 0 = 4000 ∧ r 0 = 240000)
    (s1 : e 1 = e 0 * 1.021 ∧ d 1 = d 0 * 1.021 ∧ r 1 = 1.079 * r 0)
    (s2 : e 2 = (e 1 - 1000) * 1.021 ∧ d 2 = (d 1 + 1000 * 60.1 / 58.9) * 1.021 ∧ r 2 = 1.079 * r 1)
    (s3 : e 3 = (e 2 + 2000 * 58.5 / 63.2) * 1.021 ∧ d 3 = (d 2 - 2000) * 1.021 ∧ r 3 = 1.079 * r 2) :
    ⌊e 3⌋ = 4040 ∧ ⌊d 3⌋ = 3279 ∧ ⌊r 3⌋ = 301491 := by 
  rcases start with ⟨ea0, da0, ra0⟩
  rcases s1 with ⟨e1, d1, r1⟩
  rcases s2 with ⟨e2, d2, r2⟩
  rcases s3 with ⟨e3, d3, r3⟩
  simp [ea0] at e1 
  simp [da0] at d1 
  simp [ra0] at r1 
  simp [e1] at e2 
  simp [d1] at d2 
  simp [r1] at r2
  simp [e2, d2, r2] at e3 d3 r3 
  norm_num [Int.floor_eq_iff, e3, d3, r3]