import Mathlib

theorem number_theory_159338 (p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (h : p1 ≤ p2) :
    (4 * p1)^2 + (4 * p2)^2 = 100000 ↔ (p1, p2) = (3, 79) := by
  constructor
  · -- Assume (4 * p1)^2 + (4 * p2)^2 = 100000, prove (p1, p2) = (3, 79)
    intro heq
    have eq1 : 16 * (p1 ^ 2 + p2 ^ 2) = 100000 := by
      nlinarith
    have eq2 : p1 ^ 2 + p2 ^ 2 = 6250 := by
      omega
    have h1 : p1 ≤ 79 := by
      nlinarith [sq_nonneg (p1 : ℕ), sq_nonneg (p2 : ℕ), eq2, h]
    have h2 : p2 ≤ 79 := by
      nlinarith [sq_nonneg (p1 : ℕ), sq_nonneg (p2 : ℕ), eq2, h]
    interval_cases p1 <;> interval_cases p2 <;> norm_num at hp1 hp2 eq2
    <;> norm_num [Prod.ext_iff] at *
  · -- Assume (p1, p2) = (3, 79), prove (4 * p1)^2 + (4 * p2)^2 = 100000
    rintro ⟨rfl, rfl⟩
    norm_num