import Mathlib

theorem number_theory_604194 (x y : ℤ) (hx : x > 0) (hy : y > 0) :
  9 * (x ^ 2 + y ^ 2 + 1) + 2 * (3 * x * y + 2) = 2005 ↔ (x, y) = (11, 7) ∨ (x, y) = (7, 11) := by
  constructor
  · -- Assume the equation, derive the solutions
    intro h
    have h1 : 3 * x^2 + 2 * x * y + 3 * y^2 = 664 := by
      nlinarith
    have h2 : x ≤ 18 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    have h3 : y ≤ 18 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    interval_cases x <;> interval_cases y <;> norm_num at h1 <;> norm_num [Prod.ext_iff]
    <;> tauto
  · -- Show the solutions satisfy the equation
    rintro (h | h)
    · -- Check (11, 7)
      simp [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Check (7, 11)
      simp [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num