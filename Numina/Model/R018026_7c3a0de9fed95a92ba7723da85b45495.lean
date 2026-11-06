import Mathlib

theorem number_theory_316269 : {(x, y) : ℤ × ℤ | x ^ 2 - 2 * x * y + 126 * y ^ 2 = 2009} =
    {(1, 4), (7, 4), (-1, -4), (-7, -4)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x^2 - 2xy + 126 y^2 = 2009) prove ((x, y) in the set).
    rintro H
    have h1 : (x - y) ^ 2 + 125 * y ^ 2 = 2009 := by
      nlinarith
    have h2 : y ≥ -4 := by
      nlinarith [sq_nonneg (y), sq_nonneg (x - y)]
    have h3 : y ≤ 4 := by
      nlinarith [sq_nonneg (y), sq_nonneg (x - y)]
    interval_cases y <;> try { 
      have h6 : x ≤ 45 := by
        nlinarith [sq_nonneg (x - 45)]
      have h7 : x ≥ -45 := by
        nlinarith [sq_nonneg (x + 45)]
      interval_cases x <;> norm_num at h1 ⊢
      <;> tauto
    }
    <;> try { tauto }
  · -- Assume (x, y) in the finite set, prove (x^2 - 2xy + 126 y^2 = 2009).
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (1, 4)
      norm_num
    · -- (7, 4)
      norm_num
    · -- (-1, -4)
      norm_num
    · -- (-7, -4)
      norm_num