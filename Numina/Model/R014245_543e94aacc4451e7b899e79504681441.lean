import Mathlib

theorem algebra_283163 (x y : ℤ) :
    x > 0 ∧ y > 0 ∧ 2 * x ^ 2 + 5 * y ^ 2 = 11 * (x * y - 11) ↔ (x, y) = (14, 27) := by
  constructor
  · -- Assume (x, y) is a positive integer pair that satisfies the equation, prove (x, y) = (14, 27)
    rintro ⟨hx, hy, heq⟩
    have h1 : (2 * x - y) * (x - 5 * y) = -121 := by
      nlinarith
    have h2 : (2 * x - y) ∣ -121 := by
      use (x - 5 * y)
      all_goals nlinarith
    have h3 : (2 * x - y) ∣ 121 := by
      have h4 : (2 * x - y) ∣ -121 := h2
      exact Int.dvd_neg.mp h4
    have h4 : (2 * x - y) ≤ 121 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : (2 * x - y) ≥ -121 := by
      have h6 : -(2 * x - y) ∣ 121 := by
        exact Int.neg_dvd.2 h3
      have h7 : -(2 * x - y) ≤ 121 := by
        apply Int.le_of_dvd (by norm_num) h6
      linarith
    interval_cases k : (2 * x - y) <;> norm_num at h1 ⊢
      <;> norm_num [Prod.ext_iff] at *
      <;> try { 
        omega
      }
      <;> try { 
        all_goals
          nlinarith
          all_goals
            nlinarith
      }
  · -- Assume (x, y) = (14, 27), prove they satisfy the equation
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · -- check the equation
      norm_num
      <;> simp [Prod.ext_iff]
      <;> norm_num
      <;> try { tauto }
      <;> try { nlinarith }