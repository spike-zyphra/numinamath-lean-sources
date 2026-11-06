import Mathlib


theorem algebra_302599 (m : ℤ) :
    (∃ x1 x2 : ℕ, x1 > 0 ∧ x2 > 0 ∧ x1 ≠ x2 ∧ (m^2 - 1)*x1^2 - 6*(3*m - 1)*x1 + 72 = 0 ∧
      (m^2 - 1)*x2^2 - 6*(3*m - 1)*x2 + 72 = 0) ↔ m = 2 := by
  constructor
  · -- Forward direction: if the equation has two distinct positive integer roots, then m = 2.
    rintro ⟨x1, x2, hx1, hx2, hne, h1, h2⟩
    have eq1 : (m ^ 2 - 1 : ℤ) * x1 ^ 2 - 6 * (3 * m - 1) * x1 + 72 = 0 := by
      exact_mod_cast h1
    have eq2 : (m ^ 2 - 1 : ℤ) * x2 ^ 2 - 6 * (3 * m - 1) * x2 + 72 = 0 := by
      exact_mod_cast h2
    have eq3 : (m ^ 2 - 1 : ℤ) * (x1 + x2) = 6 * (3 * m - 1) := by
      have eq3 : (m ^ 2 - 1 : ℤ) * (x1 ^ 2 : ℤ) - 6 * (3 * m - 1) * (x1 : ℤ) + 72 = 0 := by
        exact_mod_cast h1
      have eq4 : (m ^ 2 - 1 : ℤ) * (x2 ^ 2 : ℤ) - 6 * (3 * m - 1) * (x2 : ℤ) + 72 = 0 := by
        exact_mod_cast h2
      have eq5 : (m ^ 2 - 1 : ℤ) * (x1 ^ 2 : ℤ) - (m ^ 2 - 1 : ℤ) * (x2 ^ 2 : ℤ) - 6 * (3 * m - 1) * (x1 : ℤ) + 6 * (3 * m - 1) * (x2 : ℤ) = 0 := by
        nlinarith
      have eq6 : (m ^ 2 - 1 : ℤ) * ((x1 : ℤ) ^ 2 - (x2 : ℤ) ^ 2) - 6 * (3 * m - 1) * ((x1 : ℤ) - (x2 : ℤ)) = 0 := by
        linarith
      have eq7 : (m ^ 2 - 1 : ℤ) * ((x1 : ℤ) - (x2 : ℤ)) * ((x1 : ℤ) + (x2 : ℤ)) - 6 * (3 * m - 1) * ((x1 : ℤ) - (x2 : ℤ)) = 0 := by
        ring_nf at eq6 ⊢
        linarith
      have eq8 : ((x1 : ℤ) - (x2 : ℤ)) * ((m ^ 2 - 1 : ℤ) * ((x1 : ℤ) + (x2 : ℤ)) - 6 * (3 * m - 1)) = 0 := by
        linarith
      cases (mul_eq_zero.mp eq8) with
      | inl h =>
        exfalso
        have h3 : (x1 : ℤ) = (x2 : ℤ) := by linarith
        have h4 : x1 = x2 := by
          exact_mod_cast h3
        omega
      | inr h =>
        linarith
    -- From eq1 and eq3, we can derive (m^2-1)x1x2 = 72
    have eq4 : (m ^ 2 - 1 : ℤ) * ((x1 : ℤ) * (x2 : ℤ)) = 72 := by
      have eq3' : (m ^ 2 - 1 : ℤ) * (x1 + x2) = 6 * (3 * m - 1) := eq3
      have eq5 : (m ^ 2 - 1 : ℤ) * (x1 : ℤ) ^ 2 - (6 * (3 * m - 1) : ℤ) * (x1 : ℤ) + 72 = 0 := by
        exact_mod_cast h1
      rw [show 6 * (3 * m - 1) = (m ^ 2 - 1 : ℤ) * (x1 + x2) by linarith [eq3']] at eq5
      nlinarith
    -- Now we have (m^2-1)(x1 x2) = 72 and (m^2-1)(x1+x2) = 6(3m-1)
    -- So m^2-1 divides 72.
    have h10 : m ^ 2 - 1 > 0 := by
      nlinarith [show (x1 : ℤ) * (x2 : ℤ) > 0 by
        have h10 : x1 > 0 := by linarith
        have h11 : x2 > 0 := by linarith
        have h12 : (x1 : ℤ) > 0 := by exact_mod_cast h10
        have h13 : (x2 : ℤ) > 0 := by exact_mod_cast h11
        nlinarith
      ]
    have h11 : (m ^ 2 - 1 : ℤ) ∣ 72 := by
      use (x1 * x2 : ℤ)
      linarith [eq4]
    have h12 : m ≤ 9 := by
      have h13 : (m ^ 2 - 1 : ℤ) ≤ 72 := by
        exact Int.le_of_dvd (by norm_num) h11
      have h14 : m ^ 2 ≤ 73 := by
        nlinarith
      have h15 : m ≤ 8 := by
        nlinarith [sq_nonneg (m : ℤ)]
      linarith
    have h13 : m ≥ -9 := by
      have h13 : (m ^ 2 - 1 : ℤ) ≤ 72 := by
        exact Int.le_of_dvd (by norm_num) h11
      have h14 : m ^ 2 ≤ 73 := by
        nlinarith
      have h15 : m ≥ -8 := by
        nlinarith [sq_nonneg (m : ℤ)]
      linarith
    interval_cases m <;> try { 
      omega 
    } <;> try { 
      all_goals
      have h4 : x1 ≤ 32 := by
        nlinarith
      have h5 : x2 ≤ 32 := by
        nlinarith
      interval_cases x1 <;> try { 
        omega 
      } <;> try { 
        omega 
      }
    }
  · -- Backward direction: if m = 2, then the equation has two distinct positive integer roots.
    intro hm
    rw [hm]
    use 4, 6
    all_goals
      norm_num