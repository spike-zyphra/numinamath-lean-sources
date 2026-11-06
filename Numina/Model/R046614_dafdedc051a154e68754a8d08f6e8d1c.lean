import Mathlib

theorem algebra_160634 :
    IsLeast {x : ℚ | ∃ a b c : ℤ, x = (a * b + c) / (a + b + c) ∧ 1 ≤ a ∧ a ≤ 2011 ∧ 1 ≤ b ∧ b ≤ 2011 ∧ 1 ≤ c ∧ c ≤ 2011} (2 / 3) := by
  constructor
  · -- Show 2/3 is in the set
    use 1, 1, 1
    norm_num
  · -- Show 2/3 is the least
    intro x hx
    rcases hx with ⟨a, b, c, h_eq, ha1, ha2, hb1, hb2, hc1, hc2⟩
    have h1 : (a * b + c : ℚ) / (a + b + c) ≥ (2 / 3 : ℚ) := by
      have h2 : (a + b + c : ℚ) > (0 : ℚ) := by
        exact_mod_cast (by omega : a + b + c > 0)
      have h3 : (a * b + c : ℚ) ≥ (2 / 3 : ℚ) * (a + b + c : ℚ) := by
        have h4 : (a * b + c : ℚ) * 3 ≥ (2 * (a + b + c) : ℚ) := by
          exact_mod_cast (show (a * b + c) * 3 ≥ 2 * (a + b + c) by 
            nlinarith [show a ≥ 1 by omega, show b ≥ 1 by omega, show c ≥ 1 by omega, 
                      mul_nonneg (show (0 : ℤ) ≤ a - 1 by omega) (show (0 : ℤ) ≤ b - 1 by omega),
                      mul_nonneg (show (0 : ℤ) ≤ a - 1 by omega) (show (0 : ℤ) ≤ c - 1 by omega),
                      mul_nonneg (show (0 : ℤ) ≤ b - 1 by omega) (show (0 : ℤ) ≤ c - 1 by omega)
            ]
          )
        linarith
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    have h2 : x = (a * b + c : ℚ) / (a + b + c : ℚ) := by 
      linarith [h_eq]
    linarith [h2, h1]