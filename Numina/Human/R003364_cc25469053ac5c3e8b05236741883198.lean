import Mathlib
/-1. [5] A polynomial $P$ with integer coefficients is called tricky if it has 4 as a root.
A polynomial is called teeny if it has degree at most 1 and integer coefficients between -7 and 7 , inclusive.
How many nonzero tricky teeny polynomials are there?-/
theorem algebra_172809 (P : ℝ → ℝ ) (c a b : ℤ ) (hp :(∀ x:ℝ , P x = c) ∨(∀x:ℝ , P x = a*x + b))
(hptricky : P 4 = 0) (hpteeny1 : -7 ≤ a ∧ a ≤ 7) (hpteeny2 : -7 ≤ b ∧ b ≤ 7) (hpteeny3 : -7 ≤ c ∧ c ≤ 7) :
  ∀ x : ℝ , P x = -1*x +4∨ P x = x - 4 ∨ P x = 0:= by

  rcases hp with (hp|hp)
  · -- case where P is constant function
    have h1 : (c : ℝ ) = 0 := by
      specialize hp 4
      rw [hp] at hptricky
      linarith
    intro x
    specialize hp x
    rw [hp]
    rw [h1]
    simp
  · -- case where P is linear function
    have h1 : (a : ℝ ) * (4 : ℝ ) + (b : ℝ ) = 0 := by
      specialize hp 4
      rw [hp] at hptricky
      linarith
    have h2 : a * 4 + b = 0 := by
      have ha1 : (a : ℝ ) * (4 : ℝ ) + (b : ℝ ) = (a * 4 + b : ℤ ) := by
        simp
      rw [ha1] at h1
      norm_cast at h1 ⊢
    have ha1 : -1 ≤ a := by omega
    have ha2 : a ≤ 1 := by omega
    -- solve possible integer values
    -- a is integer and -1 ≤ a ≤ 1, so a ∈ {-1,0,1}
    have h4 : a = -1 ∨ a = 0 ∨ a = 1 := by omega
    intro x
    specialize hp x
    rw [hp]
    have h3 : b = -4 * a := by omega
    rw [h3]
    rcases h4 with (ha | ha | ha)
    · -- a = -1
      rw [ha]
      norm_num
    · -- a = 0
      rw [ha]
      norm_num
    · -- a = 1
      rw [ha]
      norm_num
      tauto
