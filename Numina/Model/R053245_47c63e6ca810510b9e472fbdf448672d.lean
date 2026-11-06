import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_5511 {f g : ℝ → ℝ}
  (hf : ∀ x > 0, f x = x + 1 / x)
  (hg : ∀ x > 0, g x = x ^ 2 - 4 * x + 2019) :
  IsLeast {g (f x) | x > 0} 2015 := by 
  constructor
  · -- First, we need to prove that 2015 is attainable, meaning g (f x) can equal 2015 for some x > 0
    use 1
    constructor
    · -- Show that 1 > 0
      norm_num
    · -- Show that g (f 1) = 2015
      have hfx : f 1 = 2 := by 
        specialize hf 1 (show (1 : ℝ) > 0 by norm_num)
        rw [hf]
        norm_num
      rw [hfx]
      have : g (2 : ℝ) = 2015 := by 
        specialize hg 2 (show (2 : ℝ) > 0 by norm_num)
        rw [hg]
        norm_num
      linarith

  · -- Now, we need to prove that 2015 is a lower bound; i.e., for all x > 0, g (f x) ≥ 2015
    intro y me_neg
    rcases me_neg with ⟨x, hx, rfl⟩

    have hfxge2 : f x ≥ 2 := by 
      have hfx : f x = x + 1 / x := hf x hx
      rw [hfx]
      have h1 : x + 1 / x ≥ 2 := by
        have h2 : x * (1 / x) = 1 := by 
          field_simp
        nlinarith [sq_nonneg (x - 1)]
      linarith

    have hgxge2015 : g (f x) ≥ 2015 := by 
      have h9 : g (f x) = (f x) ^ 2 - 4 * (f x) + 2019 := by 
        have h3 : f x > 0 := by
          have hfx : f x ≥ 2 := hfxge2 
          linarith
        specialize hg (f x) h3 
        simpa using hg
      rw [h9]
      nlinarith [sq_nonneg ((f x) - 2)]
    
    linarith