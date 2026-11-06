import Mathlib

theorem algebra_244338 {F : ℤ → ℤ → ℤ → ℝ}
    (hF : ∀ a b c n, F (n * a) (n * b) (n * c) = n * F a b c)
    (hF' : ∀ a b c n, F (a + n) (b + n) (c + n) = F a b c + n)
    (hF'' : ∀ a b c, F a b c = F c b a) :
    F 58 59 60 = 59 := by 
  have eq1 : F 0 0 0 = 0 := by
    have h1 := hF 1 1 1 (0 : ℤ)
    norm_num at h1 ⊢
    linarith 
  have eq5 : F 58 58 58 = (58 : ℝ) := by
    have eq4 : F 58 58 58 = F 0 0 0 + (58 : ℝ) := by 
      specialize hF' 0 0 0 58 
      norm_num at hF' ⊢ 
      linarith 
    rw [eq1] at eq4
    linarith 
  have eq3 : F 58 58 58 = (58 : ℝ) * F 1 1 1 := by 
    have h1 := hF 1 1 1 (58 : ℤ)
    norm_num at h1 ⊢
    linarith 
  have eq7 : F 1 1 1 = 1 := by 
    have eqA : F 58 58 58 = (58 : ℝ) * F 1 1 1 := by 
      have h1 := hF 1 1 1 (58 : ℤ)
      norm_num at h1 ⊢
      linarith 
    have eqB : F 58 58 58 = (58 : ℝ) := by 
      linarith [eq5]
    have eqC : (58 : ℝ) * F 1 1 1 = (58 : ℝ) := by
      linarith [eqA, eqB]
    have eq8 : F 1 1 1 = 1 := by
      apply (mul_left_inj' (show (58 : ℝ) ≠ 0 by norm_num)).mp 
      linarith 
    linarith 
  have eq8 : F 58 59 60 = F 0 1 2 + 58 := by 
    specialize hF' 0 1 2 58 
    norm_num at hF' ⊢ 
    linarith 
  have eq9 : F 0 1 2 = 1 := by
    have eq19 : F 0 1 2 = F (-1 : ℤ) (0 : ℤ) (1 : ℤ) + (1 : ℝ) := by 
      specialize hF' (-1 : ℤ) (0 : ℤ) (1 : ℤ) 1 
      norm_num at hF' ⊢ 
      linarith 
    have eq20 : F (-1 : ℤ) (0 : ℤ) (1 : ℤ) = 0 := by 
      have eq22 : F (-1 : ℤ) (0 : ℤ) (1 : ℤ) = - F (1 : ℤ) (0 : ℤ) (-1 : ℤ) := by 
        specialize hF 1 0 (-1 : ℤ) (-1 : ℤ)
        norm_num at hF ⊢ 
        linarith 
      have eq23 : F (1 : ℤ) (0 : ℤ) (-1 : ℤ) = F (-1 : ℤ) (0 : ℤ) (1 : ℤ) := by 
        specialize hF'' 1 0 (-1 : ℤ) 
        norm_num at hF'' ⊢ 
        linarith 
      have eq24 : F (-1 : ℤ) (0 : ℤ) (1 : ℤ) = - F (-1 : ℤ) (0 : ℤ) (1 : ℤ) := by
        linarith [eq22, eq23]
      have eq25 : F (-1 : ℤ) (0 : ℤ) (1 : ℤ) = 0 := by
        linarith
      linarith 
    rw [eq20] at eq19
    linarith 
  linarith [eq8, eq9]