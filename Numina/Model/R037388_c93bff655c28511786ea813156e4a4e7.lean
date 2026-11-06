import Mathlib

theorem algebra_16713 (f : ℤ → ℝ → ℝ) (hf : ∀ b, ∀ x, f b x = x ^ 2 + b * x + 12) :
    IsGreatest {b : ℤ | (-4) ∉ Set.range (f b)} 7 := by
  constructor
  · -- Show 7 is in the set
    show (-4) ∉ Set.range (f 7)
    intro h
    rcases h with ⟨y, hy⟩
    have eq1 : f 7 y = -4 := hy
    rw [hf 7 y] at eq1
    have eq3 : y ^ 2 + (7 : ℝ) * y + 16 = 0 := by 
      norm_num at eq1 ⊢
      nlinarith 
    have eq4 : (y + (7 / 2 : ℝ)) ^ 2 ≥ 0 := by 
      apply sq_nonneg 
    nlinarith 
  · -- Show that for any b in the set, b ≤ 7
    intro b hb
    have h : (-4) ∉ Set.range (f b) := hb
    by_contra h1
    push_neg at h1 
    have h8 : b ≥ 8 := by 
      omega 
    have h9 : (b : ℝ) ≥ (8 : ℝ) := by 
      exact_mod_cast h8 
    have h10 : ∃ z : ℝ, f b z = -4 := by 
      use (- (b : ℝ) + Real.sqrt ((b : ℝ) ^ 2 - 64)) / 2 
      rw [hf b] 
      field_simp 
      nlinarith [Real.sqrt_nonneg ((b : ℝ) ^ 2 - 64), Real.sq_sqrt (show (0 : ℝ) ≤ (b : ℝ) ^ 2 - 64 by 
        nlinarith [show (b : ℝ) ≥ (8 : ℝ) by linarith]
      )
      ] 
    rcases h10 with ⟨z, h11⟩
    have h11 : (-4) ∈ Set.range (f b) := by 
      refine ⟨z, h11⟩
    contradiction