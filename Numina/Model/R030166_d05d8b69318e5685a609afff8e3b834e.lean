import Mathlib

theorem algebra_283007 :
    {(p₁, p₂, s) : ℝ × ℝ × ℝ | 
      p₁ > 0 ∧ p₂ > 0 ∧ s > 0 ∧
      s = 0.8 * p₁ ∧ 
      s = 1.2 * p₂ ∧ 
      p₁ + p₂ - 2*s = 10} =
    {(150, 100, 120)} := by
  ext ⟨p₁, p₂, s⟩
  simp
  constructor
  · -- Assume (p₁, p₂, s) is in the set.
    rintro ⟨hp₁, hp₂, hs, h1, h2, h3⟩
  
    have eq1 : p₁ = 150 := by
      norm_num at h1 h2 h3
      linarith

    have eq2 : p₂ = 100 := by
      norm_num at h1 h2 h3
      linarith
  
    have eq3 : s = 120 := by
      norm_num at h1 h2 h3
      linarith
  
    simp [eq1, eq2, eq3]
    all_goals linarith
  · -- Now prove the reverse direction.
    rintro ⟨rfl, rfl, rfl⟩
  
    constructor
    · norm_num
  
    constructor
    · norm_num
  
    constructor
    · norm_num
  
    constructor
    · norm_num
  
    constructor
    · norm_num
  
    · norm_num