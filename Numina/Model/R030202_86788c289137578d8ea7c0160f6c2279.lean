import Mathlib

theorem algebra_252547 :
  { (x, y) : ℝ × ℝ | 0 < x ∧ 0 < y ∧ 
    ∃ (va vb : ℝ), 0 < va ∧ 0 < vb ∧ 
    va / vb = 5 / 4 ∧  
    x + y/3 = 145 ∧   
    x + 7*y/9 = 201 } =   
  { (103, 126) } := by

  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume h: P, prove ⊢ Q
    rintro ⟨hx, hy, ⟨va, vb, h1, h2, h3, h4, h5⟩⟩
    norm_num at h3 h4 h5
    have hx2 : x = 103 := by
      nlinarith
    have hy2 : y = 126 := by
      nlinarith

    exact (Prod.ext_iff.mpr ⟨hx2, hy2⟩)

  · -- Assume right side, prove left side
    rintro ⟨rfl, rfl⟩
    constructor
    · -- Show 0 < x
      norm_num
    constructor
    · -- Show 0 < y
      norm_num
    use (125), (100)
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show that 125 / 100 = 5 / 4
      norm_num
    constructor
    · -- Show that 103 + 126/3 = 145
      norm_num
    · -- Show that 103 + 7*126/9 = 201
      norm_num