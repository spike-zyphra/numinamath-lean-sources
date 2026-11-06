import Mathlib

theorem algebra_256744 :
  { (x, y, z) : ℝ × ℝ × ℝ | 
    x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧
    x + y + z = 351 ∧
    x/9 + 3*y/9 + 5*z/9 = 91 ∧
    3*x/9 + 5*y/9 + z/9 = 117 ∧
    5*x/9 + y/9 + 3*z/9 = 143
  } = { (195, 78, 78) } := by
  ext ⟨x, y, z⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (x, y, z) in left side, prove (x,y,z) in right side.
    rintro ⟨hx, hy, hz, h1, h2, h3, h4⟩
    have eq1 : x = 195 := by
      linarith
    have eq2 : y = 78 := by
      linarith
    have eq3 : z = 78 := by
      linarith
    simp [eq1, eq2, eq3]
  · -- Show that (195, 78, 78) is in the set
    rintro (h_eq)
    rcases h_eq with ⟨rfl, rfl, rfl⟩
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
    constructor
    · norm_num
    · norm_num