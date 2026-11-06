import Mathlib

theorem algebra_249083 :
    { (u, v) : ℝ × ℝ | ∃ (x y : ℝ),
        0 < x ∧ 0 < y ∧
        
        5 * x + 1 = 4 * y ∧  
        4 * x + 8 = 5 * y ∧  
        
        u = 5 * x ∧ v = 5 * y } =
    { (15, 20) } := by
  ext ⟨u, v⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume h : (u, v) ∈ left side
    rintro ⟨x, y, hx, hy, h1, h2, h3, h4⟩
    have eq1 : x = 3 := by
      nlinarith
    have eq2 : y = 4 := by
      nlinarith [eq1, h1]
    have eq3 : u = 15 := by
      nlinarith [eq1, h3]
    have eq4 : v = 20 := by
      nlinarith [eq2, h4]
    simp [eq3, eq4]
  · -- Assume (u, v) = (15, 20)
    rintro ⟨rfl, rfl⟩ 
    use 3, 4 
    norm_num