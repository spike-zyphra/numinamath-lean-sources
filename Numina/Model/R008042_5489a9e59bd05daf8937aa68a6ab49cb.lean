import Mathlib

theorem algebra_10423 : IsGreatest {m : ℝ | ∃ f g : ℝ → ℝ, Set.range f = Set.Icc (-5) 3 ∧
    Set.range g = Set.Icc (-2) 1 ∧ ∃ y : ℝ, m = f y * g y} 10 := by
  constructor
  · -- We need to prove 10 is in the set
    use (λ y => max (-5) (min 3 y)), (λ y => max (-2) (min 1 y))
    constructor
    · -- Show that the range of f is [-5, 3]
      ext x
      simp [Set.mem_range]
      constructor
      · -- Show that if x ∈ range f, then x ∈ [-5, 3]
        rintro ⟨y, hy⟩
        rw [← hy]
        simp [max_le_iff, le_min_iff]
        all_goals linarith
      · -- Show that if x ∈ [-5, 3], then x ∈ range f
        rintro ⟨hx1, hx2⟩
        use x
        simp [max_eq_left_of_lt, min_eq_right_of_lt, hx1, hx2]
    constructor
    · -- Show that the range of g is [-2, 1]
      ext x
      simp [Set.mem_range]
      constructor
      · -- Show that if x ∈ range g, then x ∈ [-2, 1]
        rintro ⟨y, hy⟩
        rw [← hy]
        simp [max_le_iff, le_min_iff]
        all_goals linarith
      · -- Show that if x ∈ [-2, 1], then x ∈ range g
        rintro ⟨hx1, hx2⟩
        use x
        simp [max_eq_left_of_lt, min_eq_right_of_lt, hx1, hx2]
    · -- Show the existence of y such that m = f y * g y
      use (-5 : ℝ)
      norm_num [max_eq_left_of_lt, min_eq_right_of_lt]
  · -- We need to prove that 10 is the greatest element in the set
    rintro m ⟨f, g, h1, h2, ⟨y, hy⟩⟩
    have h3 : f y ∈ Set.Icc (-5) 3 := by
      rw [←h1]
      exact Set.mem_range_self y
    have h4 : g y ∈ Set.Icc (-2) 1 := by 
      rw [←h2]
      exact Set.mem_range_self y
    rcases h3 with ⟨h3l, h3r⟩
    rcases h4 with ⟨h4l, h4r⟩
    nlinarith