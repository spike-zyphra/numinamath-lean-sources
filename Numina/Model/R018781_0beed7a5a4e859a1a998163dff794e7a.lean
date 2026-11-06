import Mathlib

theorem algebra_4765 {a b c : ℝ} (ha : a ≠ 0) (h : (a + b + c) * (a - b + c) < 0)
    (f : ℝ → ℝ) (hf : f = fun x => |a * x ^ 2 + b * x + c|) :
    IsLeast (Set.range f) 0 ∧ (∃ x, f x = 0) := by

  have h1 : a + b + c ≠ 0 := by
    by_contra h1
    have : (a + b + c) * (a - b + c) = 0 := by
      rw [h1]
      norm_num
    linarith

  have h2 : a - b + c ≠ 0 := by
    by_contra h2
    have : (a + b + c) * (a - b + c) = 0 := by
      rw [h2]
      norm_num
    linarith

  have h3 : b ^ 2 - 4 * a * c > 0 := by 
    nlinarith [sq_pos_of_ne_zero (show (2 * a) ≠ 0 by 
      intro h'
      apply ha
      linarith
    ), sq_nonneg (b + 2 * a), sq_nonneg (b - 2 * a), sq_pos_of_ne_zero ha
    ]

  have h4 : ∃ x, a * x ^ 2 + b * x + c = 0 := by
    use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
    field_simp [ha]
    ring_nf
    rw [Real.sq_sqrt (by nlinarith)]
    <;> nlinarith
  
  rcases h4 with ⟨x0, hx0⟩

  have h0x0 : f x0 = 0 := by 
    rw [hf]
    simp [hx0]
  
  -- Show that 0 is in the range of f
  have hx5 : 0 ∈ Set.range f := by
    use x0
    all_goals 
      exact h0x0
  
  -- Show that 0 is minimal
  have hx4 : ∀ y, y ∈ Set.range f → 0 ≤ y := by 
    intro y hy
    obtain ⟨x, hx⟩ := hy 
    rw [hf] at hx 
    simp at hx 
    have h_nonneg : |a * x ^ 2 + b * x + c| ≥ 0 := abs_nonneg (a * x ^ 2 + b * x + c)
    linarith
  
  have h6 : IsLeast (Set.range f) 0 := by 
    constructor 
    · exact hx5 
    · exact hx4
  
  have hx3 : ∃ x, f x = 0 := ⟨x0, h0x0⟩
  
  constructor 
  · exact h6 
  · exact hx3