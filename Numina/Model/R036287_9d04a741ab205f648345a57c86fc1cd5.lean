import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_169171: {m: ℝ | ∃! x: ℤ, -x^2 + x + m + 2 ≥ |x|} = Ico (-2) (-1) := by
  ext m 
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · -- Assume there's a unique integer x such that -x² + x + m + 2 ≥ |x|
    rintro ⟨x, ⟨hx1, hx2⟩⟩
    have h1 := hx1 
    by_cases h3 : x = 0 
    · -- x = 0.
      have hx_eq : x = 0 := h3 
      have h1' := h1 
      rw [hx_eq] at h1' 
      have h10 : (m : ℝ) ≥ (-2 : ℝ) := by
        norm_num [abs_of_nonneg (show (0 : ℝ) ≥ 0 by norm_num)] at h1'
        linarith 
      have h5 := hx2 1 
      have h6 : (-(1 : ℤ) ^ 2 + (1 : ℤ) + m + 2 : ℝ) < |(1 : ℤ)| := by
        by_contra h7 
        push_neg at h7 
        have h8 := h5 h7 
        omega 
      have h20 : (m : ℝ) < (-1 : ℝ) := by 
        norm_num at h6 
        linarith 
      constructor <;> linarith 
    · -- x ≠ 0 
      have hx_ne_zero : x ≠ 0 := h3 
      have h5 := hx2 0 
      have h6 : (x : ℤ) ≠ 0 := hx_ne_zero 
      have h7 : (-(0 : ℤ) ^ 2 + (0 : ℤ) + m + 2 : ℝ) < |(0 : ℤ)| := by 
        by_contra h8 
        push_neg at h8 
        have h9 := h5 h8 
        tauto 
      norm_num at h7 
      by_cases h8 : x > 0 
      · -- x > 0 
        have h9 : x > 0 := h8 
        have h10 : (x : ℝ) > 0 := by exact_mod_cast h9 
        have hx0 : |(x : ℝ)| = (x : ℝ) := by 
          rw [abs_of_nonneg (show (x : ℝ) ≥ 0 by nlinarith)]
        have h11 : (m : ℝ) + 2 ≥ (x : ℝ) ^ 2 := by
          norm_num [hx0] at h1 
          nlinarith 
        nlinarith 
      · -- x ≤ 0 
        have h11 : x ≤ 0 := by omega 
        have h12 : x < 0 := by 
          by_contra h9 
          push_neg at h9 
          have h10 : x = 0 := by linarith 
          tauto 
        have h13 : (x : ℝ) < 0 := by exact_mod_cast h12 
        have hx0 : |(x : ℝ)| = (- (x : ℝ)) := by 
          rw [abs_of_neg (show (x : ℝ) < 0 by nlinarith)]
        have h14 : (m : ℝ) + 2 + 2 * (x : ℝ) ≥ (x : ℝ) ^ 2 := by 
          norm_num [hx0] at h1 
          nlinarith 
        nlinarith [sq_nonneg ((x : ℝ) + 1), sq_nonneg ((m + 2) : ℝ)]
  · -- Show the reverse direction: if m is in the interval then there's a unique solution
    rintro ⟨h1, h2⟩ 
    use 0 
    constructor 
    · -- Show 0 is a solution 
      norm_num 
      all_goals linarith 
    · -- Show uniqueness 
      intro y hy 
      by_cases h3 : y ≥ 0 
      · -- y ≥ 0 
        have hy0 : |(y : ℝ)| = (y : ℝ) := by 
          simp [abs_of_nonneg (show (y : ℝ) ≥ 0 by exact_mod_cast (show y ≥ 0 by omega))]
        norm_num [hy0] at hy 
        by_cases h4 : y > 0 
        · -- y > 0 
          have h5 : y ≥ 1 := by omega 
          have h6 : (y : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h5 
          nlinarith 
        · -- y = 0 
          have h5 : y = 0 := by omega 
          omega 
      · -- y < 0 
        have hy0 : |(y : ℝ)| = (-y : ℝ) := by 
          simp [abs_of_neg (show (y : ℝ) < 0 by exact_mod_cast (show y < 0 by omega))]
        norm_num [hy0] at hy 
        have h5 : y ≤ -1 := by omega 
        have h6 : (y : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h5 
        nlinarith