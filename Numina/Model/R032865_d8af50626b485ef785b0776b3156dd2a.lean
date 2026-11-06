import Mathlib

theorem algebra_19406 {x : ℚ} (hx : x > 1) (h : Real.sqrt x / Real.sqrt (x - 1) = 3 / 2) :
    {(a,b) |  x = (a / b)  ∧  a = x.num ∧ b = x.den} = {(9,5)} := by 
  have hx1 : (x : ℝ) > (1 : ℝ) := by exact_mod_cast hx
  have h1 : Real.sqrt x / Real.sqrt (x - 1) = 3 / 2 := by
    simpa using h
  have h2 : Real.sqrt (x : ℝ) = (3 / 2) * Real.sqrt (x - 1 : ℝ) := by 
    field_simp [show Real.sqrt (x - 1 : ℝ) ≠ 0 by 
      have h5 : (x - 1 : ℝ) > (0 : ℝ) := by
        exact_mod_cast sub_pos.mpr hx
      positivity
    ] at h1 ⊢
    <;> nlinarith [Real.sqrt_nonneg (x : ℝ), Real.sqrt_nonneg (x - 1 : ℝ)] -- addresses the nonnegativity conditions
  -- Use h2: ∃ y > 0 : sqrt (x) = y ∧ sqrt(x - 1) = y * 2/3
  -- Then sqrt(x) would operator over to get x = y^2, x - 1 = (y*2/3)^2
  have h3 : (Real.sqrt (x : ℝ) : ℝ) ^ 2 = ( (3 / 2) * Real.sqrt (x - 1 : ℝ) ) ^ 2 := by 
    rw [h2]
  have h4 : (Real.sqrt (x : ℝ) : ℝ) ^ 2 = (x : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by exact_mod_cast show (0 : ℚ) ≤ x by linarith)
  have h5 : ( (3 / 2) * Real.sqrt (x - 1 : ℝ) : ℝ ) ^ 2 = ( 9 / 4 ) * ( (Real.sqrt (x - 1 : ℝ) : ℝ ) ^ 2 ) := by
    ring_nf
  have h6 : ( (Real.sqrt (x - 1 : ℝ) : ℝ ) ^ 2 ) = ( (x - 1 : ℝ ) ) := Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1 : ℝ) by exact_mod_cast show (0 : ℚ) ≤ (x - 1) by linarith)
  rw [h4, h5, h6] at h3
  -- Solving equation leads to x = 9/5.
  have h7 : (x : ℝ) = (9 / 5 : ℝ) := by
    nlinarith
  have hx10 : x = (9 / 5 : ℚ) := by 
    have h8 : (x : ℝ) = (9 / 5 : ℝ) := h7
    have h9 : (x : ℝ) = (↑(9 / 5 : ℚ) : ℝ) := by
      rw [h8]
      all_goals norm_num
    have h10 : x = (9 / 5 : ℚ) := by
      exact_mod_cast h9
    exact h10
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, hx10]
  constructor
  · -- Assume ⟨a, b⟩ satisfy the conditions. 
    rintro ⟨hx_eq, ha_eq, hb_eq⟩
    simp [ha_eq, hb_eq]
    all_goals norm_num at *
    all_goals try linarith
    all_goals norm_num [Rat.num, Rat.den] at *
  · -- Assume ⟨9,5⟩.
    rintro ⟨rfl, rfl⟩
    constructor
    · -- Check x = 9/5.
      norm_num
    constructor
    · -- Check a = 9.
      norm_num
    · -- Check b = 5.
      norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto
  all_goals norm_num
  all_goals tauto