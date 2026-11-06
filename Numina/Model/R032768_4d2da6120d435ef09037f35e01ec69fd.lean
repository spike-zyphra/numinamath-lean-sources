import Mathlib

theorem algebra_228574 :
    { a : ℝ | ∃ x1 x2, x1 = 4 * x2 ∧ x1^2 + a * x1 + 2 * a = 0 ∧ x2^2 + a * x2 + 2 * a = 0 } = {0, 25/2} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First, show that if such x1, x2 exist, then a ∈ {0, 25/2}
    rintro ⟨x1, x2, hx12, h1, h2⟩
    rw [hx12] at h1
    have eq3 : 8 * x2 ^ 2 + 2 * a * x2 + a = 0 := by
      nlinarith 
    have eq4 : 7 * x2 ^ 2 + a * (x2 - 1) = 0 := by 
      nlinarith [h2, eq3]
    by_cases h : x2 - 1 = 0
    · -- x2 = 1
      have h4 : x2 = 1 := by
        linarith
      rw [h4] at eq4
      nlinarith 
    · -- x2 ≠ 1
      have eq5 : a = -7 * x2 ^ 2 / (x2 - 1) := by 
        field_simp [(show x2 - 1 ≠ 0 by 
          by_contra h'
          have : x2 - 1 = 0 := by linarith 
          contradiction 
        )]
        linarith [eq4] 
      rw [eq5] at h2 
      have h2' : x2 - 1 ≠ 0 := h 
      field_simp [h2'] at h2 
      have eq7 : -3 * x2 ^ 2 * (2 * x2 + 5) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp eq7) with h8 h9 
      · -- -3 * x2^2 = 0 
        have hx2 : x2 = 0 := by 
          nlinarith 
        rw [hx2] at eq5 
        norm_num at eq5 ⊢ 
        left 
        linarith 
      · -- 2 * x2 + 5 = 0 
        have hx2 : x2 = -5 / 2 := by 
          linarith 
        rw [hx2] at eq5 
        norm_num at eq5 ⊢ 
        right 
        linarith 
  · -- Show that if a ∈ {0, 25/2}, then there exist x1, x2 such that x1 = 4 * x2 and both are roots
    rintro (rfl | rfl)
    · -- a = 0 
      use 0, 0 
      norm_num 
    · -- a = 25/2 
      use -10, -5 / 2 
      constructor 
      · -- Show that -10 = 4 * (-5/2) 
        norm_num 
      constructor 
      · -- Show that (-10)^2 + (25/2)(-10) + 25 = 0 
        norm_num 
      · -- Show that (-5/2)^2 + (25/2)(-5/2) + 25 = 0 
        norm_num