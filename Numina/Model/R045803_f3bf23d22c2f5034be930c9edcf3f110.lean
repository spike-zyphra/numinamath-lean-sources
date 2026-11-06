import Mathlib

theorem algebra_11391
    (s : Set ℝ)
    (hs : s = {x : ℝ | (x + 2) / (2 * x + 2) = (4 * x + 3) / (7 * x + 3)}) :
    s.Finite ∧ ((fin : s.Finite) → fin.toFinset.prod id = 0) := by
  have h1 : s = {0, 3} := by
    ext x
    simp [hs]
    constructor
    · -- Assume (x + 2) / (2 * x + 2) = (4 * x + 3) / (7 * x + 3)
      intro h
      have h2 : x ≠ -1 := by
        by_contra h2
        rw [h2] at h
        norm_num at h 
      have h3 : x ≠ -3 / 7 := by
        by_contra h3
        rw [h3] at h
        norm_num at h
      have h4 : (x + 2) / (2 * x + 2) = (4 * x + 3) / (7 * x + 3) := h 
      have h5 : (x + 2) * (7 * x + 3) = (4 * x + 3) * (2 * x + 2) := by
        have hx1 : (2 * x + 2) ≠ 0 := by
          intro hx
          apply h2
          linarith 
        have hx2 : (7 * x + 3) ≠ 0 := by 
          intro hx
          apply h3
          linarith
        field_simp [hx1, hx2] at h4 ⊢
        <;> nlinarith 
      have h6 : x * (x - 3) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.1 h6) with h7 h8
      · -- x = 0 
        left 
        linarith 
      · -- x - 3 = 0, so x = 3 
        right 
        linarith 
    · -- Show that if x ∈ {0, 3}, then (x + 2)/(2x + 2) = (4x + 3)/(7x + 3)
      rintro (rfl | rfl)
      · -- Check x = 0 
        norm_num 
      · -- Check x = 3 
        norm_num 
  rw [h1]
  constructor
  · -- Show {0, 3} is finite 
    simp 
  · -- Show that the product is 0 
    intro fin
    simp [Finset.prod_insert, Finset.prod_singleton]
    all_goals norm_num 
  all_goals norm_num 
  <;> try { tauto }