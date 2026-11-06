import Mathlib

theorem number_theory_204706 (X Y : ℤ) :
    Prime (X ^ 4 + 4 * Y ^ 4) ↔ ((X = 1 ∧ Y = 1) ∨ (X = -1 ∧ Y = 1) ∨ (X = 1 ∧ Y = -1) ∨ (X = -1 ∧ Y = -1))  := by 
  have eq1 : X ^ 4 + 4 * Y ^ 4 = (X ^ 2 + 2 * X * Y + 2 * Y ^ 2) * (X ^ 2 - 2 * X * Y + 2 * Y ^ 2) := by 
    ring
  constructor
  · intro h
    have eq2 : X ^ 4 + 4 * Y ^ 4 ≥ 0 := by positivity
    have eq3 : X ^ 2 + 2 * X * Y + 2 * Y ^ 2 ≥ 0 := by nlinarith
    -- Irreducible.isUnit_or_isUnit'
    have auxprime : Irreducible (X ^ 4 + 4 * Y ^ 4)  := by 
      exact Prime.irreducible h
    obtain h2 := Irreducible.isUnit_or_isUnit' auxprime _ _ eq1
    
    have eq4 : X ^ 2 + 2 * X * Y + 2 * Y ^ 2 = 1 ∨ (X ^ 2 - 2 * X * Y + 2 * Y ^ 2) = 1 := by 
      have pos : X ^ 2 + 2 * X * Y + 2 * Y ^ 2 ≥ 0 := by 
        calc 
          _ = (X + Y) ^ 2 + Y ^ 2 := by 
            ring
          _ ≥ 0 := by positivity
      obtain h2 | h2 := h2
      left
      -- since above is unit in ℤ, then X ^ 2 + 2 * X * Y + 2 * Y ^ 2 = 1 ∨ -1, but -1 is not possible.
      obtain h3 | h3 := Int.isUnit_iff.mp h2
      exact h3
      linarith
      obtain h3 | h3 := Int.isUnit_iff.mp h2
      right 
      exact h3
      have pos2 : X ^ 2 - 2 * X * Y + 2 * Y ^ 2 ≥ 0 := by
        nlinarith
      linarith 
    obtain heq | heq := eq4
    -- the cases : X ^ 2 + 2 * X * Y + 2 * Y ^ 2 = 1
    · have eq4 : (X + Y) ^ 2+Y ^ 2 = 1 := by 
        rw [←heq]
        ring
      by_cases hzero : Y = 0
      rw [hzero] at eq4
      simp at eq4
      obtain hx | hx := eq4
      rw [hx, hzero] at h
      norm_num at h
      rw [hx, hzero] at h
      norm_num at h
      have ineq : Y ^ 2 ≠  0 := by 
        exact pow_ne_zero 2 hzero
      have ineq2 : Y ^ 2 ≥ 1 := by 
        by_contra hc
        simp at hc
        exact hzero hc
      have eq5 : (X + Y) ^ 2 = 0 := by 
        nlinarith
      have eq6 : X = -Y := by
        nlinarith
      have yeq : Y = 1 ∨ Y = -1 := by 
        have aux : Y ^ 2 = 1 := by 
          nlinarith
        exact sq_eq_one_iff.mp aux
      obtain yeq | yeq := yeq
      rw [yeq] at eq6
      rw [eq6, yeq] at h
      norm_num at h
      rw [eq6, yeq] at h2
      norm_num at h2
      right
      left
      exact ⟨eq6, yeq⟩
      rw [yeq] at eq6
      simp at eq6
      right
      right
      left
      exact ⟨eq6,yeq⟩
    -- the cases : X ^ 2 + 2 * X * Y + 2 * Y ^ 2 = 1
    · have eq4 : (X - Y) ^ 2+Y ^ 2 = 1 := by 
        rw [←heq]
        ring
      by_cases hzero : Y = 0
      rw [hzero] at eq4
      simp at eq4
      obtain hx | hx := eq4
      rw [hx, hzero] at h
      norm_num at h
      rw [hx, hzero] at h
      norm_num at h
      have ineq : Y ^ 2 ≠  0 := by 
        exact pow_ne_zero 2 hzero
      have ineq2 : Y ^ 2 ≥ 1 := by 
        by_contra hc
        simp at hc
        exact hzero hc
      have eq5 : (X - Y) ^ 2 = 0 := by 
        nlinarith
      have eq6 : X = Y := by
        nlinarith
      have yeq : Y = 1 ∨ Y = -1 := by 
        have aux : Y ^ 2 = 1 := by 
          nlinarith
        exact sq_eq_one_iff.mp aux
      obtain yeq | yeq := yeq
      rw [yeq] at eq6
      left
      exact ⟨eq6, yeq⟩
      rw [yeq] at eq6
      right
      right
      right
      exact ⟨eq6,yeq⟩
 
  intro h
  obtain h | h | h | h := h
  all_goals simp_all
  norm_num
  norm_num
  norm_num
  norm_num
  