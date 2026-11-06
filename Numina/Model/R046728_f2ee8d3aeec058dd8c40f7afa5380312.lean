import Mathlib
open Real

theorem algebra_252352 : {(a, b) : ℝ × ℝ | b > 0 ∧ ∃ x : ℤ, x ^ 2 + a * x + a = b ∧ (x + 1) ^ 2 + a * (x + 1) + a = -b ∧ (x + 2) ^ 2 + a * (x + 2) + a = -b ∧ (x + 3) ^ 2 + a * (x + 3) + a = b} = {(-1, 1), (5, 1)}:= by
  ext ⟨a, b⟩ 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Show (a, b) in LHS then in RHS.
    rintro ⟨hb, ⟨x, h1, h2, h3, h4⟩⟩
    have eq1 : (x : ℝ) ^ 2 + a * (x : ℝ) + a = b := by 
      exact_mod_cast h1 
    have eq2 : (x + 1 : ℝ) ^ 2 + a * (x + 1 : ℝ) + a = -b := by 
      exact_mod_cast h2 
    have eq3 : (x + 2 : ℝ) ^ 2 + a * (x + 2 : ℝ) + a = -b := by 
      exact_mod_cast h3 
    have eq4 : (x + 3 : ℝ) ^ 2 + a * (x + 3 : ℝ) + a = b := by 
      exact_mod_cast h4 
    have eq5 : 2 * (x : ℝ) + a = -3 := by
      ring_nf at eq1 eq4
      nlinarith 
    have eq6 : a = -3 - 2 * (x : ℝ) := by 
      linarith 
    have eq7 : (x : ℝ) ^ 2 + a * (x : ℝ) + a = b := by 
      exact_mod_cast h1 
    rw [eq6] at eq7 
    have eq8 : (x + 1 : ℝ) ^ 2 + a * (x + 1 : ℝ) + a = -b := by 
      exact_mod_cast h2 
    rw [eq6] at eq8 
    have eq9 : b = - (x : ℝ) ^ 2 - 5 * (x : ℝ) - 3 := by 
      nlinarith 
    have eq10 : b = (x : ℝ) ^ 2 + 5 * (x : ℝ) + 5 := by 
      nlinarith 
    have eq11 : (x : ℝ) ^ 2 + 5 * (x : ℝ) + 4 = 0 := by 
      nlinarith 
    have eq12 : (x : ℝ) ^ 2 + 5 * (x : ℝ) + 4 = ((x : ℝ) + (1 : ℝ)) * ((x : ℝ) + (4 : ℝ)) := by 
      ring 
    rw [eq12] at eq11 
    cases' (mul_eq_zero.mp eq11) with h5 h6 
    · -- Case `h5 : (x : ℝ) + 1 = 0`. This means x = -1 as integer. 
      have eq13 : (x : ℝ) = -1 := by 
        nlinarith 
      have eq14 : x = -1 := by 
        have h15 : (x : ℝ) = -1 := by 
          linarith 
        exact_mod_cast h15 
      have eq15 : a = -1 := by 
        rw [eq6]
        have eq16 : (x : ℝ) = -1 := by 
          linarith 
        rw [eq16]
        norm_num 
      have eq16 : b = 1 := by 
        rw [eq9]
        have eq17 : (x : ℝ) = -1 := by 
          linarith 
        rw [eq17]
        norm_num 
      simp [eq15, eq16] 
    · -- Case h6 : (x : ℝ) + 4 = 0 
      have eq13 : (x : ℝ) = -4 := by 
        nlinarith 
      have eq14 : x = -4 := by 
        have h15 : (x : ℝ) = -4 := by 
          linarith 
        exact_mod_cast h15 
      have eq15 : a = 5 := by 
        rw [eq6]
        have eq16 : (x : ℝ) = -4 := by 
          linarith 
        rw [eq16]
        norm_num 
      have eq16 : b = 1 := by 
        rw [eq9]
        have eq17 : (x : ℝ) = -4 := by 
          linarith 
        rw [eq17]
        norm_num 
      simp [eq15, eq16] 
  · -- Show RHS in LHS 
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Case a = -1, b = 1 
      constructor 
      · norm_num 
      · -- Show existence of integer x = -1 
        use -1 
        norm_num 
    · -- Case a = 5, b = 1 
      constructor 
      · norm_num 
      · -- Show existence of integer x = -4 
        use -4 
        norm_num