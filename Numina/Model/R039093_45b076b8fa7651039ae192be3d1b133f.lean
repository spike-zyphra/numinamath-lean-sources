import Mathlib

theorem algebra_12981 : IsGreatest {(x : ℝ) | ⌊x⌋ = 5 + 100 * (x - ⌊x⌋)} 104.99 := by 
  constructor
  · -- Show that 104.99 is in the set 
    show ⌊(104.99 : ℝ)⌋ = 5 + 100 * ((104.99 : ℝ) - ⌊(104.99 : ℝ)⌋)
    norm_num 
  · -- Show that for all x in the set, x ≤ 104.99 
    intro x hx 
    have h_eq : ⌊x⌋ = 5 + 100 * (x - ⌊x⌋) := hx 
    let n := ⌊x⌋ 
    have hn1 : n = ⌊x⌋ := rfl 
    have h_eq1 : (n : ℝ) = 5 + 100 * (x - (n : ℝ)) := by 
      simpa using h_eq 
    have hn2 : (n : ℝ) ≤ x := by 
      exact Int.floor_le x 
    have hn3 : x < (n + 1 : ℝ) := by 
      exact Int.lt_floor_add_one x 
    have hn4 : n ≥ 5 := by 
      by_contra h 
      push_neg at h 
      have : n < 5 := by omega 
      have h4 : (n : ℝ) < (5 : ℝ) := by exact_mod_cast this 
      nlinarith 
    have hn5 : n < 105 := by 
      by_contra h 
      push_neg at h 
      have : n ≥ 105 := by omega 
      have h6 : (n : ℝ) ≥ (105 : ℝ) := by exact_mod_cast this 
      nlinarith 
    have h_eq2 : (x : ℝ) = (101 * (n : ℝ) - 5 ) / 100 := by 
      nlinarith 
    have hn6 : (n : ℝ) ≤ (104 : ℝ) := by
      exact_mod_cast (show n ≤ 104 by omega)
    rw [h_eq2]
    nlinarith [ show (n : ℝ) ≤ (104 : ℝ) by exact_mod_cast (show n ≤ 104 by omega) ]