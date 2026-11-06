import Mathlib

theorem algebra_212163 {x : ℚ} (hx : x ≠ 0) :
    ⌊x⌋ * (x - ⌊x⌋) + x = 2 * (x - ⌊x⌋) + 10 ↔
    x = 10 ∨ x = 7 + 1 / 2 ∨ x = 9 + 1 / 8 ∨ x = 8 + 2 / 7 ∨ x = 6 + 4 / 5 := by
  constructor
  · -- Assume the equation holds, we need to prove x is one of the solutions
    intro h
    let n := ⌊x⌋
    have hn1 : n ≤ (x : ℚ) := by exact Int.floor_le x
    have hn2 : (x : ℚ) < (n + 1 : ℚ) := by exact Int.lt_floor_add_one x
    have h_eq2 : (n : ℚ) * (x - (n : ℚ)) + x = 2 * (x - (n : ℚ)) + 10 := by 
      simpa using h 
    have h1 : (n : ℚ) ≤ x := by exact_mod_cast hn1
    have h2 : x < (n + 1 : ℚ) := by exact_mod_cast hn2
    have h3 : n ≤ 10 := by
      by_contra h
      push_neg at h
      have h4 : n ≥ 11 := by omega
      have h5 : (n : ℚ) ≥ 11 := by exact_mod_cast (show n ≥ 11 by omega)
      have h6 : (n - 1 : ℚ) ≥ 10 := by nlinarith
      have h7 : x - (n : ℚ) ≥ 0 := by linarith
      nlinarith
    have h4 : n ≥ 0 := by
      by_contra h
      push_neg at h
      have h5 : n ≤ -1 := by omega
      have h6 : (n : ℚ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith
    interval_cases n <;> norm_num at h_eq2 h1 h2 
      <;> try { 
        have h5 : x = 10 := by nlinarith 
        left 
        linarith 
      } 
      <;> try { 
        have h5 : x = 7 + 1 / 2 := by nlinarith 
        right 
        left 
        linarith 
      } 
      <;> try { 
        have h5 : x = 9 + 1 / 8 := by nlinarith 
        right 
        right 
        left 
        linarith 
      } 
      <;> try { 
        have h5 : x = 8 + 2 / 7 := by nlinarith 
        right 
        right 
        right 
        left 
        linarith 
      } 
      <;> try { 
        have h5 : x = 6 + 4 / 5 := by nlinarith 
        right 
        right 
        right 
        right 
        linarith 
      }
  · -- Assume the solutions satisifes the equation.
    rintro (rfl | rfl | rfl | rfl | rfl)
    · -- Check x = 10 
      norm_num
    · -- Check x = 7 + 1/2 
      norm_num 
    · -- Check x = 9 + 1/8 
      norm_num 
    · -- Check x = 8 + 2/7 
      norm_num 
    · -- Check x = 6 + 4/5 
      norm_num