import Mathlib

theorem algebra_316091 {x y : ℝ} (hx : x ≠ 0)
    (h : 4 * x + 3 * y - 2 * x * ⌊(x ^ 2 + y ^ 2) / x ^ 2⌋ = 0) :
    y / x = -2 / 3 ∨ y / x = 2 := by
  let n := ⌊(x ^ 2 + y ^ 2) / x ^ 2⌋
  have h_eq : (4 * x + 3 * y) = 2 * x * (n : ℝ) := by
    have h1 : (4 * x + 3 * y - 2 * x * (n : ℝ)) = 0 := by
      simpa using h
    linarith 
  have h1 : (n : ℝ) ≤ (x ^ 2 + y ^ 2) / x ^ 2 := by 
    exact Int.floor_le ((x ^ 2 + y ^ 2) / x ^ 2)
  have h2 : (x ^ 2 + y ^ 2) / x ^ 2 < (n + 1 : ℝ) := by 
    exact Int.lt_floor_add_one ((x ^ 2 + y ^ 2) / x ^ 2)
  have eq6 : y = x * ( (2 * (n : ℝ) - 4) / 3 ) := by
    have eq3 : (4 * x + 3 * y) = 2 * x * (n : ℝ) := h_eq 
    have eq8 : 3 * y = x * (2 * (n : ℝ) - 4) := by 
      nlinarith 
    have eq3' : y = x * ( (2 * (n : ℝ) - 4) / 3 ) := by
      have eq8' : 3 * y = x * (2 * (n : ℝ) - 4) := eq8
      have eq9 : y = (x * (2 * (n : ℝ) - 4)) / 3 := by
        linarith 
      field_simp at eq9 ⊢
      <;> linarith 
    linarith 
  have eq1' : y / x = (2 * (n : ℝ) - 4) / 3 := by 
    have eq6' : y = x * ( (2 * (n : ℝ) - 4) / 3 ) := eq6 
    have eq7 : y / x = (2 * (n : ℝ) - 4) / 3 := by 
      have eq8 : y = x * ( (2 * (n : ℝ) - 4) / 3 ) := eq6 
      have eq9 : y / x = (2 * (n : ℝ) - 4) / 3 := by 
        field_simp [hx] at *
        nlinarith 
      linarith 
    linarith 
  have h3 : (n : ℝ) - 1 ≤ (y / x) ^ 2 := by
    have h4 : (n : ℝ) ≤ (x ^ 2 + y ^ 2) / x ^ 2 := h1 
    have h5 : (x ^ 2 + y ^ 2) / x ^ 2 = 1 + (y / x) ^ 2 := by
      field_simp 
      <;> nlinarith 
    nlinarith [h4, h5] 
  have h4 : (y / x) ^ 2 < (n : ℝ) := by 
    have h5 : (x ^ 2 + y ^ 2) / x ^ 2 < (n + 1 : ℝ) := h2 
    have h6 : (x ^ 2 + y ^ 2) / x ^ 2 = 1 + (y / x) ^ 2 := by 
      field_simp 
      <;> nlinarith 
    nlinarith [h5, h6] 
  rw [eq1'] at h3 h4
  have h8 : n ≥ 1 := by 
    by_contra h 
    push_neg at h 
    have h9 : n ≤ 0 := by omega 
    have h10 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h9 
    nlinarith [sq_nonneg ((2 * (n : ℝ) - 4) / 3), sq_nonneg ((n : ℝ) - 1) ]
  have h9 : n ≤ 5 := by 
    by_contra h 
    push_neg at h 
    have h10 : n ≥ 6 := by omega 
    have h11 : (n : ℝ) ≥ (6 : ℝ) := by exact_mod_cast h10 
    nlinarith [sq_nonneg ((2 * (n : ℝ) - 4) / 3), sq_nonneg ((n : ℝ) - 1) ]
  have h7 : n = 1 ∨ n = 5 := by 
    interval_cases n <;> norm_num at h3 h4 <;> 
      try { 
        omega 
      }
  rcases h7 with (h7 | h7)
  · -- n = 1 
    have eq1_n : (n : ℝ) = 1 := by exact_mod_cast h7 
    rw [eq1_n] at eq1' 
    left 
    linarith 
  · -- n = 5 
    have eq1_n : (n : ℝ) = 5 := by exact_mod_cast h7 
    rw [eq1_n] at eq1' 
    right 
    linarith