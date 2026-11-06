import Mathlib

theorem algebra_150634 {x : ℝ} (hx : ⌊x⌋ * (x - ⌊x⌋) + x = 2 * (x - ⌊x⌋) + 9) :
    x = 9 ∨ x = 8 + 1 / 7 ∨ x = 7 + 1 / 3 ∨ x = 6 + 3 / 5 := by 
  let n := ⌊x⌋
  have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
  have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have hn1' : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hn1
  have hn2' : (x : ℝ) < (n + 1 : ℝ) := by exact_mod_cast hn2
  have h_eq : (n : ℝ) * (x - ↑n) + x = 2 * (x - ↑n) + 9 := by
    simpa using hx
  have h3 : (n : ℝ) ≤ (x : ℝ) := hn1'
  have h4 : (x : ℝ) < (n + 1 : ℝ) := hn2'
  have h5 : n ≤ 9 := by
    by_contra h
    push_neg at h
    have hn3 : n ≥ 10 := by omega
    have h6 : (n : ℝ) ≥ (10 : ℝ) := by exact_mod_cast hn3
    nlinarith [sq_nonneg ((x : ℝ) - (n : ℝ)), sq_nonneg ((n : ℝ) - (10 : ℝ))]
  have h7 : n ≥ 1 := by
    by_contra h
    push_neg at h
    have hn8 : n ≤ 0 := by omega
    have hn9 : n ≤ 0 := by omega
    have hn10 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn9
    nlinarith [sq_nonneg ((x : ℝ) - (n : ℝ)), sq_nonneg ((n : ℝ) - (0 : ℝ))]
  have hn8 : n ≤ 9 := by linarith
  have hn9 : n ≥ 1 := by linarith
  interval_cases n <;> norm_num at h_eq hn1' hn2' ⊢ 
    <;> try { 
      have hx10 : x = 9 := by
        nlinarith
      left
      linarith
    }
    <;> try { 
      have hx11 : x = 8 + 1 / 7 := by
        nlinarith
      right
      left
      linarith
    }
    <;> try { 
      have hx12 : x = 7 + 1 / 3 := by
        nlinarith
      right
      right
      left
      linarith
    }
    <;> try { 
      have hx13 : x = 6 + 3 / 5 := by
        nlinarith
      right
      right
      right
      linarith
    }