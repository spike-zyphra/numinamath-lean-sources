import Mathlib

theorem algebra_8298 {x : ℝ} (hx : x^2 - 8 * ⌊x⌋ + 7 = 0) :
    x = 1 ∨ x = Real.sqrt 33 ∨ x = Real.sqrt 41 ∨ x = 7 := by
  have h1 : ⌊x⌋ ≤ (x : ℝ) := by
    exact Int.floor_le x
  have h2 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
    exact Int.lt_floor_add_one x

  have h4 : ⌊x⌋ ≤ 7 := by
    by_contra h
    push_neg at h
    have h5 : ⌊x⌋ ≥ 8 := by
      omega
    have h6 : (⌊x⌋ : ℝ) ≥ (8 : ℝ) := by
      exact_mod_cast h5
    nlinarith [show x^2 ≥ 0 by nlinarith, sq_nonneg (x - (⌊x⌋ : ℝ)), h1, h2, sq_nonneg (x + (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ + 1 : ℝ) - x)]
  have h5 : ⌊x⌋ ≥ 1 := by
    by_contra h
    push_neg at h
    have h7 : ⌊x⌋ ≤ 0 := by
      omega
    have h8 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by
      exact_mod_cast h7
    nlinarith [show x^2 ≥ 0 by nlinarith, sq_nonneg (x - (⌊x⌋ : ℝ)), h1, h2, sq_nonneg (x + (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ + 1 : ℝ) - x)]
  have h0 : ⌊x⌋ ≥ 1 := h5 
  have h11 : ⌊x⌋ ≤ 7 := h4 
  have h33 : ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 ∨ ⌊x⌋ = 3 ∨ ⌊x⌋ = 4 ∨ ⌊x⌋ = 5 ∨ ⌊x⌋ = 6 ∨ ⌊x⌋ = 7 := by 
    omega 
  rcases h33 with (h | h | h | h | h | h | h)
  · -- case n = 1
    have hn1 : ⌊x⌋ = 1 := by 
      omega 
    have h_eq1 : x ^ 2 = 1 := by 
      have h6 : (⌊x⌋ : ℝ) = 1 := by
        exact_mod_cast hn1 
      nlinarith 
    have h_eq3 : x ^ 2 - 1 = 0 := by 
      linarith 
    have h_eq6 : x = 1 := by 
      nlinarith [sq_nonneg (x - 1), h1, h2] 
    left 
    exact h_eq6 
  · -- case n = 2 
    exfalso 
    have h44 : ⌊x⌋ = 2 := by 
      omega 
    have h44' : (⌊x⌋ : ℝ) = 2 := by 
      exact_mod_cast h44 
    have h55 : x >= (⌊x⌋ : ℝ) := by 
      exact_mod_cast h1 
    have h55' : x < (⌊x⌋ + 1 : ℝ) := by 
      exact_mod_cast h2 
    nlinarith [show x ^ 2 ≥ 0 by nlinarith, sq_nonneg ((x) - (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ + 1 : ℝ) - (x))]
  · -- case n = 3 
    exfalso 
    have h44 : ⌊x⌋ = 3 := by 
      omega 
    have h44' : (⌊x⌋ : ℝ) = 3 := by 
      exact_mod_cast h44 
    have h55 : x >= (⌊x⌋ : ℝ) := by 
      exact_mod_cast h1 
    have h55' : x < (⌊x⌋ + 1 : ℝ) := by 
      exact_mod_cast h2 
    nlinarith [show x ^ 2 ≥ 0 by nlinarith, sq_nonneg ((x) - (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ + 1 : ℝ) - (x))]
  · -- case n = 4 
    exfalso 
    have h44 : ⌊x⌋ = 4 := by 
      omega 
    have h44' : (⌊x⌋ : ℝ) = 4 := by 
      exact_mod_cast h44 
    have h55 : x >= (⌊x⌋ : ℝ) := by 
      exact_mod_cast h1 
    have h55' : x < (⌊x⌋ + 1 : ℝ) := by 
      exact_mod_cast h2 
    nlinarith [show x ^ 2 ≥ 0 by nlinarith, sq_nonneg ((x) - (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ + 1 : ℝ) - (x))]
  · -- case n = 5 
    have hn5 : ⌊x⌋ = 5 := by 
      omega 
    have h11 : (⌊x⌋ : ℝ) = 5 := by 
      exact_mod_cast hn5 
    have h12 : x ^ 2 = 33 := by 
      nlinarith 
    have h13 : x = Real.sqrt 33 := by 
      have h14 : x ^ 2 = (33 : ℝ) := h12 
      have h15 : x ≥ 0 := by nlinarith 
      have h16 : x = Real.sqrt 33 := by 
        rw [← h14] 
        field_simp 
      exact h16 
    right 
    left 
    exact h13 
  · -- case n = 6
    have hn6 : ⌊x⌋ = 6 := by 
      omega 
    have h21 : (⌊x⌋ : ℝ) = 6 := by 
      exact_mod_cast hn6 
    have h22 : x ^ 2 = 41 := by 
      nlinarith 
    have h10 : x ≥ 0 := by 
      nlinarith 
    have h23 : x = Real.sqrt 41 := by 
      have h24 : x ^ 2 = (41 : ℝ) := h22 
      have h25 : x ≥ 0 := by nlinarith 
      have h26 : x = Real.sqrt 41 := by 
        rw [← h24] 
        field_simp 
      exact h26 
    right 
    right 
    left 
    exact h23 
  · -- case n = 7 
    have hn7 : ⌊x⌋ = 7 := by 
      omega 
    have h31 : (⌊x⌋ : ℝ) = 7 := by 
      exact_mod_cast hn7 
    have h32 : x ^ 2 = 49 := by 
      nlinarith 
    have h35 : x = 7 := by 
      nlinarith [sq_nonneg (x - 7)]
    right 
    right 
    right 
    exact h35