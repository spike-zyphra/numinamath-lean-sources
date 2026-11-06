import Mathlib

theorem number_theory_209198 {x : ℝ} (hx : x > 0) (h : ∃ r, Int.fract x = r * x ∧ x = r * Int.floor x) :
    x = (Real.sqrt 5 + 1) / 2 := by
  rcases h with ⟨r, hfrac, h2⟩
  have h3 : Int.fract x = x - (Int.floor x : ℝ) := by
    rw [Int.fract]
    <;> ring_nf <;> simp [Int.floor]
  rw [h3] at hfrac
  have h8 : (Int.floor x : ℝ) ≤ x := by exact_mod_cast Int.floor_le x
  have h9 : x < (Int.floor x + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one x
  have h14 : (Int.floor x : ℝ) ≥ 0 := by
    by_contra h
    push_neg at h
    have h7 : (Int.floor x : ℝ) < (0 : ℝ) := by nlinarith
    have h8 : Int.floor x < 0 := by 
      by_contra h8
      push_neg at h8
      have h9 : Int.floor x ≥ 0 := h8
      have h9 : (Int.floor x : ℝ) ≥ (0 : ℝ) := by exact_mod_cast h9
      linarith
    have h9 : Int.floor x ≤ (-1 : Int) := by
      omega
    have h10 : (Int.floor x : ℝ) ≤ (-1 : ℝ) := by
      exact_mod_cast h9
    nlinarith
  have hn0 : Int.floor x ≥ 0 := by
    by_contra h
    push_neg at h
    have h7 : Int.floor x < 0 := by
      omega
    have h8 : (Int.floor x : ℝ) < (0 : ℝ) := by
      nlinarith [show (Int.floor x : ℝ) < (0 : ℝ) by exact_mod_cast h7]
    have h8 : x < (0 : ℝ) := by
      nlinarith
    linarith
  have hn0' : (Int.floor x : ℝ) ≥ 0 := by
    exact_mod_cast hn0
  by_cases h15 : Int.floor x > 0
  · -- Assume Int.floor x > 0.
    have hn1 : Int.floor x ≥ 1 := by
      omega
    have hn1' : (Int.floor x : ℝ) ≥ (1 : ℝ) := by
      exact_mod_cast hn1
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
      hfrac, h2, sq_nonneg (x - (Int.floor x : ℝ)), sq_nonneg (x - 1), sq_nonneg (r - 1)]
  · -- Assume Int.floor x = 0
    have hn1 : Int.floor x = 0 := by
      omega
    have hn1' : (Int.floor x : ℝ) = (0 : ℝ) := by
      exact_mod_cast hn1
    rw [hn1'] at h2
    have hr0 : r = 0 := by
      nlinarith
    rw [hr0] at hfrac
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
      sq_nonneg (x - 1), sq_nonneg (r), sq_nonneg (x - (Real.sqrt 5 + 1) / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]