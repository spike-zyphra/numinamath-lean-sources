import Mathlib

theorem algebra_321791 {a : ℝ} (ha : a > 0) (h : ∃ r, a * r = ⌊a⌋ ∧ a * r^2 = a - ⌊a⌋) :
    a = (1 + Real.sqrt 5) / 2 := by 
  rcases h with ⟨r, h1, h2⟩
  have h3 : (⌊a⌋ : ℝ) ≤ a := by 
    exact_mod_cast (Int.floor_le a)
  have h4 : a < (⌊a⌋ + 1 : ℝ) := by 
    exact_mod_cast (Int.lt_floor_add_one a)
  have h5 : (⌊a⌋ : ℝ) ≥ 0 := by
    have h6 : (⌊a⌋ : ℝ) ≥ (0 : ℝ) := by
      have h7 : ⌊a⌋ ≥ 0 := by
        by_contra h
        push_neg at h
        have h8 : ⌊a⌋ ≤ -1 := by omega
        have h9 : (⌊a⌋ : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h8
        have h10 : a < (⌊a⌋ + 1 : ℝ) := by 
          exact_mod_cast (Int.lt_floor_add_one a)
        nlinarith [show a > 0 by linarith]
      exact_mod_cast h7
    linarith
  have eq1 : a * r^2 + a * r - a = 0 := by
    nlinarith
  have eq2 : a * (r^2 + r - 1) = 0 := by
    nlinarith
  have eq3 : r^2 + r - 1 = 0 := by 
    apply (mul_left_inj' (ne_of_gt ha)).mp
    linarith
  have h8 : ⌊a⌋ ≥ 0 := by 
    by_contra h
    push_neg at h
    have h9 : ⌊a⌋ ≤ -1 := by omega
    have h10 : (⌊a⌋ : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h9
    have h11 : a < (⌊a⌋ + 1 : ℝ) := by 
      exact_mod_cast (Int.lt_floor_add_one a)
    nlinarith [show a > 0 by linarith]
  have h9 : ⌊a⌋ = 0 ∨ ⌊a⌋ = 1 ∨ ⌊a⌋ ≥ 2 := by
    have h10 : ⌊a⌋ ≥ 0 := by
      exact Int.floor_nonneg.mpr (by linarith)
    have h11 : ⌊a⌋ ≤ 1 ∨ ⌊a⌋ ≥ 2 := by
      by_cases h3 : ⌊a⌋ ≤ 1
      · left
        omega
      · right
        have h4 : ⌊a⌋ ≥ 2 := by omega
        omega
    omega
  rcases h9 with h10 | h11 | h12
  · -- Case where ⌊a⌋ = 0
    have h13 : (⌊a⌋ : ℝ) = (0 : ℝ) := by
      exact_mod_cast h10
    have h14 : a * r = 0 := by
      nlinarith [h13, h1]
    have h15 : r = 0 := by
      nlinarith [h14, show a > 0 by linarith]
    rw [h15] at eq3
    nlinarith
  · -- Case where ⌊a⌋ = 1
    have h16 : (⌊a⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h11
    have h17 : a * r = 1 := by
      nlinarith [h16, h1]
    have h18 : r > 0 := by
      nlinarith [h17, show a > 0 by linarith]
    have h19 : r = (Real.sqrt 5 - 1) / 2 := by
      have hr_eq : r^2 + r - 1 = 0 := eq3
      have : r^2 + r - 1 = (r - (Real.sqrt 5 - 1) / 2) * (r - (-1 - Real.sqrt 5) / 2) := by
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        linarith
      rw [this] at hr_eq
      cases (mul_eq_zero.mp hr_eq) with
      | inl h => 
        linarith
      | inr h => 
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have h20 : a = (1 + Real.sqrt 5) / 2 := by
      nlinarith [h17, h19, Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num ) ]
    linarith [h20]
  · -- Case where ⌊a⌋ ≥ 2
    have h22 : (⌊a⌋ : ℝ) ≥ (2 : ℝ) := by
      have h23 : ⌊a⌋ ≥ 2 := by 
        omega
      exact_mod_cast h23
    have h23 : a * r ≥ (2 : ℝ) := by 
      nlinarith [show (⌊a⌋ : ℝ) ≥ (2 : ℝ) by nlinarith, h1]
    nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (a - (1 + Real.sqrt 5) / 2), sq_nonneg (r - (Real.sqrt 5 - 1) / 2) ]