import Mathlib

theorem algebra_324965 {x : ℝ} (hx : ¬∃ n : ℤ, x = n) (h : x + 113 / x = ⌊x⌋ + 113 / ⌊x⌋) :
    x = -10 - 3 / 11 := by
  let n := ⌊x⌋
  have h1 : n ≤ (x : ℝ) := by 
    exact Int.floor_le x
  have h2 : (x : ℝ) < (n + 1 : ℝ) := by
    exact Int.lt_floor_add_one x
  have h3 : (x : ℝ) ≠ (n : ℝ) := by
    by_contra h_eq
    have h4 : ∃ k : ℤ, x = (k : ℝ) := by 
      refine' ⟨n, by linarith⟩
    contradiction
  have h4 : (n : ℝ) < (x : ℝ) := by 
    by_contra h_eq
    have h_eq2 : (x : ℝ) ≤ (n : ℝ) := by linarith
    have h_eq2 : (x : ℝ) = (n : ℝ) := by linarith [h1, h_eq2]
    contradiction
  have h5 : (n : ℝ) ≠ 0 := by
    by_contra h_eq
    have hn0 : (n : ℝ) = (0 : ℝ) := by linarith
    -- If n = 0 then 0 < x < 1, so x + 113 / x = 0 + 0 = 0. This forces x = 0, which is a contradiction
    have h6 : (n : ℝ) = (0 : ℝ) := by linarith
    have h7 : (x : ℝ) > (0 : ℝ) := by
      have h8 : (n : ℝ) = (0 : ℝ) := by linarith
      nlinarith [show (x : ℝ) > (n : ℝ) by linarith [h4, hn0], hn0]
    -- If n = 0 then original equation implies x + 113/x = 0.
    have eq1 : x + 113 / x = (0 : ℝ) := by 
      rw [show (n : ℝ) = (0 : ℝ) by linarith] at h 
      norm_num [h_eq] at h ⊢
      all_goals 
        linarith 
    -- This implies x = 0.
    have hxne0 : x ≠ (0 : ℝ) := by 
      nlinarith [h4, hn0]
    -- Multiply eq1 by x
    have eq2 : x ^ 2 + 113 = (0 : ℝ) := by
      have hxne0' : x ≠ 0 := hxne0
      field_simp at eq1
      nlinarith
    nlinarith [sq_nonneg (x) ]
  -- manipulating the equation
  have h6 : x + 113 / x = (n : ℝ) + 113 / (n : ℝ) := by 
    simpa using h
  have h7 : x ≠ (0 : ℝ) := by 
    by_contra h_eq
    rw [show x = (0 : ℝ) by linarith] at h6 
    field_simp [h5] at h6 
    all_goals 
      nlinarith 
  have h8 : (n : ℝ) ≠ (0 : ℝ) := by 
    exact_mod_cast h5 
  -- manipulating the equation
  have heq : (n : ℝ) * x = 113 := by
    have eq2 : (x - (n : ℝ)) * ((n : ℝ) * x - 113) = 0 := by
      have eq1 : x + 113 / x = (n : ℝ) + 113 / (n : ℝ) := h6
      field_simp [h7, h8] at eq1 ⊢
      nlinarith [sq_nonneg (x * (n : ℝ)), sq_nonneg (x - (n : ℝ)), sq_nonneg ((n : ℝ)), sq_nonneg (x)]
    cases' (mul_eq_zero.1 eq2) with h9 h10
    · -- First side gives x = n, which we know is false
      exfalso
      apply h3
      linarith
    · -- Second side gives n * x = 113
      linarith
  -- derived n
  have hn11 : n = -11 := by 
    have h50 : n ≤ 10 := by
      by_contra h9
      push_neg at h9
      have h9' : n ≥ 11 := by
        omega
      have h10 : (n : ℝ) ≥ (11 : ℝ) := by
        exact_mod_cast h9'
      nlinarith [sq_nonneg (x - (11 : ℝ)), sq_nonneg ((n : ℝ) - 11), sq_nonneg (x * (n : ℝ)), 
          heq, h1, h2]
    have h51 : n ≥ -11 := by
      by_contra h9
      push_neg at h9
      have h9' : n ≤ -12 := by
        omega
      have h10 : (n : ℝ) ≤ (-12 : ℝ) := by
        exact_mod_cast h9'
      nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg ((n : ℝ) + 12), sq_nonneg (x * (n : ℝ)), 
          heq, h1, h2]
    interval_cases n <;> norm_num at heq h1 h2 h4 <;> norm_num at heq ⊢ 
      <;> nlinarith
  -- derived x
  have h20 : (n : ℝ) = (-11 : ℝ) := by 
    exact_mod_cast hn11
  have h21 : x = (-113 / 11 : ℝ) := by
    rw [h20] at heq 
    linarith
  rw [h21]
  norm_num