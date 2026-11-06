import Mathlib

open Real

theorem other_143880 : ¬∃ n : ℕ, n > 0 ∧ (1 / sqrt 2) * n = 1 := by
  rintro ⟨n, hn1, hn2⟩
  have h1 : (Real.sqrt 2 : ℝ) = (n : ℝ) := by
    field_simp at hn2 
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h4 : (n : ℝ) ^ 2 = (2 : ℝ) := by 
    have h10 : (Real.sqrt 2 : ℝ) = (n : ℝ) := h1 
    have h11 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := by 
      exact Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    rw [h10] at h11
    linarith
  have h9 : (n : ℝ) > (0 : ℝ) := by
    have hn1' : n > 0 := hn1
    have : (n : ℝ) > (0 : ℝ) := by exact_mod_cast hn1'
    linarith
  have h12 : (n : ℝ) = Real.sqrt 2 := by
    have h13 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    have h14 : (n : ℝ) ^ 2 = (Real.sqrt 2) ^ 2 := by
      linarith [h4, h13]
    have h15 : (n : ℝ) ≥ 0 := by
      have hn1' : n > 0 := hn1
      have : (n : ℝ) > (0 : ℝ) := by exact_mod_cast hn1'
      linarith
    have h16 : Real.sqrt 2 ≥ 0 := by
      positivity
    have h17 : (n : ℝ) = Real.sqrt 2 := by
      nlinarith [h14, h15, h16, Real.sqrt_nonneg 2]
    exact h17
  -- Now h1 : Real.sqrt 2 = n now needs separating it. As our chosen earlier with native_decide or now in its misapplied. Note will travel free variable thus removing this.
  have h14 : ( (n : ℕ) : ℝ ) ^ 2 = 2 := by
    have h14a : (n : ℝ) ^ 2 = (2 : ℝ) := h4
    norm_cast at h14a ⊢
  -- contradiction as there's no integer n s.t n^2 =2.
  have h15 : ( (n : ℕ) ) ^ 2 = 2 := by
    have h14a : (n : ℝ) ^2 = (2 : ℝ) := h4
    have h16 : ( (n : ℕ) : ℝ ) ^2 = (2 : ℝ) := by
      simpa using h14a
    have h17 : ( (n : ℕ) ) ^2 = (2 : ℕ) := by
      have eq18 : ( (n : ℕ) : ℝ ) ^2 = (2 : ℝ) := h16
      have eq19 : ( ( (n : ℕ ) ^2) : ℝ) = (2 : ℝ) := by
        nlinarith
      exact_mod_cast eq19
    assumption
  have h18 : n ≤ 1 := by
    by_contra h
    push_neg at h
    have h19 : n ≥ 2 := by
      omega
    have h20 : n ^ 2 ≥ 4 := by
      nlinarith [h19, show 0 ≤ (n : ℕ) by omega]
    have h21 : n ^ 2 = 2 := h15
    linarith 
  have hn1' : n > 0 := hn1
  have hn11 : n ≥ 1 := by
    omega
  interval_cases n <;> norm_num at h15 hn1 <;> tauto