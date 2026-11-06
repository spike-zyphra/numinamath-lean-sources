import Mathlib

open scoped BigOperators

theorem algebra_243328 (k : ℕ) (hk : 0 < k) (a : ℕ → ℝ)
  (ha0 : a 0 = 1 / k) (han : ∀ n, a (n + 1) = a n + (1 / (n + 1)^2) * (a n)^2)
  (h : ∀ n, 0 < n → a n < 1) :
  3 ≤ k := by
  by_contra h'
  push_neg at h'
  have h1 : k < 3 := by linarith
  have h2 : k = 1 ∨ k = 2 := by
    interval_cases k <;> omega
  rcases h2 with (h2 | h2)
  · -- k = 1
    have k1 : (k : ℝ) = (1 : ℝ) := by exact_mod_cast h2
    have ha1 : a 1 < 1 := h 1 (by norm_num)
    -- Compute a1
    have ha0' : a 0 = (1 / 1 : ℝ) := by 
      rw [k1] at ha0
      linarith 
    have eq1 := han 0
    norm_num [ha0'] at eq1 
    have eq2 : a 1 = (2 : ℝ) := by
      nlinarith 
    linarith [eq2, ha1]
  · -- k = 2
    have k2 : (k : ℝ) = (2 : ℝ) := by exact_mod_cast h2
    have ha0' : a 0 = (1 / 2 : ℝ) := by
      rw [k2] at ha0
      norm_num at ha0 ⊢ 
      linarith 
    have ha1 : a 1 < 1 := h 1 (by norm_num)
    have eq10 := han 0 
    norm_num [ha0'] at eq10 
    -- Compute a2
    have ha2 : a 2 < 1 := h 2 (by norm_num)
    have eq20 := han 1
    norm_num at eq20 
    -- Compute a3
    have ha3 : a 3 < 1 := h 3 (by norm_num)
    have eq30 := han 2
    norm_num at eq30 
    -- Compute a4
    have ha4 : a 4 < 1 := h 4 (by norm_num)
    have eq40 := han 3
    norm_num at eq40 
    -- Compute a5
    have ha5 : a 5 < 1 := h 5 (by norm_num)
    have eq50 := han 4
    norm_num at eq50 
    -- Compute a6
    have ha6 : a 6 < 1 := h 6 (by norm_num)
    have eq60 := han 5
    norm_num at eq60 
    -- Compute a7
    have ha7 : a 7 < 1 := h 7 (by norm_num)
    have eq70 := han 6
    norm_num at eq70 
    norm_num [k2] at ha0' eq10 eq20 eq30 eq40 eq50 eq60 eq70 ha0' ha1 ha2 ha3 ha4 ha5 ha6 
    all_goals
      nlinarith