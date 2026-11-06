import Mathlib

theorem number_theory_303940 (a : ℕ → ℤ) (ha : ∀ n, a n > 0)
    (h : ∀ n, a n^2 + a (n + 1)^2 = a (n + 2)^2) :
    ¬∃ r, ∀ n, a (n + 1) = r * a n ∧
    ¬∃ r, ∀ n, a (n + 1) = r / a n := by 
  rintro ⟨r, hr⟩
  have h0 := h 0
  have h1 := h 1
  have hr0 := (hr 0).1
  have hr1 := (hr 1).1
  have hr2 := (hr 2).1
  have hr3 := (hr 3).1
  have eq1 : a 1 = r * a 0 := by 
    simpa using hr0
  have eq2 : a 2 = r * a 1 := by 
    simpa using hr1
  have ha1 : a 1 = r * a 0 := eq1
  have ha2 : a 2 = r * a 1 := by simpa using hr1
  rw [ha1] at ha2
  -- Now we have a 2 = r * (r * a 0)
  have eq3 : a 0 ^ 2 + a 1 ^ 2 = a 2 ^ 2 := by 
    simpa using h0
  -- Substitute a 1 and a 2 in the equation.
  have eq3' : a 0 ^ 2 + (r * a 0) ^ 2 = (r * (r * a 0)) ^ 2 := by
    rw [show a 1 = r * a 0 by linarith [eq1] ] at eq3
    rw [show a 2 = r * (r * a 0) by nlinarith [eq1, ha2] ] at eq3
    all_goals 
      nlinarith
  -- Now we derive the polynomial equation r^4 - r^2 - 1 = 0
  have h_eq : (r : ℤ) ^ 4 - (r : ℤ) ^ 2 - 1 = 0 := by
    have h02 : a 0 ^ 2 > 0 := by nlinarith [ha 0]
    have comb_eq : a 0 ^ 2 + (r * a 0) ^ 2 = (r * (r * a 0)) ^ 2 := eq3'
    have eq5 : (r : ℤ) ^ 4 - (r : ℤ) ^ 2 - 1 = 0 := by
      have h11 : a 0 ^ 2 * (1 + r ^ 2) = a 0 ^ 2 * r ^ 4 := by
        nlinarith [comb_eq]
      have h12 : a 0 ^ 2 > 0 := h02
      have eq6 : (1 + r ^ 2 : ℤ) = r ^ 4 := by
        nlinarith [h11, h12]
      nlinarith
    exact_mod_cast eq5
  -- Now we need to show this polynomial is impossible for integer r.
  have h_eq' : r ^ 4 - r ^ 2 - 1 ≠ 0 := by
    by_cases h1 : r ^ 2 > 1
    · -- r^2 ≥ 2
      have h2 : r ^ 2 ≥ 2 := by nlinarith
      have h3 : r ^ 4 - r ^ 2 - 1 > 0 := by
        nlinarith [sq_nonneg (r ^ 2 - 2 : ℤ), sq_nonneg (r ^ 2 - (1 : ℤ)), sq_nonneg (r : ℤ), sq_nonneg (r ^ 2), sq_nonneg (r * r - 1)]
      intro h_eq_eq
      nlinarith
    · -- r^2 ≤ 1
      have h4 : r ^ 2 ≤ 1 := by nlinarith
      have h5 : r ≤ 1 := by nlinarith [sq_nonneg (r : ℤ), h4]
      have h6 : r ≥ -1 := by nlinarith [sq_nonneg (r : ℤ), h4]
      interval_cases r <;> omega
  -- Contradiction step
  have h_eq_zero : r ^ 4 - r ^ 2 - 1 = 0 := by 
    nlinarith [h_eq]
  exfalso 
  apply h_eq' 
  all_goals 
    linarith [h_eq_zero]