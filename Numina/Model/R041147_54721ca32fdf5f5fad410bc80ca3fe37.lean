import Mathlib

theorem number_theory_74904 (a : Fin 2018 → ℝ) (ha : ∀ i, 0 < a i)
    (h : a 2017 ^ 2 + a 2016 ^ 2 = a 2015 ^ 2 - a 2014 ^ 2 + ∑ i ∈ Finset.range 2014, (-1 : ℝ) ^ (i + 1) * a i ^ 2) :
    ∃ x y, x ^ 2 - y ^ 2 = ∏ i ∈ Finset.range 2018, a i + 2025 := by
  use Real.sqrt ((∏ i ∈ Finset.range 2018, a i) + 2025), 0
  have h1 : 0 ≤ (∏ i ∈ Finset.range 2018, a i) + 2025 := by 
    have h2 : (∏ i ∈ Finset.range 2018, a i) > 0 := by 
      apply Finset.prod_pos 
      intro i hi
      exact ha i 
    linarith 
  have h2 : (Real.sqrt ((∏ i ∈ Finset.range 2018, a i) + 2025)) ^ 2 = (∏ i ∈ Finset.range 2018, a i) + 2025 := Real.sq_sqrt (show (0 : ℝ) ≤ (∏ i ∈ Finset.range 2018, a i) + 2025 by 
      have h2 : (∏ i ∈ Finset.range 2018, a i) > 0 := by 
        apply Finset.prod_pos 
        intro i hi
        exact ha i 
      linarith 
  )
  simp [h2]