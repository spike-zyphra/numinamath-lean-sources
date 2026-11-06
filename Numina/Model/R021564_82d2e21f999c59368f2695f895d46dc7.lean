import Mathlib

theorem number_theory_323599 {p q : ℕ} (hq : q ≠ 0) (h : p / q = ∑ i ∈ Finset.range 1319, (-1 : ℤ) ^ (i + 1) / (i + 2)) :
    1979 ∣ p := by
  norm_num [Finset.sum_range_succ] at h

  have h1 : (p : ℤ) / (q : ℤ) = -660 := by
    simpa using h
  
  have h2 : (p : ℤ) ≥ 0 := by
    exact_mod_cast show (0 : ℕ) ≤ p by omega

  have h3 : (q : ℤ) ≥ 1 := by 
    have hq' : q ≥ 1 := by 
      by_contra h
      push_neg at h
      have : q = 0 := by linarith
      tauto
    exact_mod_cast hq'

  have h4 : (p : ℤ) / (q : ℤ) ≥ 0 := by 
    apply Int.ediv_nonneg
    omega
    omega
  
  linarith