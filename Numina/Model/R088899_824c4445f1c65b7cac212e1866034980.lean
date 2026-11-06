import Mathlib

theorem number_theory_67899 {P : Polynomial ℤ} (hP : P.eval 1997 = 0 ∧ P.eval 2010 = 0)
    (hP' : |P.eval 2005| < 10) : P.eval 2005 = 0 := by
  rcases hP with ⟨h1, h2⟩
  have h3 : (2005 - 1997 : ℤ) ∣ P.eval 2005 := by
    have h4 : (2005 - 1997 : ℤ) ∣ P.eval 2005 - P.eval 1997 := by
      apply Polynomial.sub_dvd_eval_sub
    have h5 : P.eval 1997 = 0 := h1
    have h6 : P.eval 2005 - P.eval 1997 = P.eval 2005 := by
      rw [h5]
      all_goals ring
    rw [h6] at h4
    exact h4
  have h8 : (2005 - 2010 : ℤ) ∣ P.eval 2005 := by
    have h9 : (2005 - 2010 : ℤ) ∣ P.eval 2005 - P.eval 2010 := by
      apply Polynomial.sub_dvd_eval_sub
    have h10 : P.eval 2010 = 0 := h2
    have h11 : P.eval 2005 - P.eval 2010 = P.eval 2005 := by
      rw [h10]
      all_goals ring
    rw [h11] at h9
    exact h9
  have h8' : (2005 - 1997 : ℤ) = 8 := by norm_num
  have h8'' : (2005 - 2010 : ℤ) = -5 := by norm_num
  rw [h8'] at h3
  rw [h8''] at h8
  have h12 : 8 ∣ P.eval 2005 := by 
    exact h3
  have h13 : 5 ∣ P.eval 2005 := by
    have h14 : (-5 : ℤ) ∣ P.eval 2005 := h8
    exact Int.neg_dvd.1 h14
  have h15 : 40 ∣ P.eval 2005 := by 
    omega
  have h16 : P.eval 2005 ≥ -9 := by 
    rw [abs_lt] at hP'
    omega
  have h17 : P.eval 2005 ≤ 9 := by 
    rw [abs_lt] at hP'
    omega
  have h20 : P.eval 2005 = 0 := by 
    omega
  exact h20