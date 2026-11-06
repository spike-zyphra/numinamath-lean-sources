import Mathlib

theorem number_theory_2450 (M N : ℕ) (hM : M < 100) (hN : N < 100)
    (hMN : IsSquare M ∧ IsSquare N) (hMN1 : M - N = 27) :
    Real.sqrt M + Real.sqrt N = 9 := by
  rcases hMN with ⟨hM1, hN1⟩
  rcases hM1 with ⟨a, ha⟩
  rcases hN1 with ⟨b, hb⟩
  have h3 : M = N + 27 := by
    omega
  rw [ha] at h3
  rw [hb] at h3
  have h4 : a ≤ 10 := by
    nlinarith
  have h5 : b ≤ 10 := by
    nlinarith
  interval_cases a <;> try { 
    omega 
  } <;> interval_cases b 
  <;> norm_num at h3 ha hb ⊢ 
  <;> try { 
    have h9 : Real.sqrt (M : ℝ) = (6 : ℝ) := by
      rw [show (M : ℝ) = (36 : ℝ) by norm_num [ha]]
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    have h10 : Real.sqrt (N : ℝ) = (3 : ℝ) := by
      rw [show (N : ℝ) = (9 : ℝ) by norm_num [hb]]
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h9, h10]
    all_goals norm_num
  }
  <;> try { 
    exfalso 
    all_goals nlinarith 
  }