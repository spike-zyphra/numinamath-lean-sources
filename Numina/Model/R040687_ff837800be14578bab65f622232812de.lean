import Mathlib

theorem algebra_269070 {P : Polynomial ℤ} (hP : P.eval 19 = 1994) (hP' : P.eval 94 = 1994)
    (hP'' : |P.eval 0| < 1000) : P.eval 0 = 208 := by
  have h1 : (19 - 0 : ℤ) ∣ (P.eval 19 - P.eval 0) := by
    apply Polynomial.sub_dvd_eval_sub 
  have h2 : (94 - 0 : ℤ) ∣ (P.eval 94 - P.eval 0) := by 
    apply Polynomial.sub_dvd_eval_sub 
  rw [hP] at h1
  rw [hP'] at h2
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  have h3 : P.eval 0 = 1994 - 19 * k1 := by
    linarith [hk1]
  have h4 : 19 * k1 = 94 * k2 := by 
    nlinarith [hk1, hk2]
  have h5 : ∃ m : ℤ, k1 = 94 * m := by 
    have : 19 * k1 = 94 * k2 := by linarith 
    have h6 : 19 ∣ 94 * k2 := by 
      omega 
    have h7 : 19 ∣ k2 := by
      omega 
    rcases h7 with ⟨m, hm⟩
    use m
    nlinarith [hm]
  rcases h5 with ⟨m, hm⟩
  have h6 : k2 = 19 * m := by 
    nlinarith [hm, h4]
  have h7 : P.eval 0 = 1994 - 1786 * m := by
    rw [h3]
    rw [hm]
    all_goals
      ring
  have h8 : -1000 < P.eval 0 := by 
    linarith [abs_lt.mp hP'']
  have h9 : P.eval 0 < 1000 := by 
    linarith [abs_lt.mp hP'']
  rw [h7] at h8 h9 
  have h10 : m = 1 := by
    omega 
  rw [h10] at h7
  linarith