import Mathlib

theorem number_theory_95212 {A P a b: ℕ} (ha : a > 0) (hb : b > 0)
    (hA' : A = a * b) (hP' : P = 2 * (a + b)) :
    A + P ≠ 102 := by
  intro h
  rw [hA', hP'] at h
  have h_eq : a * b + 2 * (a + b) = 102 := by
    linarith
  have h_eq2 : (a + 2) * (b + 2) = 106 := by 
    nlinarith
  have h1 : (a + 2) * (b + 2) = 106 := h_eq2 
  have h2 : a ≤ 106 := by
    by_contra h3 
    push_neg at h3 
    have h4 : (a + 2) * (b + 2) ≥ (a + 2) * 2 := by 
      nlinarith [show b ≥ 1 from by linarith]
    nlinarith [h1, h4, h3, show b ≥ 1 from by linarith]
  have h3 : b ≤ 106 := by
    by_contra h4 
    push_neg at h4 
    nlinarith [h1, h4, show a ≥ 1 from by linarith]
  interval_cases a <;> 
    omega