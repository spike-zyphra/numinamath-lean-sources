import Mathlib

theorem algebra_244760 {x y : ℕ} (hx : x > 0) (hy : y > 0) (hxy : x - y = 202)
    (h : (x * y - 1000) / x = 288 ∧ (x * y - 1000) % x = 67) :
    x * y = 97299 := by
  have h_eq1 : (x * y - 1000) = x * 288 + 67 := by
    have h_eq1 := (Nat.div_add_mod (x * y - 1000) x).symm
    have h_eq2 : (x * y - 1000) / x = 288 := h.1
    have h_eq3 : (x * y - 1000) % x = 67 := h.2
    simp [h_eq2, h_eq3] at h_eq1 ⊢ 
    all_goals omega
  have eq1 : x * y = 288 * x + 1067 := by 
    omega
  have h_eq4 : y = x - 202 := by 
    omega
  have eq2 : x * (x - 202) = 288 * x + 1067 := by 
    rw [show y = x - 202 by omega] at eq1 
    omega 
  have h1 : x ≤ 503 := by 
    by_contra h2
    push_neg at h2
    have h2 : x ≥ 504 := by 
      omega 
    have h3 : x * (x - 202) > 288 * x + 1067 := by 
      have h4 : x - 202 ≥ 302 := by 
        omega 
      nlinarith [h2, sq_nonneg (x : ℤ), sq_nonneg ((x - 202 : ℤ))]
    nlinarith 
  have h2 : x ≥ 203 := by 
    have : x ≥ y + 202 := by 
      omega 
    have h3 : y ≥ 1 := by 
      omega 
    have : x ≥ 1 + 202 := by 
      omega 
    omega 
  interval_cases x <;> norm_num [h_eq4] at eq1 h_eq1 h_eq4 eq2 ⊢ <;> omega