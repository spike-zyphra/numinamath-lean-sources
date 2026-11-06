import Mathlib

theorem algebra_94808 (m : ℕ) (hm : m > 0) (x y : ℤ) (h : 13 * x + 11 * y = 700) (h' : y = m * x - 1) :
    m = 6 := by
  rw [h'] at h
  have h1 : (13 : ℤ) * x + 11 * (m * x - 1) = 700 := h
  have h2 : x * (13 + 11 * (m : ℤ)) = 711 := by
    nlinarith
  have h3 : x ∣ 711 := by
    use 13 + 11 * (m : ℤ)
    linarith [h2]
  have h4 : x ≥ 1 := by
    by_contra h4
    push_neg at h4
    have h5 : x ≤ 0 := by
      omega
    have h1' : (13 + 11 * (m : ℤ)) ≥ 1 := by
      have hm' : (m : ℤ) > 0 := by exact_mod_cast hm
      omega
    nlinarith
  have h5 : x ≤ 711 := by
    apply Int.le_of_dvd (by norm_num) h3
  have h6 : (m : ℤ) = 6 := by
    interval_cases x <;> try { 
      omega
    }
    <;> try { 
      have h_m : (m : ℤ) = 6 := by 
        omega
      exact_mod_cast h_m
    }
  exact_mod_cast h6