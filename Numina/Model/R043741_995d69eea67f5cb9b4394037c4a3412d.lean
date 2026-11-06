import Mathlib

theorem number_theory_136330 :
    ¬∃ k l m n : ℤ, k * l * m * n - k = 1966 ∧ k * l * m * n - l = 966 ∧ k * l * m * n - m = 66 ∧ k * l * m * n - n = 6 := by
  rintro ⟨k, l, m, n, h1, h2, h3, h4⟩
  have eq1 : l = k + 1000 := by 
    have h5 : k * l * m * n = 1966 + k := by
      linarith
    have h6 : k * l * m * n = 966 + l := by
      linarith
    have h7 : 1966 + k = 966 + l := by 
      linarith [h5, h6] 
    linarith
  have eq2 : m = l + 900 := by
    have h8 : k * l * m * n = 966 + l := by
      linarith
    have h9 : k * l * m * n = 66 + m := by
      linarith 
    have h10 : 966 + l = 66 + m := by
      linarith [h8, h9]
    linarith 
  have eq3 : m = k + 1900 := by
    linarith [eq1, eq2] 
  have eq4 : n = m + 60 := by
    have h11 : k * l * m * n = 66 + m := by
      linarith 
    have h12 : k * l * m * n = 6 + n := by
      linarith 
    have h13 : 66 + m = 6 + n := by
      linarith [h11, h12]
    linarith 
  have eq5 : n = k + 1960 := by 
    linarith [eq3, eq4] 
  have eq6 : k * (k + 1000) * (k + 1900) * (k + 1960) = k + 1966 := by
    have eq7 : k * l * m * n = k + 1966 := by 
      linarith 
    rw [show l = k + 1000 by linarith [eq1]] at eq7
    rw [show m = k + 1900 by linarith [eq3]] at eq7
    rw [show n = k + 1960 by linarith [eq5]] at eq7 
    linarith 
  have eq7 : k ≤ 2 := by 
    have eq7' : k * (k + 1000) * (k + 1900) * (k + 1960) = k + 1966 := eq6 
    nlinarith [sq_nonneg (k + 1), sq_nonneg (k - 1), sq_nonneg (k + 1000), sq_nonneg (k + 1900), sq_nonneg (k + 1960), sq_nonneg ((k + 1000) * (k + 1900)), sq_nonneg ((k + 1000) * (k + 1960)), sq_nonneg ((k + 1900) * (k + 1960)), sq_nonneg (k * (k + 1000)), sq_nonneg (k * (k + 1900)), sq_nonneg (k * (k + 1960))]
  have eq8 : k ≥ -1966 := by 
    have eq6' : k * (k + 1000) * (k + 1900) * (k + 1960) = k + 1966 := eq6 
    nlinarith [sq_nonneg (k + 1), sq_nonneg (k - 1), sq_nonneg (k + 1000), sq_nonneg (k + 1900), sq_nonneg (k + 1960), sq_nonneg ((k + 1000) * (k + 1900)), sq_nonneg ((k + 1000) * (k + 1960)), sq_nonneg ((k + 1900) * (k + 1960)), sq_nonneg (k * (k + 1000)), sq_nonneg (k * (k + 1900)), sq_nonneg (k * (k + 1960))]
  interval_cases k <;> omega