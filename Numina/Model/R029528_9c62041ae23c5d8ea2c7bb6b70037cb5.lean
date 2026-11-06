import Mathlib

theorem number_theory_300538 :
    ¬∃ a b c d : ℤ, (a * b * c * d - a = 1961) ∧ (a * b * c * d - b = 961) ∧
      (a * b * c * d - c = 61) ∧ (a * b * c * d - d = 1) := by
  rintro ⟨a, b, c, d, h1, h2, h3, h4⟩
  have eq1 : b = a + 1000 := by 
    have h5 : a * b * c * d - a - (a * b * c * d - b) = 1961 - 961 := by
      linarith
    have h6 : a * b * c * d - a - (a * b * c * d - b) = -a + b := by 
      linarith
    linarith
  have eq2 : c = b + 900 := by 
    have h6 : a * b * c * d - b - (a * b * c * d - c) = 961 - 61 := by 
      linarith
    have h7 : a * b * c * d - b - (a * b * c * d - c) = -b + c := by 
      linarith
    linarith
  have eq3 : d = c + 60 := by
    have h7 : a * b * c * d - c - (a * b * c * d - d) = 61 - 1 := by 
      linarith
    have h8 : a * b * c * d - c - (a * b * c * d - d) = -c + d := by 
      linarith
    linarith
  have eq4 : c = a + 1900 := by 
    linarith [eq1, eq2]
  have eq5 : d = a + 1960 := by 
    linarith [eq4, eq3, eq1]
  have eq7 : d * (a * b * c - 1) = 1 := by
    nlinarith
  have h7 : d ∣ 1 := by 
    use (a * b * c - 1)
    linarith
  have h8 : d = 1 ∨ d = -1 := by
    have h9 : d ∣ 1 := h7
    have h10 : d ≤ 1 := by 
      apply Int.le_of_dvd (by norm_num) h9
    have h11 : -1 ≤ d := by 
      have h12 : -d ∣ 1 := by 
        exact Int.neg_dvd.2 h9
      have h13 : -d ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h12
      omega
    interval_cases d <;> tauto
  cases h8 with
  | inl h9 =>
    -- Assume d = 1, derive contradiction.
    have h10 : a = -1959 := by
      omega
    have h11 : b = -959 := by
      rw [h10] at eq1
      omega
    have h12 : c = -59 := by 
      nlinarith [h10, eq4]
    have h13 : d = 1 := h9
    rw [h10, h11, h12, h13] at h1
    norm_num at h1
  | inr h9 =>
    -- Assume d = -1, derive contradiction.
    have h10 : a = -1961 := by
      omega
    have h11 : b = -961 := by
      rw [h10] at eq1
      omega
    have h12 : c = -61 := by 
      nlinarith [h10, eq4]
    have h13 : d = -1 := h9
    rw [h10, h11, h12, h13] at h1
    norm_num at h1