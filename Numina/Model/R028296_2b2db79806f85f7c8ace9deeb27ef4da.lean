import Mathlib

theorem algebra_310675 (a : ℕ → ℝ) (h : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (ha : ∀ n, 0 < a n) (h1 : 2 * a 4 + a 3 - 2 * a 2 - a 1 = 8) :
    2 * a 8 + a 7 ≥ 54 := by
  rcases h with ⟨r, hr⟩

  have ha1 : 0 < a 0 := by
    have h3 := ha 0
    simpa using h3

  have ha2 : 0 < r := by
    have h11 :=  ha 1
    have h00 :=  ha 0
    have h11' : 0 < a 1 := by 
      simpa using  h11
    have h12 : a 1 = a 0 * r ^ 1 := by
      specialize hr 1
      simpa using  hr
    rw [h12] at h11'
    have h13 : 0 < a 0 := by 
      simpa using  ha 0
    nlinarith

  have eq1 : 2 * a 4 + a 3 - 2 * a 2 - a 1 = 8 := h1

  have eq1a : a 1 = a 0 * r ^ 1 := by
    specialize  hr 1
    simpa using  hr

  have eq1b : a 2 = a 0 * r ^ 2 := by
    specialize  hr 2
    simpa using  hr

  have eq1c : a 3 = a 0 * r ^ 3 := by
    specialize  hr 3
    simpa using  hr

  have eq1d : a 4 = a 0 * r ^ 4 := by
    specialize  hr 4
    simpa using  hr

  rw [eq1a, eq1b, eq1c, eq1d] at eq1

  have eq3 : 2 * a 8 + a 7 = a 0 * r ^ 7 * (2 * r + 1) := by 
    have eq7 : a 7 = a 0 * r ^ 7 := by 
      specialize hr 7 
      simpa using  hr
    have eq8 : a 8 = a 0 * r ^ 8 := by 
      specialize hr 8 
      simpa using  hr
    nlinarith [eq7, eq8]

  have eq4 : a 0 * r * (r ^ 2 - 1) * (2 * r + 1) = 8 := by
    nlinarith

  have h2 : r ^ 2 > 1 := by
    have h3 : (r ^ 2 - 1) * (2 * r + 1) > 0 := by 
      have h4 : a 0 * r * (r ^ 2 - 1) * (2 * r + 1) = 8 := eq4
      have h5 : (r ^ 2 - 1) * (2 * r + 1) > 0 := by 
        have h6 : a 0 * r > 0 := by 
          apply mul_pos 
          all_goals linarith
        nlinarith 
      linarith 
    have h6 : 0 < (r ^ 2 - 1) := by 
      have h7 : 0 < 2 * r + 1 := by nlinarith
      nlinarith 
    nlinarith

  have eq7 : (a 0 * r ^ 7 * (2 * r + 1)) ≥ 54 := by
    have h3 : (r ^ 2 - 1) * (2 * r + 1) > 0 := by 
      have h4 : a 0 * r * (r ^ 2 - 1) * (2 * r + 1) = 8 := eq4
      have h5 : (r ^ 2 - 1) * (2 * r + 1) > 0 := by 
        have h6 : a 0 * r > 0 := by 
          apply mul_pos 
          all_goals linarith 
        nlinarith 
      linarith
    have h11 : 0 < r ^ 2 - 1 := by
      nlinarith 
    nlinarith [sq_nonneg (r ^ 2 - 3 / 2), sq_nonneg (r ^ 2 - 3 / 2), sq_nonneg (r ^ 2 - 3 / 2), 
      sq_nonneg (r ^ 2 - 3 / 2), sq_nonneg ( (r ^ 2 - 1) * (r ^ 2 - 3 / 2) ), sq_nonneg ( (r ^ 2 - 1) ), sq_nonneg ( (r ^ 2 - 3 / 2) * (r ^ 2) ), sq_nonneg ( (r ^ 2 - 3 / 2) * (r ^ 2 - 1) ), mul_pos ha1 (show 0 < r by nlinarith), 
      mul_pos (show 0 < r by nlinarith) (show 0 < r ^ 2 by nlinarith), 
      mul_pos (show 0 < r ^ 2 - 1 by nlinarith) (show 0 < r by nlinarith), 
      mul_pos (show 0 < r ^ 2 - 1 by nlinarith) (show 0 < 2 * r + 1 by nlinarith)
    ]
  linarith