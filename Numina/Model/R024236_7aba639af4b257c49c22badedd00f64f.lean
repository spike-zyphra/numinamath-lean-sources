import Mathlib

theorem algebra_321964 {a b c m : ℝ}
    (hroots : {x | x^2 - 4 * x + m = 0} = {a, b})
    (hroots' : {x | x^2 - 8 * x + 5 * m = 0} = {b, c}) :
    m = 0 ∨ m = 3 := by
  have h1 : a^2 - 4 * a + m = 0 := by
    have ha : a ∈ {x | x^2 - 4 * x + m = 0} := by
      rw [hroots]
      simp
    simpa using ha
  have h2 : b^2 - 4 * b + m = 0 := by
    have hb : b ∈ {x | x^2 - 4 * x + m = 0} := by
      rw [hroots]
      simp
    simpa using hb
  have h3 : b^2 - 8 * b + 5 * m = 0 := by 
    have hb : b ∈ {x | x^2 - 8 * x + 5 * m = 0} := by
      rw [hroots']
      simp
    simpa using hb
  have h4 : c^2 - 8 * c + 5 * m = 0 := by
    have hc : c ∈ {x | x^2 - 8 * x + 5 * m = 0} := by
      rw [hroots']
      simp
    simpa using hc
  have eq1 : (a - b) * (a + b - 4) = 0 := by
    nlinarith [h1, h2]
  cases' (mul_eq_zero.mp eq1) with h_eq1 h_eq2
  · -- Case 1: a = b
    have hb_eq : b = a := by 
      linarith 
    rw [hb_eq] at h3 
    have h5 : a * (a - 3) = 0 := by 
      nlinarith [h1, h3] 
    cases' (mul_eq_zero.mp h5) with h6 h7 
    · -- Case 1a: a = 0
      have ha0 : a = 0 := by
        linarith 
      have hm0 : m = 0 := by
        nlinarith [h1, ha0] 
      left 
      linarith [hm0] 
    · -- Case 1b: a = 3
      have ha3 : a = 3 := by
        linarith 
      have hm3 : m = 3 := by
        nlinarith [h1, ha3] 
      right 
      linarith [hm3] 
  · -- Case 2: a + b = 4
    have hb_eq : b = 4 - a := by
      linarith 
    rw [hb_eq] at h3 
    have h5 : (a - 1) * (a - 4) = 0 := by 
      nlinarith [h1, h3] 
    cases' (mul_eq_zero.mp h5) with h8 h9 
    · -- Case 2a: a = 1
      have ha1 : a = 1 := by
        linarith 
      have hm3 : m = 3 := by 
        nlinarith [h1, ha1] 
      right 
      linarith [hm3] 
    · -- 2b: a = 4
      have ha4 : a = 4 := by 
        linarith 
      have hm0 : m = 0 := by 
        nlinarith [h1, ha4] 
      left 
      linarith [hm0]