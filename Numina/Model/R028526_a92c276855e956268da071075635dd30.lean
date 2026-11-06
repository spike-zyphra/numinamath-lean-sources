import Mathlib

theorem algebra_12183 {a b : ℂ} (ha : a^2 - 4*a + 5 = 0) (hb : b^2 - 4*b + 5 = 0)
    (hroots : a ≠ b) :
    a^3 + a^4*b^2 + a^2*b^4 + b^3 = 154 := by

  have eq1 : a^2 - 4*a + 5 - (b^2 - 4*b + 5) = 0 := by
    rw [ha, hb]
    ring_nf

  have eq5 : a^2 - b^2 - 4*a + 4*b = 0 := by
    ring_nf at eq1 ⊢
    exact_mod_cast eq1

  have eq5' : (a - b) * (a + b - 4) = 0 := by 
    ring_nf at eq5 ⊢
    exact_mod_cast eq5

  have h1 : a + b = 4 := by
    cases' (mul_eq_zero.mp eq5') with h1 h2
    · -- Assume `a - b = 0`, which implies `a = b`.
      exfalso
      apply hroots
      have : a = b := by
        have h2 : a - b = 0 := h1
        exact sub_eq_zero.mp h2
      exact this
    · -- `a + b - 4 = 0` 
      have eq7 : a + b = 4 := by
        have h3 : a + b - 4 = 0 := by
          simpa using h2
        have h4 : a + b = 4 := by
          calc
            a + b = (a + b - 4) + 4 := by ring_nf
            _ = 0 + 4 := by rw [h3]
            _ = 4 := by ring_nf
        exact_mod_cast h4
      exact_mod_cast eq7

  have eq8 : a * b = 5 := by
    have eq4 : a^2 + b^2 - 4*a - 4*b + 10 = 0 := by
      have eq1 : a^2 - 4*a + 5 = 0 := by 
        exact_mod_cast ha
      have eq2 : b^2 - 4*b + 5 = 0 := by 
        exact_mod_cast hb
      have eq5 : a^2 + b^2 -4*a -4*b +10 =0 := by
        calc
          a^2 + b^2 -4*a -4*b +10 = (a^2 -4*a +5) + (b^2 -4*b +5) := by ring_nf
          _ = 0 + 0 := by rw [eq1, eq2]
          _ = 0 := by ring_nf
      exact_mod_cast eq5

    have eq9 : (a + b) ^ 2 = 16 := by
      rw [show a + b = (4 : ℂ) by 
          exact_mod_cast h1
      ]
      norm_num

    have eq7' : a^2 + b^2 = 4*(a+b) - 10 := by 
      have h4 : a^2 + b^2 -4*a -4*b +10 =0 := eq4
      calc 
        a^2 + b^2 = (a^2 + b^2 -4*a -4*b +10) + 4*a + 4*b -10 := by ring_nf
        _ = 0 + 4*a + 4*b -10 := by rw [h4]
        _ = 4*(a+b) -10 := by ring_nf

    have eq14 : a^2 + b^2 = 6 := by 
      rw [show a + b = (4 : ℂ) by 
          exact_mod_cast h1
      ] at eq7'
      norm_num at eq7' ⊢
      exact_mod_cast eq7'

    have eq15 : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring_nf

    have eq11 : a^2 + 2*a*b + b^2 = 16 := by
      rw [eq15] at eq9
      exact_mod_cast eq9

    have eq13 : a * b = 5 := by 
      have eq18 : a^2 + b^2 = 6 := eq14
      have eq19 : a^2 + 2 * a * b + b^2 = 16 := by 
        exact_mod_cast eq11
      have eq3 : 2*(a * b) = 10 := by 
        calc 
          2*(a * b) = (a^2 + 2 * a * b + b^2) - (a^2 + b^2) := by ring_nf
          _ = 16 - (6) := by rw [eq19, eq18]
          _ = (10 : ℂ) := by norm_num
      have h : a * b = 5 := by
        calc 
          a * b = (2 * (a * b)) / 2 := by ring_nf
          _ = 10 / 2 := by rw [eq3]
          _ = 5 := by norm_num
      exact_mod_cast h
    exact_mod_cast eq13

  have eq9 : a^3 + a^4 * b^2 + a^2 * b^4 + b^3 = 154 := by
    have eq1 : a ^3 + b ^3 = 4 := by
      have eq2 : a + b = 4 := h1
      have eq3 : a * b = 5 := eq8
      have eq4 : a ^3 + b ^3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by 
        ring_nf
      rw [eq4, eq2, eq3]
      norm_num

    have eq5 : a^4 * b^2 + a^2 * b^4 = 150 := by
      have eq7 : a^4 * b^2 + a^2 * b^4 = (a * b)^2 * (a^2 + b^2) := by 
        ring_nf
      rw [eq7]
      have eq6 : a * b = 5 := eq8
      have eq8' : (a * b)^2 = 25 := by 
        rw [eq6]
        norm_num
      have eq9 : a^2 + b^2 = 6 := by
        have eq4 : a^2 + b^2 - 4*a - 4*b + 10 = 0 := by
          have eq1 : a^2 - 4*a + 5 = 0 := by 
            exact_mod_cast ha
          have eq2 : b^2 - 4*b + 5 = 0 := by 
            exact_mod_cast hb
          have eq5 : a^2 + b^2 -4*a -4*b +10 =0 := by
            calc
              a^2 + b^2 -4*a -4*b +10 = (a^2 -4*a +5) + (b^2 -4*b +5) := by ring_nf
              _ = 0 + 0 := by rw [eq1, eq2]
              _ = 0 := by ring_nf
          exact_mod_cast eq5
        have eq5 : a^2 + b^2 = 4*(a+b) -10 := by 
          have h4 : a^2 + b^2 -4*a -4*b +10 =0 := eq4
          calc 
            a^2 + b^2 = (a^2 + b^2 -4*a -4*b +10) + 4*a + 4*b -10 := by ring_nf
            _ = 0 + 4*a + 4*b -10 := by rw [h4]
            _ = 4*(a+b) -10 := by ring_nf
        rw [show a + b = (4 : ℂ) by 
            exact_mod_cast h1] at eq5
        norm_num at eq5 ⊢ 
        exact_mod_cast eq5
      rw [eq8', eq9]
      all_goals norm_num

    have eq6 : a^3 + a^4 * b^2 + a^2 * b^4 + b^3 = (a^3 + b^3) + (a^4 * b^2 + a^2 * b^4) := by ring_nf
    rw [eq6, eq1, eq5]
    all_goals norm_num
  exact_mod_cast eq9