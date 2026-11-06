import Mathlib

theorem algebra_20361 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hseq : ∃ d, b = a + d ∧ c = b + d ∧ d = c + d)
    (hge : ∃ r, b = a * r ∧ d = b * r) :
    a / d = 1 / 4 := by

  rcases hseq with ⟨d', h1, h2, h3⟩
  rcases hge with ⟨r, h4, h5⟩

  have eq1 : b = a + d' := by linarith 
  have eq2 : c = a + 2 * d' := by
    linarith [h1, h2]
  have eq3 : d = a + 3 * d' := by
    have h4' : d = c + d' := by linarith [h3]
    rw [h4']
    have h5' : c = a + 2 * d' := by
      linarith [h1, h2]
    linarith [h5']
  
  have eq4 : b = a * r := by linarith 
  have eq5 : d = b * r := by linarith 
  have eq6 : d = a * r ^ 2 := by
    rw [eq5]
    rw [eq4]
    all_goals ring
  
  have eq7 : a + d' = a * r := by
    linarith [eq1, eq4]

  have eq8 : a + 3 * d' = a * r ^ 2 := by
    linarith [eq3, eq6]

  have eq9 : d' = a * (r - 1) := by
    linarith [eq7]

  rw [eq9] at eq8
  
  have eq11 : 1 + 3 * (r - 1) = r ^ 2 := by
    have ha' : 0 < a := ha
    apply (mul_left_inj' (ne_of_gt ha)).mp
    linarith

  have eq12 : r ^ 2 - 3 * r + 2 = 0 := by
    linarith [eq11]

  have eq13 : (r - 1) * (r - 2) = 0 := by
    linarith [eq12]

  cases' (mul_eq_zero.mp eq13) with eq14 eq15

  · -- When $r - 1 = 0$, $r = 1$, which implies $b = a$, $d = a$, contradiction
    have h10 : r = 1 := by linarith
    have h11 : b = a := by
      rw [h4]
      rw [h10]
      all_goals nlinarith
    have h12 : d = a := by
      rw [h5]
      rw [h11]
      rw [h10]
      all_goals nlinarith
    have h13 : d' = 0 := by
      nlinarith [h11, eq1]
    have h14 : c = a := by
      linarith [h2, h11, h13]
    nlinarith [hb, ha, h11, h14, h12, h3]

  · -- When $r - 2 = 0$, $r = 2$
    have h10 : r = 2 := by linarith
    have h11 : d' = a := by
      rw [h10] at eq7
      linarith

    have h12 : b = 2 * a := by
      nlinarith [h10, h4, h11]

    have h14 : d = 4 * a := by
      linarith [h11, h12, h3, (show c = 3 * a by linarith [h12, h11, h2])]

    have h15 : a / d = 1 / 4 := by 
      have h16 : d = 4 * a := by linarith
      rw [show d = 4 * a by linarith]
      have h19 : 4 * a ≠ 0 := by
        nlinarith [show 0 < a by linarith]
      field_simp [h19]
      <;> nlinarith 
    exact h15