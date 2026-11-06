import Mathlib

theorem algebra_94395 {a b c sa sb sc : ℝ} (ha: a > 0) (hb: b > 0) (hc: c > 0)
(hsa: sa > 0) (hsb: sb > 0) (hsc: sc > 0)
(hab : a = 2 * b) (hac : a = 3 * c) (hbc' : sc / sb = 1 / 2) (hac' : sc / sa = 1 / 3) :
b / sb < a / sa ∧ b / sb < c / sc := by
  -- From hbc', we get that `sc = (1/2) * sb`.
  have h1 : sc = sb / 2 := by
    have h2 : sb ≠ 0 := by linarith
    field_simp [h2] at hbc'
    linarith
  -- From hac', we get that `sc = (1/3) * sa`. Therefore, combining these equations,
  have h2 : sc = sa / 3 := by
    have h2 : sa ≠ 0 := by linarith
    field_simp [h2] at hac'
    linarith
  -- Now since `sc = (1/3) * sa` and `sc = (1/2) * sb`, we have `sa = (3/2) * sb`.
  have h3 : 2 * sa = 3 * sb := by
    have eq1 : sc = sa / 3 := h2
    have eq2 : sc = sb / 2 := h1
    linarith
  -- Now we need to prove `b/sb < a/sa` and `b/sb < c/sc`.
  -- First part: `b / sb < a / sa`.
  have h4 : b / sb < a / sa := by
    have ha1 : a = 2 * b := hab
    rw [show a = 2 * b by linarith]
    have h5 : b > 0 := hb
    have h6 : sa > 0 := hsa
    have h7 : sb > 0 := hsb
    have h8 : b * sa < 2 * b * sb := by
      nlinarith [h3]
    have h9 : b / sb < (2 * b) / sa := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h9
  -- Second part: `b / sb < c / sc`.
  have h6 : b / sb < c / sc := by
    have ha1 : a = 2 * b := hab
    have h2b : c = a / 3 := by
      linarith [hac]
    rw [show c = a / 3 by linarith]
    rw [show a = 2 * b by linarith]
    have h10 : b > 0 := hb
    have h11 : sc > 0 := hsc
    have h12 : sb > 0 := hsb
    have h13 : b / sb < (2 * b / 3) / sc := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      have h14 : b * sc < (2 * b / 3) * sb := by
        have eq1 : sc = sb / 2 := h1
        rw [show sc = sb / 2 by linarith [h1]]
        nlinarith
      nlinarith
    exact h13
  -- So, both parts are proven.
  constructor
  · exact h4
  · exact h6