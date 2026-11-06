import Mathlib


lemma lemma_1 (x : ℤ) (hx : x = -4) : 100 / abs x > x ^ 2 + 1 := by
  subst x
  have h1 : abs (-4 : ℤ) = 4 := by
    rfl
  rw [h1]
  norm_num


theorem inequalities_124611 :
    IsLeast {x : ℤ | 100 / |x| > x ^ 2 + 1} (-4) := by
  constructor
  · -- Show that -4 is in the set
    exact lemma_1 (-4) (by rfl)
  · -- Show that if x is in the set and x < -4 then contradiction
    intro x hx
    have h1 : (100 : ℤ) / |x| > x ^ 2 + 1 := by
      simpa using hx
    by_contra h
    push_neg at h
    have h2 : x ≤ -5 := by omega
    have h3 : (100 : ℤ) / (-x) ≤ 20 := by
      have h4 : x ≤ -5 := h2
      have h10 : x ≤ -5 := h4
      have h20 : -x ≥ 5 := by omega
      -- For x ≤ -5, since |x|= -x, so 100 / (-x) ≤ 20
      have h40 : (100 : ℤ) / (-x) ≤ 20 := by
        have h7 : (-x) ≥ 5 := by omega
        -- Show by the fact that 100 / (-x) ≤ 100 / 5 = 20
        have h13 : (100 : ℤ) ≤ (20 * (-x) : ℤ) := by
          omega
        have h100 : (100 : ℤ) / (-x) ≤ 20 := by
          apply Int.ediv_le_of_le_mul
          all_goals omega
        linarith
      linarith
    have h30 : |x| = -x := by
      rw [abs_of_neg (show x < 0 by omega)]
      <;> omega
    rw [h30] at h1
    have h400 : x ^ 2 + 1 ≥ 26 := by
      nlinarith [sq_nonneg (x + 5), sq_nonneg (x - 5)]
    have h50 : (100 : ℤ) / (-x) ≤ x ^ 2 + 1 := by
      nlinarith
    linarith