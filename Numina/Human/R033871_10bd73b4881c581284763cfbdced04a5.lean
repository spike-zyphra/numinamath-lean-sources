import Mathlib

/- Andy's lawn has twice as much area as Beth's lawn and three times as much area as Carlos' lawn. Carlos' lawn mower cuts half as fast as Beth's mower and one third as fast as Andy's mower. If they all start to mow their lawns at the same time, who will finish first?
(A) Andy
(B) Beth
(C) Carlos
(D) Andy and  Carlos tie for first.
(E) All three tie.
 -/
theorem algebra_94395 {a b c sa sb sc : ℝ} (ha: a > 0) (hb: b > 0) (hc: c > 0)
(hsa: sa > 0) (hsb: sb > 0) (hsc: sc > 0)
(hab : a = 2 * b) (hac : a = 3 * c) (hbc' : sc / sb = 1 / 2) (hac' : sc / sa = 1 / 3) :
b / sb < a / sa ∧ b / sb < c / sc := by
  -- a, b, c are lawn areas and sa, sb, sc are mower speeds of andy, beth, carlos. first express all areas in terms of a and express all speeds in terms of sa
  have hb' : b = a / 2 := by linarith
  have hc' : c = a / 3 := by linarith
  have hsc' : sc = sa / 3 := by
    field_simp at hac'
    linarith
  have hsb' : sb = 2 * sa / 3 := by
    field_simp at hbc'
    linarith
  -- now replace all sb, sc, b, c in goal to get new goal: a / 2 / (2 * sa / 3) < a / sa ∧ a / 2 / (2 * sa / 3) < a / 3 / (sa / 3)
  rw [hb', hc', hsc', hsb']
  -- we'll prove both goals, now the way to prove is same so we can repeat the logic, first change goal to that with sa multiplied (so that it cancels out from denominator), then normalize and calculate
  constructor
  repeat
  . apply (mul_lt_mul_iff_of_pos_right hsa).mp
    ring_nf
    field_simp
    linarith