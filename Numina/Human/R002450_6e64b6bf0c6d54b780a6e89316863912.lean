import Mathlib

/- Let a, b, and c be positive integers with a ≥ b ≥ c such that
a^2−b^2−c^2+ab=2011 and
a^2+3b^2+3c^2-3ab-2ac-2bc=-1997
.What is a?
(A) 249
(B) 250
(C) 251
(D) 252
(E) 253
 -/
theorem algebra_93609 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : a ≥ b ∧ b ≥ c) (h2 : a^2 - b^2 - c^2 + a * b = 2011) (h3 : a^2 + 3 * b^2 + 3 * c^2 - 3 * a * b - 2 * a * c - 2 * b * c = -1997) : a = 253 := by
  -- define some simple facts for a-c and a-b that'll be useful later
  have hac : 0 ≤ a-c := by linarith
  have hab : 0 ≤ a-b := by linarith
  have hab' : a-b ≤ a-c := by linarith
  -- add two equations and express in terms of a-b and a-c
  have h4 : (a-b)^2 + ((a-c) - (a-b))^2 + (a-c)^2 = 14 := by linarith
  -- last equation implies a-c ≤ 3
  have h_ub: a-c ≤ 3 := by
    have : (a-c)^2 ≤ 14 := by linarith [sq_nonneg (a-b), sq_nonneg (b-c)]
    suffices (a-c)^2 < 4^2 by
      suffices |a-c| < |4| by
        simp [abs] at this
        linarith
      exact sq_lt_sq.mp this
    linarith
  -- express original equation in terms of a, a-b, a-c
  have h2' : a^2 - (a - (a-b))^2 - (a - (a-c))^2 + a * (a - (a-b)) = 2011 := by linarith
  -- now try out all possible values for a-c and a-b, for each case do algebraic manipulaton to get contradictions in most cases and in one get a = 253
  interval_cases hac': (a-c)
  all_goals interval_cases hab'': (a-b)
  any_goals linarith
  all_goals ring_nf at h2'
  omega