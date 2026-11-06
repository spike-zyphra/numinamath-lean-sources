import Mathlib

/- Let a+ar_1+ar_1^2+ar_1^3+⋯ and a+ar_2+ar_2^2+ar_2^3+⋯ be two different infinite geometric series
 of positive numbers with the same first term.  The sum of the first series is r_1​ ,and the sum of the
 second series is r_2​.  What is r_1+r_2​ ?
 (A) 0
 (B) 1/2
 (C) 1
 (D) (1+sqrt(5))/2
 (E) 2
 -/
theorem algebra_93424 {a r1 r2 : ℝ} (ha : 0 < a) (hr1 : 0 < r1) (hr1' : r1 < 1) (hr2 : 0 < r2) (hr2' : r2 < 1)
(hd : r1 ≠ r2) (h1 : a / (1 - r1) = r1) (h2 : a / (1 - r2) = r2) : r1 + r2 = 1 := by {
  -- since h1 and h2 are similar, we'll prove a = r * (1-r) in a common statement
  have ha {r: ℝ} (hr: r < 1) (hs: a / (1 - r) = r) : a = r * (1-r) := by
    calc
      a = a / (1-r) * (1-r) := by
        apply Eq.symm
        apply div_mul_cancel_of_imp
        intro hz
        have : False := by linarith
        contradiction
      _ = r * (1-r) := by rw [hs]
  -- derive r1 * (1-r1) = r2 * (1-r2)
  have ha1 := ha hr1' h1
  have ha2 := ha hr2' h2
  rw [ha1] at ha2
  -- manipulate r1 * (1-r1) = r2 * (1-r2) to figure out (r1 - r2) * (r1 + r2 - 1) = 0
  have : (r1 - r2) * (r1 + r2 - 1) = 0 := by linarith
  -- two cases, first case, r1 - r2 = 0 can't be possible as r1 ≠ r1,
  -- second case is r1 + r2 - 1 = 0, that proves r1 + r2 = 1
  have htwo : r1 - r2 = 0 ∨ r1 + r2 - 1 = 0 := by
    apply mul_eq_zero.1
    assumption
  have hsum: r1 + r2 - 1 = 0 := by
    cases htwo with
    | inl hsame =>
      have : r1 = r2 := by linarith
      contradiction
    | inr hsum => assumption
  linarith
}