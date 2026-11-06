import Mathlib

/- 11th Irish 1998 Problem B2 Show that for positive reals a, b, c we have 9/(a+b+c) ≤ 2/(a+b) + 2/(b+c) + 2/(c+a) ≤ 1/a + 1/b + 1/c. -/
theorem inequalities_128586 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / (a + b + c) ≤ 2 / (a + b) + 2 / (b + c) + 2 / (c + a) ∧
    2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≤ 1 / a + 1 / b + 1 / c := by
  -- first prove a variation of am-gm for 2 variable that will be used later
  have h_ineq {a b :ℝ} (ha : 0 < a) (hb : 0 < b) : 2 ≤ a / b + b / a := by
    have : 2 * a * b ≤ a ^ 2 + b ^ 2 := by linarith [show 0 ≤ (a-b)^2 by positivity]
    have : 2 * a * b / (a * b) ≤ (a^2 + b^2) / (a * b) := by gcongr
    rw [show 2 = 2 * a * b / (a * b) by field_simp; ring]
    rw [show a / b + b / a = (a^2 + b^2) / (a * b) by field_simp; ring]
    exact this
  constructor
    -- first goal, replace A = b + c, B = c + a, C = a + b
  . set A := b + c with hA
    set B := c + a with hB
    set C := a + b with hC
    have : C + c = (A + B + C)/2 := by rw [hA, hB, hC]; ring
    rw [this]
    -- write 9 as 3 + 2 + 2 + 2 and apply the lemma on those 2
    calc
    9 / ((A + B + C)/2) = 2 * 9 / (A + B + C) := by field_simp; ring
    _ ≤ 2 * (3 + (A / B + B / A) + (B / C + C / B) + (A / C + C / A)) / (A + B + C) := by
      gcongr
      rw [show (9:ℝ) = 3 + 2 + 2 + 2 by norm_num]
      gcongr
      all_goals exact h_ineq (by positivity) (by positivity)
    _ = 2 / C + 2 / A + 2 / B := by field_simp; ring
    -- second goal, use the lemma to prove another lemma
  . replace h_ineq {a b : ℝ} (ha: 0 < a) (hb: 0 < b) : 4 / (a + b) ≤ 1/a + 1/b := by calc
      4 / (a + b) = (2 + 2) / (a + b) := by ring_nf
      _ ≤ (2 + (a / b + b / a)) / (a + b) := by
        gcongr
        exact h_ineq ha hb
      _ = 1/a + 1/b := by field_simp; ring
    -- just apply the lemma on a, b; b, c; c, a; add and divide by 2
    linear_combination ((h_ineq ha hb) + (h_ineq hb hc) + h_ineq hc ha)/2