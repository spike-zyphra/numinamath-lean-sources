import Mathlib

/-Let $a, b, c$ be lengths of triangle sides, $p=\frac{a}{b}+\frac{b}{c}+\frac{c}{a}$ and $q=\frac{a}{c}+\frac{c}{b}+\frac{b}{a}$.

Prove that $|p-q|<1$.-/
theorem inequalities_606017 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  |(a / b + b / c + c / a) - (a / c + c / b + b / a)| < 1 := by
-- Multiply both sides by $a* b* c$ and rewrite the LHS as $(b-c)* (c-a)* (a-b)$
  rw [← mul_lt_mul_left (show 0<a*b*c by positivity)]
  nth_rw 1 [show a*b*c = |a*b*c| by rw [abs_eq_self.mpr]; positivity, ← abs_mul]
  nth_rw 2 [add_comm]; field_simp; calc
  _ = |(b - c) * (c - a) * (a - b)| := by congr; field_simp; ring
  _ < _ := by
  -- Rule out the trivial cases when $a=b$ or $b=c$ or $c=a$
    rcases eq_or_ne a b with hab|_ <;> rcases eq_or_ne b c with hbc|_ <;> rcases eq_or_ne c a with hca|_
    any_goals simp [hab]; positivity
    any_goals simp [hbc]; positivity
    simp [hca]; positivity
  -- Use the inequalities of $a$, $b$ and $c$ to prove $|b-c|< a$, $|c-a|< b$ and $|a-b|< c$, this is enough to finish the goal
    rw [abs_mul, abs_mul]; apply mul_lt_mul; apply mul_lt_mul; any_goals positivity
    · rw [abs_lt]; constructor; all_goals linarith
    any_goals rw [abs_le]; constructor; all_goals linarith
    all_goals rw [abs_sub_pos]; assumption