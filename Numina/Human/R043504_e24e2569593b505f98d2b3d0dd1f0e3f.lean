import Mathlib

/- 130. Prove that if the product of three positive numbers is 1, and the sum of these numbers is strictly greater than the sum of their reciprocals, then exactly one of these numbers is greater than 1. -/
theorem inequalities_276884 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * b * c = 1) (hrec : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by
  -- let's first assume wlog that a ≥ (b, c)
  wlog hab: a≥ b;
  · simp at hab
    specialize this b a c hb ha hc (by linarith) (by linarith) (by linarith)
    aesop
  wlog hac: a≥ c;
  · simp at hac
    specialize this c b a hc hb ha (by linarith) (by linarith) (by linarith) (by linarith)
    aesop
  left
  -- get rid of denominators at hrec and factor
  have :0 < a + b + c - 1/a - 1/b - 1/c := by linarith
  have hrec': 0 < (a*b*c)*(a + b + c - 1/a - 1/b - 1/c) := by apply mul_pos; aesop; assumption
  conv_rhs at hrec' =>
    calc (a*b*c)*(a + b + c - 1/a - 1/b - 1/c)
    _ = a^2*b*c + a*b^2*c + a*b*c^2 - ((a/a)*b*c) - (a*(b/b)*c) - (a*b*(c/c)) := by ring_nf
    _ = a*(a*b*c) + b*(a*b*c) + c*(a*b*c) - b*c - a*c - a*b := by rw [div_self (by linarith), div_self (by linarith), div_self (by linarith)]; ring_nf
    _ = a + b + c - b*c - a*c - a*b := by rw [hsum]; simp
    _ = a*b*c - b*c - a*c - a*b + a + b + c -1 := by rw [hsum]; ring_nf
    _ = (a-1)*(b-1)*(c-1) := by ring_nf
  -- the conclusion is clear but some work remains
  constructor
  · by_contra h; simp at h
    cases' lt_or_eq_of_le h with lt eq
    · have hb': b < 1 := by linarith
      have hc': c < 1 := by linarith
      have := mul_lt_mul lt (d:=1) (c:=b) (by linarith) (by linarith) (by norm_num)
      have := mul_lt_mul this (d:=1) (c:=c) (by linarith) (by linarith) (by norm_num)
      linarith
    · rw [eq] at hrec'; simp at hrec'
  constructor
  · by_contra h; simp at h
    have ha': 1 < a := by linarith
    have hh: 0 < (a - 1) * (b - 1) := by exact mul_pos (by linarith) (by linarith)
    nlinarith
  · by_contra h; simp at h
    have ha': 1 < a := by linarith
    have hh: 0 < (a - 1) * (c - 1) := by exact mul_pos (by linarith) (by linarith)
    nlinarith