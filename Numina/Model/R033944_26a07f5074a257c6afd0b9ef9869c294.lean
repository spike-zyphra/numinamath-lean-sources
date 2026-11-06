import Mathlib

theorem number_theory_604212
    (a b c d p q : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (hp : 0 < p)
    (hq : 0 < q)
    (h1 : a * d - b * c = 1)
    (h2 : (a : ℝ) / b > (p : ℝ) / q)
    (h3 : (p : ℝ) / q > (c : ℝ) / d) :
    q ≥ b + d ∧ (q = b + d → p = a + c) := by
  have h4 : a * q > p * b := by
    have h2' : (a : ℝ) / b > (p : ℝ) / q := h2
    have h5 : (a : ℝ) * (q : ℝ) > (p : ℝ) * (b : ℝ) := by
      have h6 : 0 < (b : ℝ) := by exact_mod_cast hb
      have h7 : 0 < (q : ℝ) := by exact_mod_cast hq
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h2'
      linarith
    have h8 : a * q > p * b := by
      exact_mod_cast h5
    linarith
  have h5 : p * d > c * q := by
    have h3' : (p : ℝ) / q > (c : ℝ) / d := h3
    have h6 : (p : ℝ) * (d : ℝ) > (c : ℝ) * (q : ℝ) := by
      have h7 : 0 < (q : ℝ) := by exact_mod_cast hq
      have h8 : 0 < (d : ℝ) := by exact_mod_cast hd
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h3'
      linarith
    have h7 : p * d > c * q := by
      exact_mod_cast h6
    linarith
  have h6 : a * q - p * b ≥ 1 := by
    omega
  have h7 : p * d - c * q ≥ 1 := by
    omega
  have h8 : q ≥ b + d := by
    nlinarith [h1, h6, h7, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos ha hq, mul_pos hb hc, mul_pos hb hd, mul_pos hb hq, mul_pos hc hd, mul_pos hc hq, mul_pos hd hq]
  constructor
  · exact h8
  · -- Show that if $q = b + d$, then $p = a + c$.
    intro h_eq
    have h10 : a * q - p * b = 1 := by
      nlinarith [h1, h6, h7, h_eq, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos ha hq, mul_pos hb hc, mul_pos hb hd, mul_pos hb hq, mul_pos hc hd, mul_pos hc hq, mul_pos hd hq]
    have h11 : p * d - c * q = 1 := by
      nlinarith [h1, h6, h7, h_eq, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos ha hq, mul_pos hb hc, mul_pos hb hd, mul_pos hb hq, mul_pos hc hd, mul_pos hc hq, mul_pos hd hq]
    have h12 : p = a + c := by
      nlinarith [h1, h10, h11, h_eq, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos ha hq, mul_pos hb hc, mul_pos hb hd, mul_pos hb hq, mul_pos hc hd, mul_pos hc hq, mul_pos hd hq]
    linarith [h12]