import Mathlib

theorem number_theory_598896 (a b c d e f : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f)
    (h₁ : (a / b : ℚ) > (c / d : ℚ)) (h₂ : (c / d : ℚ) > (e / f : ℚ)) (h₃ : a * f - b * e = 1) :
    d ≥ b + f := by
  rcases h₀ with ⟨ha, hb, hc, hd, he, hf⟩
  have h4 : (a : ℚ) / b > (c : ℚ) / d := by linarith
  have h5 : a * (d : ℚ) > b * (c : ℚ) := by
    have h6 : (a : ℚ) / b > (c : ℚ) / d := h4
    have h7 : (a : ℚ) * (d : ℚ) > (b : ℚ) * (c : ℚ) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h6
      linarith
    linarith
  have h8 : a * d > b * c := by
    exact_mod_cast h5
  have h6 : (c : ℚ) / d > (e : ℚ) / f := by linarith
  have h7 : c * (f : ℚ) > d * (e : ℚ) := by
    have h8 : (c : ℚ) / d > (e : ℚ) / f := h6
    have h9 : (c : ℚ) * (f : ℚ) > (d : ℚ) * (e : ℚ) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h8
      linarith
    linarith
  have h9 : c * f > d * e := by
    exact_mod_cast h7
  have h10 : a * f = b * e + 1 := by
    omega
  by_contra h
  push_neg at h
  have h11 : d < b + f := by 
    omega
  -- derivation of contradicts
  have h12 : a * d ≥ b * c + 1 := by
    omega
  have h13 : c * f ≥ d * e + 1 := by
    omega
  -- nlinarith to solve the nonlinear inequalities
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos ha he, mul_pos ha hf, 
          mul_pos hb hc, mul_pos hb hd, mul_pos hb he, mul_pos hb hf, 
          mul_pos hc hd, mul_pos hc he, mul_pos hc hf, 
          mul_pos hd he, mul_pos hd hf, 
          mul_pos he hf]