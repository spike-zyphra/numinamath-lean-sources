import Mathlib

open Real

theorem inequalities_284761 (a b c s : ℝ)
  (hpos : a > 0 ∧ b > 0 ∧ c > 0)
  (htri : a + b > c ∧ a + c > b ∧ b + c > a)
  (hs : s = (a + b + c) / 2) :
  a^2 + b^2 + c^2 ≥ √(s * (s - a) * (s - b) * (s - c)) * 4 * √3 := by
  have ha : a > 0 := hpos.1
  have hb : b > 0 := hpos.2.1
  have hc : c > 0 := hpos.2.2

  have h1 : a + b > c := htri.1
  have h2 : a + c > b := htri.2.1
  have h3 : b + c > a := htri.2.2

  have h4 : s > a := by
    rw [hs]
    nlinarith
  have h5 : s > b := by
    rw [hs]
    nlinarith
  have h6 : s > c := by
    rw [hs]
    nlinarith

  have h7 : s - a > 0 := by linarith
  have h8 : s - b > 0 := by linarith
  have h9 : s - c > 0 := by linarith

  have h10 : s * (s - a) * (s - b) * (s - c) > 0 := by
    have ha1 : s - a > 0 := h7
    have ha2 : s - b > 0 := h8
    have ha3 : s - c > 0 := h9
    have ha4 : s > 0 := by linarith [ha, hb, hc, h4, h5, h6]
    positivity

  have h11 : (a^2 + b^2 + c^2) ^ 2 ≥ 48 * (s * (s - a) * (s - b) * (s - c)) := by
    rw [hs]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)]
  have h13 : a^2 + b^2 + c^2 ≥ √(s * (s - a) * (s - b) * (s - c)) * 4 * √3 := by
    have h12 : (√(s * (s - a) * (s - b) * (s - c)) * 4 * √3) ^ 2 = 48 * (s * (s - a) * (s - b) * (s - c)) := by
      calc
        (√(s * (s - a) * (s - b) * (s - c)) * 4 * √3) ^ 2
          = (√(s * (s - a) * (s - b) * (s - c)))^2 * (4 * √3) ^ 2 := by ring
        _ = (s * (s - a) * (s - b) * (s - c)) * (4 * √3) ^ 2 := by 
          rw [Real.sq_sqrt]
          positivity
        _ = (s * (s - a) * (s - b) * (s - c)) * (16 * (Real.sqrt 3) ^ 2) := by ring
        _ = (s * (s - a) * (s - b) * (s - c)) * (16 * 3) := by 
          rw [Real.sq_sqrt]
          all_goals norm_num
        _ = 48 * (s * (s - a) * (s - b) * (s - c)) := by ring
    have h14 : (√(s * (s - a) * (s - b) * (s - c)) * 4 * √3) ^ 2 ≤ (a^2 + b^2 + c^2) ^ 2 := by
      nlinarith [h11, h12, Real.sqrt_nonneg (s * (s - a) * (s - b) * (s - c)), Real.sqrt_nonneg 3]
    have h15 : √(s * (s - a) * (s - b) * (s - c)) * 4 * √3 ≥ 0 := by positivity
    have h16 : a^2 + b^2 + c^2 ≥ 0 := by positivity
    nlinarith [sq_nonneg (√(s * (s - a) * (s - b) * (s - c)) * 4 * √3 - (a^2 + b^2 + c^2)), Real.sqrt_nonneg (s * (s - a) * (s - b) * (s - c)), Real.sqrt_nonneg 3, h14, h16, h15]
  exact h13