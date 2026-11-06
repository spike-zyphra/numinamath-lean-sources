import Mathlib

theorem algebra_207833 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 2 * (a^8 + b^8 + c^8) = (a^4 + b^4 + c^4)^2) :
    a^2 + b^2 = c^2 ∨ b^2 + c^2 = a^2 ∨ c^2 + a^2 = b^2 := by
  have eq1 : a^4 + b^4 - c^4 = 2 * a^2 * b^2 ∨ a^4 + b^4 - c^4 = -2 * a^2 * b^2 := by
    have eq2 : (a^4 + b^4 - c^4)^2 = 4 * (a^2)^2 * (b^2)^2 := by
      nlinarith [h, sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2)]
    have eq4 : (a^4 + b^4 - c^4) = 2 * a^2 * b^2 ∨ (a^4 + b^4 - c^4) = -2 * a^2 * b^2 := by 
      have eq5 : (a^4 + b^4 - c^4)^2 - (4 * (a^2)^2 * (b^2)^2) = 0 := by linarith 
      have eq6 : (a^4 + b^4 - c^4 - (2 * a^2 * b^2)) * (a^4 + b^4 - c^4 + (2 * a^2 * b^2)) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.1 eq6) with h7 h8
      · left
        linarith 
      · right
        linarith 
    tauto
  have eq2 : b^4 + c^4 - a^4 = 2 * b^2 * c^2 ∨ b^4 + c^4 - a^4 = -2 * b^2 * c^2 := by
    have eq2 : (b^4 + c^4 - a^4)^2 = 4 * (b^2)^2 * (c^2)^2 := by
      nlinarith [h, sq_nonneg (b^2 - c^2), sq_nonneg (b^2 - a^2), sq_nonneg (c^2 - a^2)]
    have eq4 : (b^4 + c^4 - a^4) = 2 * b^2 * c^2 ∨ (b^4 + c^4 - a^4) = -2 * b^2 * c^2 := by 
      have eq5 : (b^4 + c^4 - a^4)^2 - (4 * (b^2)^2 * (c^2)^2) = 0 := by linarith 
      have eq6 : (b^4 + c^4 - a^4 - (2 * b^2 * c^2)) * (b^4 + c^4 - a^4 + (2 * b^2 * c^2)) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.1 eq6) with h7 h8
      · left
        linarith 
      · right
        linarith 
    tauto
  have eq3 : a^4 + c^4 - b^4 = 2 * a^2 * c^2 ∨ a^4 + c^4 - b^4 = -2 * a^2 * c^2 := by
    have eq2 : (a^4 + c^4 - b^4)^2 = 4 * (a^2)^2 * (c^2)^2 := by
      nlinarith [h, sq_nonneg (a^2 - c^2), sq_nonneg (a^2 - b^2), sq_nonneg (c^2 - b^2)]
    have eq4 : (a^4 + c^4 - b^4) = 2 * a^2 * c^2 ∨ (a^4 + c^4 - b^4) = -2 * a^2 * c^2 := by 
      have eq5 : (a^4 + c^4 - b^4)^2 - (4 * (a^2)^2 * (c^2)^2) = 0 := by linarith 
      have eq6 : (a^4 + c^4 - b^4 - (2 * a^2 * c^2)) * (a^4 + c^4 - b^4 + (2 * a^2 * c^2)) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.1 eq6) with h7 h8
      · left
        linarith 
      · right
        linarith 
    tauto
  -- Now, analyze all possible 8 cases
  have eq4 : a^2 > 0 := by positivity
  have eq5 : b^2 > 0 := by positivity
  have eq6 : c^2 > 0 := by positivity
  rcases eq1 with h1 | h1 <;> rcases eq2 with h2 | h2 <;> rcases eq3 with h3 | h3 <;> 
    try { 
      have eq7 : a ^ 2 + b ^ 2 = c ^ 2 := by 
        nlinarith 
      left 
      linarith 
    } <;> 
    try { 
      have eq8 : b ^ 2 + c ^ 2 = a ^ 2 := by 
        nlinarith 
      right 
      left 
      linarith 
    } <;> 
    try { 
      have eq9 : c ^ 2 + a ^ 2 = b ^ 2 := by 
        nlinarith 
      right 
      right 
      linarith 
    }