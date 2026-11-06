import Mathlib
theorem algebra_605465 :
  IsLeast {x : ℝ | ∃ a b c d : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ a + b + c + d = 4 ∧ x =
    a / (b ^ 3 + 4) + b / (c ^ 3 + 4) + c / (d ^ 3 + 4) + d / (a ^ 3 + 4)} (2 / 3) := by
  constructor
  · -- Show 2/3 is attainable by some nonnegative a, b, c, d with sum 4
    use 2, 2, 0, 0
    norm_num
  · -- Now show that 2/3 is the lower bound
    intro x h
    rcases h with ⟨a, b, c, d, ha, hb, hc, hd, h_sum, hx⟩
    
    have h1 : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → x / (y ^ 3 + 4) ≥ x * (1 / 4 - y / 12):= by
      intro x y hx hy
      rw [show x / (y ^ 3 + 4) = x * (1 / (y ^ 3 + 4)) by ring]
      -- Prove that 1/(y³+4) ≥ 1/4 - y/12
      have h1 : 1 / (y ^ 3 + 4) ≥ 1 / 4 - y / 12:= by
        have h1 : y ^ 3 + 4 > 0:= by positivity
        suffices (y ^ 3 + 4) * (1 / (y ^ 3 + 4)) ≥ (y ^ 3 + 4) * (1 / 4 - y / 12) by exact le_of_mul_le_mul_left this h1
        rw [show (y ^ 3 + 4) * (1 / (y ^ 3 + 4)) = 1 by field_simp]
        -- Use the fact that y(y+1)(y-2)² ≥ 0 for y ≥ 0
        replace h1 : y * (y + 1) * (y - 2) ^ 2 ≥ 0:= by positivity
        linarith
      exact mul_le_mul_of_nonneg_left h1 hx
    
    have h2:= h1 a b ha hb
    have h3:= h1 b c hb hc
    have h4:= h1 c d hc hd
    have h5:= h1 d a hd ha
    have h6 : a / (b ^ 3 + 4) + b / (c ^ 3 + 4) + c / (d ^ 3 + 4) + d / (a ^ 3 + 4) ≥ 
    a * (1 / 4 - b / 12) + b * (1 / 4 - c / 12) + c * (1 / 4 - d / 12) + d * (1 / 4 - a / 12) := by linarith [h2, h3, h4, h5]
    
    have h7 : a * (1 / 4 - b / 12) + b * (1 / 4 - c / 12) + c * (1 / 4 - d / 12) + d * (1 / 4 - a / 12) = 
        1 - (1 / 12) * (a * b + b * c + c * d + d * a) := by 
      nlinarith [h_sum]

    have h8 : (a * b + b * c + c * d + d * a) ≤ 4:= by 
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + c - 2), sq_nonneg (b + d - 2), h_sum]

    have h9 : 1 - (1 / 12) * (a * b + b * c + c * d + d * a) ≥ 2 / 3:= by 
      nlinarith [h8]

    linarith [hx, h7, h9, h6]