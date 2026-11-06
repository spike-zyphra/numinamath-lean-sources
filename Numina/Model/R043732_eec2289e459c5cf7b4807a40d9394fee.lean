import Mathlib
theorem algebra_607254 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b + b * c + c * a = a * b * c) :
1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) ≤ 1 / 6 ∧ (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) = 1 / 6 ↔ (a = 3 ∧ b = 3 ∧ c = 3)):= by
  have h1 : ∀ x y : ℝ, 0 < x → 0 < y → 1 / (x ^ 2 + y ^ 2) ≤ 1 / (2 * x * y) := by
    intro x y hx hy
    have h₂ : 0 < 2 * x * y := by positivity
    have h₃ : x ^ 2 + y ^ 2 ≥ 2 * x * y := by
      nlinarith [sq_nonneg (x - y)]
    have h₄ : 1 / (x ^ 2 + y ^ 2) ≤ 1 / (2 * x * y) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      all_goals nlinarith
    exact h₄
  have h4 : 1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) ≤ 1 / (2 * a * b) + 1 / (2 * b * c) + 1 / (2 * c * a) := by
    linarith [h1 a b ha hb, h1 b c hb hc, h1 c a hc ha]
  have h5 : 1 / (2 * a * b) + 1 / (2 * b * c) + 1 / (2 * c * a) = (a + b + c) / (2 * a * b * c) := by
    field_simp
    ring
  have h6 : (a + b + c) / (2 * a * b * c) ≤ 1 / 6 := by
    have h7 : a * b * c > 0 := by positivity
    have h8 : (a + b + c) / (2 * a * b * c) ≤ 1 / 6 := by
      have pos1 : 0 < (2 * a * b * c : ℝ) := by positivity
      have pos2 : 0 < (6 : ℝ) := by norm_num
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, h, 
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)
      ]
    exact h8
  have h7 : 1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) ≤ 1 / 6 := by
    linarith [h4, h5, h6]
  have eq_iff : 1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) = 1 / 6 ↔ (a = 3 ∧ b = 3 ∧ c = 3) := by 
    constructor
    · -- Assume the equality holds, proving a = 3 ∧ b = 3 ∧ c = 3.
      intro heq
      have h8 : (a - b) ^ 2 = 0 := by 
        have h11 : 1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) = 1 / (2 * a * b) + 1 / (2 * b * c) + 1 / (2 * c * a) := by
          linarith [show 1 / (2 * a * b) + 1 / (2 * b * c) + 1 / (2 * c * a) ≤ 1 / 6 by linarith [h5, h6], heq, show 1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) ≤ 1 / (2 * a * b) + 1 / (2 * b * c) + 1 / (2 * c * a) by linarith [h4]
          ]
        have eq1 : 1 / (a ^ 2 + b ^ 2) = 1 / (2 * a * b) := by
          linarith [h11, show (1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2)) = (1 / (2 * b * c) + 1 / (2 * c * a)) by nlinarith [h11, show 1 / (a ^ 2 + b^2) ≤ 1/(2*a*b) from by apply h1; all_goals linarith, show 1 / (b ^ 2 + c ^ 2) ≤ 1 / (2 * b * c) from by apply h1; all_goals linarith, show 1 / (c ^ 2 + a ^ 2) ≤ 1 / (2 * c * a) from by apply h1; all_goals linarith]]
        have h9 : 0 < a ^ 2 + b ^ 2 := by positivity
        have h10 : 0 < 2 * a * b := by positivity
        have h12 : 2 * a * b = a ^ 2 + b ^ 2 := by 
          field_simp at eq1
          nlinarith [eq1]
        nlinarith
      have h9 : (b - c) ^ 2 = 0 := by 
        have h11 : 1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) = 1 / (2 * a * b) + 1 / (2 * b * c) + 1 / (2 * c * a) := by
          linarith [show 1 / (2 * a * b) + 1 / (2 * b * c) + 1 / (2 * c * a) ≤ 1 / 6 by linarith [h5, h6], heq, show 1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) ≤ 1 / (2 * a * b) + 1 / (2 * b * c) + 1 / (2 * c * a) by linarith [h4]
          ]
        have eq1 : 1 / (b ^ 2 + c ^ 2) = 1 / (2 * b * c) := by 
          linarith [h11, show (1 / (a ^ 2 + b ^ 2) + 1 / (c ^ 2 + a ^ 2)) = (1 / (2 * a * b) + 1 / (2 * c * a)) by nlinarith [h11, show 1 / (a ^ 2 + b^2) ≤ 1/(2*a*b) from by apply h1; all_goals linarith, show 1 / (b ^ 2 + c ^ 2) ≤ 1 / (2 * b * c) from by apply h1; all_goals linarith, show 1 / (c ^ 2 + a ^ 2) ≤ 1 / (2 * c * a) from by apply h1; all_goals linarith]]
        have h9 : 0 < b ^ 2 + c ^ 2 := by positivity
        have h10 : 0 < 2 * b * c := by positivity
        have h12 : 2 * b * c = b ^ 2 + c ^ 2 := by
          field_simp at eq1
          nlinarith [eq1]
        nlinarith
      have ha4 : a = b := by
        nlinarith 
      have hb4 : b = c := by
        nlinarith 
      have ha5 : a = 3 := by 
        have h7 : a * b + b * c + c * a = a * b * c := h 
        rw [show b = a by linarith [ha4], show c = a by linarith [hb4] ] at h7
        nlinarith [sq_nonneg (a ^ 2 - 9), sq_pos_of_pos ha]
      have hb5 : b = 3 := by 
        linarith [ha4, ha5]
      have hc5 : c = 3 := by 
        linarith [hb4, hb5]
      exact ⟨ha5, hb5, hc5⟩
    · -- Assume (a, b, c) = (3, 3, 3) and prove the equality.
      rintro ⟨rfl, rfl, rfl⟩ 
      norm_num at h ⊢
      all_goals linarith
  constructor 
  · linarith [h7]
  · exact eq_iff