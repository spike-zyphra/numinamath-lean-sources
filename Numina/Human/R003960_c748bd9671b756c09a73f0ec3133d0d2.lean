import Mathlib

/- 4. Given three real numbers greater than 1. The product of any two of them is greater than the sum of these two. Prove that the product of all three numbers is greater than their sum, increased by 2. -/
theorem inequalities_225224 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h1 : a * b > a + b) (h2 : b * c > b + c) (h3 : a * c > a + c) :
    a * b * c > a + b + c + 2 := by
  -- assume a ≤ b ≤ c wlog
  wlog h : a ≤ b ∧ b ≤ c
  . push_neg at h
    obtain h' | h' := le_or_lt a b
    . obtain h'' | h'' := le_or_lt a c
        -- a ≤ c ≤ b
      . linear_combination (this a c b (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ⟨h'', by linarith [h h']⟩)
        -- c ≤ a ≤ b
      . linear_combination (this c a b (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ⟨by linarith, h'⟩)
    . obtain h'' | h'' := le_or_lt b c
      . obtain h''' | h''' := le_or_lt a c
          -- b ≤ a ≤ c
        . linear_combination (this b a c (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ⟨by linarith, by linarith⟩)
          -- b ≤ c ≤ a
        . linear_combination (this b c a (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ⟨by linarith, by linarith⟩)
        -- c ≤ b ≤ a
      . linear_combination (this c b a (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ⟨by linarith, by linarith⟩)
  obtain ⟨hab, hbc⟩ := h
  -- let's prove 2 < c from 2a < ca
  have hc' : 2 < c := by
    have : 2 * a < c * a := calc
      2 * a = a + a := by ring
      _ ≤ a + c := by gcongr; linarith
      _ < a * c := by assumption
      _ = c * a := by ring
    apply lt_of_mul_lt_mul_of_nonneg_right this
    linarith
  -- now prove abc > a+b+c+2
  calc
    a*b*c > (a+b)*c := by gcongr
    _ = a*c + b*c := by ring
    _ > (a + c) + (b + c) := by gcongr
    _ = a + b + c + c := by ring
    _ > a + b + c + 2 := by gcongr