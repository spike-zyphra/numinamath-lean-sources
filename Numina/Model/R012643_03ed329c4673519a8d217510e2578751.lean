import Mathlib

/- If positive integers $a$, $b$ satisfy $\frac{3}{4}<{}\frac{a}{b}<{}\frac{4}{5}$, and $a+b$ is minimized, then $a=$ ___          ___ , $b=$ ___          ___. -/
theorem number_theory_1162 :
    IsLeast {x | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ (3 / 4 : ℚ) < a / b ∧ a / b < (4 / 5 : ℚ) ∧ x = a + b} (7 + 9) := by
  constructor
  · -- Show 7 + 9 is in the set.
    use 7, 9
    norm_num
  · -- Show no smaller element is in the set.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h1, h2, hx⟩
    by_contra h
    push_neg at h
    have h3 : (x : ℤ) < 16 := by
      omega
    have h4 : a + b < 16 := by
      omega
    have h5 : a > 0 := ha
    have h6 : b > 0 := hb
    have h7 : a < 16 := by
      omega
    have h8 : b < 16 := by
      omega
    interval_cases a <;> interval_cases b 
      <;> norm_num at h1 h2 
      <;> omega