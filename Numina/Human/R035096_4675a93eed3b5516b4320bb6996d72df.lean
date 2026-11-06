import Mathlib

/- Show that if the sum of two integers ends in 0, then the square of each number ends in the same digit. -/
theorem number_theory_288319 (a b : ℤ) (h : (a + b) % 10 = 0) :
    a^2 ≡ b^2 [ZMOD 10] := by
  have h1 : a ≡ -b [ZMOD 10] := by
    have h2 : (a + b) ≡ 0 [ZMOD 10] := by
      exact h
    have h3 : a ≡ -b [ZMOD 10] := by
      norm_num [Int.ModEq] at *
      omega
    exact h3
  have h4 : a^2 ≡ (-b)^2 [ZMOD 10] := by
    apply Int.ModEq.pow 2 h1
  have h5 : (-b:ℤ)^2 = b^2 := by ring
  rw [h5] at h4
  exact h4