import Mathlib

theorem number_theory_241597 (a b : ℤ) (h : a + b ≡ 0 [ZMOD 10]) :
    (a^2) ≡ (b^2) [ZMOD 10] := by
  have h1 : a ≡ -b [ZMOD 10] := by 
    have h2 : a + b ≡ 0 [ZMOD 10] := h
    simp [Int.ModEq] at h2 ⊢
    omega
  have h3 : a^2 ≡ (-b)^2 [ZMOD 10] := by 
    apply Int.ModEq.pow
    exact h1
  have h4 : (-b : ℤ) ^ 2 = b^2 := by 
    ring
  rw [h4] at h3
  exact h3