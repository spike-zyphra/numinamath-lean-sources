import Mathlib

theorem number_theory_288319 (a b : ℤ) (h : (a + b) % 10 = 0) :
    a^2 ≡ b^2 [ZMOD 10] := by
  have h1 : a ≡ ( -b ) [ZMOD 10] := by
    have h6 : (a + b) % 10 = 0 := h
    have h7 : (a + b) ≡ 0 [ZMOD 10] := by 
      exact h
    simp [Int.ModEq] at h7 ⊢
    all_goals 
      omega
  have h2 : (a ^ 2) ≡ (-b) ^ 2 [ZMOD 10] := by 
    apply Int.ModEq.pow 2 h1 
  have h3 : (-b : ℤ) ^ 2 = (b : ℤ) ^ 2 := by 
    ring 
  rw [h3] at h2 
  exact h2