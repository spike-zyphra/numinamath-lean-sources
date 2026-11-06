import Mathlib

theorem algebra_134166 {p : Polynomial ℤ} (h : ∀ a b c, a + b + c = 2022 → p.eval a + p.eval b + p.eval c = p.eval 674) (h0 : p.eval 0 = -2696) :
    p.eval 2022 = 5392 := by 
  have h1 := h 674 674 674 (by norm_num)
  have hp674 : p.eval 674 = 0 := by
    linarith [h1]
  have h2 := h 2022 0 0 (by norm_num)
  rw [h0, hp674] at h2
  linarith [h2]