import Mathlib

theorem number_theory_254238 (a b c d e f : ℕ) 
    (ha : a ≠ 0)
    (hdigits : a < 10 ∧ b < 10 ∧ c < 10 ∧ d < 10 ∧ e < 10 ∧ f < 10 ∧ c > 0 ∧ b > 0 ∧ d > 0 ∧ e > 0 ∧ f > 0)
    (h2 : 2 * Nat.ofDigits 10 [f, e, d, c, b, a] = Nat.ofDigits 10 [b, a, f, e, d, c])
    (h3 : 3 * Nat.ofDigits 10 [f, e, d, c, b, a] = Nat.ofDigits 10 [a, f, e, d, c, b])
    (h4 : 4 * Nat.ofDigits 10 [f, e, d, c, b, a] = Nat.ofDigits 10 [d, c, b, a, f, e])
    (h5 : 5 * Nat.ofDigits 10 [f, e, d, c, b, a] = Nat.ofDigits 10 [e, d, c, b, a, f])
    (h6 : 6 * Nat.ofDigits 10 [f, e, d, c, b, a] = Nat.ofDigits 10 [c, b, a, f, e, d]) :
    Nat.ofDigits 10 [f, e, d, c, b, a] = 142857 := by
  rcases hdigits with ⟨ha1, hb, hc, hd, he, hf, hc1, hb1, hd1, he1, hf1⟩
  simp [Nat.ofDigits, List.foldl] at h2 h3 h4 h5 h6 ⊢ 
  norm_num [ha1, hb, hc, hd, he, hf, hb1, hc1, hd1, he1, hf1] at h2 h3 h4 h5 h6 ⊢
  omega