import Mathlib

theorem number_theory_274090 (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) :
    ∃ x y : ℤ, (a^2 + b^2)^n = x^2 + y^2 := by
  have h1 : ∀ n : ℕ, n > 0 → ∃ x y : ℤ, (a ^ 2 + b ^ 2) ^ n = x ^ 2 + y ^ 2 := by
    intro n hn
    induction n with 
    | zero => 
      exfalso
      linarith 
    | succ n ih => 
      cases n with 
      | zero => 
        use a
        use b 
        norm_num
      | succ n => 
        rcases ih (by linarith) with ⟨x, y, hxy⟩ 
        use (a * x - b * y)
        use (b * x + a * y)
        rw [pow_succ, hxy]
        ring_nf
  specialize h1 n hn
  exact h1