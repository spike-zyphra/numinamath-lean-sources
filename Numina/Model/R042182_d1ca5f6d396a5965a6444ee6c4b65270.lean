import Mathlib

open Real

theorem algebra_284015 (a : ℕ → ℝ) (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = a n / (1 + n * a n)) :
    1 / a 2005 - 2000000 = 9011 := by

  have eq1 : ∀ (n : ℕ), a (n + 1) = 1 / (↑(1 : ℝ) + ↑(n ) * (↑(n + 1) / 2) ) := by
    intro n
    induction n with 
    | zero =>
      rw [ha1]
      norm_num
    | succ n ih =>
      have eq2 : a (n + 2) = a (n + 1) / (1 + ↑(n + 1) * a (n + 1) ) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [eq2]
      rw [ih]
      field_simp
      <;> ring_nf

  have h2005 : a 2005 = 1 / 2009011 := by
    have h1 : a 2005 = 1 / (↑1 + ↑(2004) * (↑(2004 + 1) / 2) ) := by
      specialize eq1 2004
      norm_num at eq1 ⊢
      linarith
    rw [h1]
    norm_num

  have h10 : 1 / a 2005 = 2009011 := by
    rw [h2005]
    norm_num

  rw [h10]
  norm_num