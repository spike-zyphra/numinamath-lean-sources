import Mathlib
open Set

theorem algebra_4909 {f : ℝ → ℝ}
    (hf : ∀ x, 0 < x → 0 < f x)
    (hff : ∀ x > 0, f (f (f x)) = x ^ 3) :
    f 1 = 1 := by
  have h1 : f (f (f 1)) = 1 ^ 3 := by
    apply hff
    norm_num
  have h2 : f (f (f (f 1))) = (f 1) ^ 3 := by
    apply hff
    have h1_pos : 0 < f 1 := hf 1 (by norm_num)
    linarith
  have eq1 : f (f (f (f 1))) = f 1 := by
    have h1' : f (f (f 1)) = 1 := by
      norm_num at h1 ⊢
      linarith
    calc
      f (f (f (f 1))) = f ( (f (f (f 1))) ) := by ring_nf
      _ = f 1 := by
        rw [h1']
  -- Now we can write f(1) = (f 1)^3
  have h3 : f 1 = (f 1) ^ 3 := by
    linarith [h2, eq1]
  have h1_pos : 0 < f 1 := hf 1 (by norm_num)
  have h4 : f 1 > 0 := h1_pos
  have h5 : (f 1) ^ 3 - f 1 = 0 := by
    nlinarith
  have h6 : f 1 * ((f 1) ^ 2 - 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- Case $f 1 = 0$
    linarith
  · -- Case $(f 1) ^ 2 - 1 = 0$
    have h5 : (f 1) ^ 2 = 1 := by
      nlinarith
    have h7 : f 1 = 1 := by
      nlinarith [h5, h4]
    linarith [h7]