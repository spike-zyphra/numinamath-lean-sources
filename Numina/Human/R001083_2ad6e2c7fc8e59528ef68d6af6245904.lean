import Mathlib

/-
Let x and y be real numbers satisfying x^4y^5+y^4x^5=810 and x^3y^6+y^3x^6=945. Evaluate 2x^3+(xy)^3+2y^3.
-/
theorem algebra_20374 {x y : ℝ} (h1 : x ^ 4 * y ^ 5 + y ^ 4 * x ^ 5 = 810) (h2 : x ^ 3 * y ^ 6 + y ^ 3 * x ^ 6 = 945) :
2 * x ^ 3 + (x * y) ^ 3 + 2 * y ^ 3 = 89 := by
  -- we'll try to express equations in terms of x*y and x+y, first manipulate first one to get (xy)^4 (x+y) = 810
  have h1' : (x * y)^4 * (x + y) = 810 := calc
    (x * y)^4 * (x + y) = x^4 * y^5 + y^4 * x^5 := by ring
    _ = 810 := by assumption
  -- next manipulate 2nd equation to get (xy)^3((x+y)^3 - 3xy(x+y)) = 945
  have h2' : (x * y)^3 * (x + y)^3 - 3 * ((x * y)^4 * (x + y)) = 945 := calc
    (x * y)^3 * (x + y)^3 - 3 * ((x * y)^4 * (x + y)) = x ^ 3 * y ^ 6 + y ^ 3 * x ^ 6 := by ring
    _ = 945 := by assumption
  -- plug in the h1' in h2' to get (xy(x+y))^3 = 3375 = 15^3
  rw [h1'] at h2'
  have : ((x * y) * (x + y)) ^ 3 = 15^3 := by linarith
  -- prove an independent lemma that, a^3 = b^3 means a = b, this can be proven by using that a^n = b^n means a = b or a = -b with n odd
  have h_eq_cube (a b : ℝ) (h: a^3 = b^3) : (a = b) := by
    have : a = b ∨ a = -b ∧ Even 3 := (pow_eq_pow_iff_of_ne_zero (by norm_num: 3 ≠ 0)).1 h
    cases this with
    | inl h => assumption
    | inr h =>
      have hf' : ¬ Even 3 := by
        apply Nat.not_even_iff_odd.2
        apply Nat.odd_iff.2
        rfl
      exact False.elim (hf' h.2)
  -- using the lemma, prove xy(x+y) = 15, this can now be plugged in original 1st equation to get (xy)^3 = 54
  have hxy : x * y * (x + y) = 15 := by exact h_eq_cube (x * y * (x + y)) 15 this
  have hxy_cb : (x * y)^3 = 54 := by
    have : (x * y)^3 * (x * y * (x + y)) = 810 := by linarith
    rw [hxy] at this
    linarith
  -- plug in (xy)^3 in original 2nd equation to get x^3 + y^3 = 17.5
  have hx_cb_y_cb : x^3 + y^3 = 17.5 := by
    have : (x * y)^3 * (x^3 + y^3) = 945 := calc
      (x * y)^3 * (x^3 + y^3) = x^3 * y^6 + y^3 * x^6 := by ring
      _ = 945 := by assumption
    rw [hxy_cb] at this
    linarith
  -- now just calculate the target expression using known facts
  calc
    2 * x ^ 3 + (x * y) ^ 3 + 2 * y ^ 3 = 2 * (x^3 + y^3) + (x*y)^3 := by ring
    _ = 2 * 17.5 + 54 := by rw [hx_cb_y_cb, hxy_cb]
    _ = 89 := by norm_num