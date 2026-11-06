import Mathlib

theorem algebra_326525 {a : ℝ} (ha : 0 < a ∧ a < 1) (x : ℕ → ℝ)
    (hx1 : x 1 = a) (hxn : ∀ n, x (n + 1) = a ^ x n) :
    Odd n → x n < x (n + 2) ∧ Even n → x (n + 2) < x n := by
  intro h_odd_n h
  -- Assume n is odd and n is even, which is a contradiction
  have h_contra : False := by
    have h1 : Odd n := h_odd_n
    have h2 : Even n := h.right
    have h3 : ¬Odd n := by
      exact Nat.not_odd_iff_even.mpr h2
    contradiction
  exact False.elim h_contra