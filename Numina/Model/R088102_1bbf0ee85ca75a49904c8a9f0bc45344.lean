import Mathlib

open Real

theorem algebra_173248 (a : ℝ) (ha : 0 < a ∧ a < 1)
    (x : ℕ → ℝ) (hx1 : x 1 = a) (hxn : ∀ n, x (n + 1) = a ^ x n) :
    Odd n → x n < x (n + 2) ∧ Even n → x (n + 2) < x n := by
  intro h_odd_n h
  have h1 : Odd n := h_odd_n
  have h2 : Even n := h.right
  have h3 : n % 2 = 1 := by 
    obtain ⟨k, hk⟩ := h1
    omega
  have h4 : n % 2 = 0 := by 
    obtain ⟨m, hm⟩ := h2
    omega
  omega