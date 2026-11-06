import Mathlib

theorem algebra_380691 (a : ℕ → ℤ) (ha1 : a 1 = 4) (han : ∀ n, a (n + 1) - a n = 3) :
    ∀ n > 0, n ≤ 6 → a n = 3 * n + 1 := by
-- use `match` command to handle all the six cases one by one
  intro n npos hn
  match n with
  | 1 =>
    simp [ha1]
  | 2 =>
    specialize han 1
    simp at han
    omega
  | 3 => 
    have h2 := han 2
    have h1 := han 1
    simp at h1 h2
    omega
  | 4 => 
    have h3 := han 3
    have h2 := han 2
    have h1 := han 1
    simp at h1 h2 h3
    omega
  | 5 => 
    have h4 := han 4
    have h3 := han 3
    have h2 := han 2
    have h1 := han 1
    simp at h1 h2 h3 h4
    omega
  | 6 => 
    have h5 := han 5
    have h4 := han 4
    have h3 := han 3
    have h2 := han 2
    have h1 := han 1
    simp at h1 h2 h3 h4 h5
    omega