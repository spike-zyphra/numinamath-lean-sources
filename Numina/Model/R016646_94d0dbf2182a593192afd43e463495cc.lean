import Mathlib

theorem number_theory_83002 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : ∃ m, m^2 = a^2 + b + c) (h2 : ∃ n, n^2 = b^2 + c + a) (h3 : ∃ p, p^2 = c^2 + a + b) :
    False := by 
  rcases h1 with ⟨m, hm⟩
  rcases h2 with ⟨n, hn⟩
  rcases h3 with ⟨p, hp⟩
  have h4 : m > a := by
    by_contra h
    push_neg at h
    have h5 : m ≤ a := by linarith
    have h6 : m ^ 2 ≤ a ^ 2 := by nlinarith
    have h7 : m ^ 2 = a ^ 2 + b + c := by linarith
    nlinarith
  have h8 : n > b := by
    by_contra h
    push_neg at h
    have h9 : n ≤ b := by linarith
    have h10 : n ^ 2 ≤ b ^ 2 := by nlinarith
    have h11 : n ^ 2 = b ^ 2 + c + a := by linarith
    nlinarith
  have h12 : p > c := by
    by_contra h
    push_neg at h
    have h13 : p ≤ c := by linarith
    have h14 : p ^ 2 ≤ c ^ 2 := by nlinarith
    have h15 : p ^ 2 = c ^ 2 + a + b := by linarith
    nlinarith
  have h4' : m ≥ a + 1 := by omega
  have h8' : n ≥ b + 1 := by omega
  have h12' : p ≥ c + 1 := by omega
  nlinarith [sq_nonneg (m - a - 1), sq_nonneg (n - b - 1), sq_nonneg (p - c - 1),
    h4', h8', h12']