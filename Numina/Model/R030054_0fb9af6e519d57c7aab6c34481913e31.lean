import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem number_theory_4549 (a b c d e f : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9)
    (h₂ : 0 ≤ c ∧ c ≤ 9) (h₃ : 0 ≤ d ∧ d ≤ 9) (h₄ : 0 ≤ e ∧ e ≤ 9) (h₅ : 0 ≤ f ∧ f ≤ 9)
    (h₆ : a ≠ b) (h₇ : a ≠ c) (h₈ : a ≠ d) (h₉ : a ≠ e) (h₁₀ : a ≠ f)
    (h₁₁ : b ≠ c) (h₁₂ : b ≠ d) (h₁₃ : b ≠ e) (h₁₄ : b ≠ f) (h₁₅ : c ≠ d)
    (h₁₆ : c ≠ e) (h₁₇ : c ≠ f) (h₁₈ : d ≠ e) (h₁₉ : d ≠ f) (h₂₀ : e ≠ f)
    (h₂₁ : 3 * (a * 100000 + b * 10000 + c * 1000 + d * 100 + e * 10 + f) =
    4 * (d * 100000 + e * 10000 + f * 1000 + a * 100 + b * 10 + c)) :
    a * 100000 + b * 10000 + c * 1000 + d * 100 + e * 10 + f = 571428 := by
  have h8 : 299600 * a + 29960 * b + 2996 * c = 399700 * d + 39970 * e + 3997 * f := by
    omega
  have h9 : 42800 * a + 4280 * b + 428 * c = 57100 * d + 5710 * e + 571 * f := by
    omega
  have h10 : 428 * (100 * a + 10 * b + c) = 571 * (100 * d + 10 * e + f) := by
    omega
  have h11 : a = 5 := by
    omega
  have h12 : b = 7 := by
    omega
  have h13 : c = 1 := by
    omega
  have h14 : d = 4 := by
    omega
  have h15 : e = 2 := by
    omega
  have h16 : f = 8 := by
    omega
  simp [h11, h12, h13, h14, h15, h16]