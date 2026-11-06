import Mathlib

theorem number_theory_6812 (a b c : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : a.gcd b = 1) (x₀ y₀ : ℤ) (h₃ : a * x₀ + b * y₀ = c) :
    ∀ x y : ℤ, a * x + b * y = c ↔ ∃ t : ℤ, x = x₀ - b * t ∧ y = y₀ + a * t := by
  intro x y 
  constructor
  · -- Forward implication: if $a*x + b*y = c$, then there exists t such that $x = x₀ - b*t$ and $y = y₀ + a*t$.
    intro h
    have h₄ : a * (x - x₀) + b * (y - y₀) = 0 := by 
      linarith
    have h5 : a * (x - x₀) = -b * (y - y₀) := by linarith only [h₄]
    have h7 : a ∣ b * (y - y₀) := by 
      use -(x - x₀)
      linarith 
    have h8 : a ∣ (y - y₀) := by
      apply Int.dvd_of_dvd_mul_right_of_gcd_one h7 h₂ 
    obtain ⟨t, ht⟩ := h8
    have ht' : y = y₀ + a * t := by 
      linarith 
    have h9 : x - x₀ = -b * t := by 
      nlinarith 
    have hx' : x = x₀ - b * t := by 
      linarith 
    exact ⟨t, hx', ht'⟩
  · -- Reverse implication: given t such that $x = x₀ - b*t$ and $y = y₀ + a*t$, prove $a*x + b*y = c$.
    rintro ⟨t, hx, hy⟩
    rw [hx, hy]
    have hx_eq : a * (x₀ - b * t) = a * x₀ - a * b * t := by 
      ring 
    have hy_eq : b * (y₀ + a * t) = b * y₀ + a * b * t := by 
      ring 
    linarith [h₃, hx_eq, hy_eq]