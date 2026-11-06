import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_153567 (f g : ℝ → ℝ)
  (hf : f = λ x => x^3) (hg : g = λ x => sqrt x) :
  ∫ x in (0)..1, π * (g x)^2 - π * (f x)^2 = 5 * π / 14 := by
  have h1 : ∀ x, g x = sqrt x := by
    intro x 
    rw [hg]

  have h2 : ∀ x, f x = x ^ 3 := by
    intro x
    rw [hf]
  have h4 : ∫ x in (0)..1, π * (g x)^2 - π * (f x)^2 = ∫ x in (0)..1, π * (sqrt x) ^ 2 - π * (x ^ 3) ^ 2 := by
    congr
    funext x 
    have h4 : g x = sqrt x := h1 x 
    have h5 : f x = x ^ 3 := h2 x 
    rw [h4, h5]
  have h3 : ∫ x in (0)..1, π * (sqrt x) ^ 2 - π * (x ^ 3) ^ 2 = 5 * π / 14 := by
    have h5 : ∀ x, x ∈ Set.Icc (0 : ℝ) 1 → π * (sqrt x) ^ 2 - π * (x ^ 3) ^ 2 = π * (x - x ^ 6) := by
      intro x hx 
      have h5 : 0 ≤ x := by
        have h5 : x ∈ Set.Icc (0 : ℝ) 1 := hx 
        exact h5.1 
      have h6 : (sqrt x) ^ 2 = x := by
        rw [Real.sq_sqrt]
        linarith
      have h7 : (x ^ 3) ^ 2 = x ^ 6 := by 
        ring
      calc
        π * (sqrt x) ^ 2 - π * (x ^ 3) ^ 2 = π * ( (sqrt x) ^ 2 ) - π * (x ^ 6) := by 
          rw [h7]
        _ = π * x - π * (x ^ 6) := by
          rw [h6]
        _ = π * (x - x ^ 6) := by 
          ring
    rw [intervalIntegral.integral_congr (fun x hx => h5 x (by simpa using hx))]
    simp [intervalIntegral.integral_const, mul_comm]
    ring_nf
    <;> field_simp 
    all_goals ring
  rw [h4]
  exact h3