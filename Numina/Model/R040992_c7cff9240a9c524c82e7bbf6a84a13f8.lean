import Mathlib

theorem number_theory_47504 (p : ℕ) (hp : p = 1601) (s : Finset ℕ)
    (hs : s = ((Finset.range p).image fun n => n ^ 2 + 1).filter fun n => ¬p ∣ n)
    (x : ℚ) (hx : x = ∑ x ∈ s, (x : ℚ)⁻¹) :
    (p : ℤ) ∣ 2 * x.num + x.den := by 
  rw [hp] at *
  rw [hx, hs]
  native_decide