import Mathlib

/- What is the smallest positive four-digit integer equivalent to 6 mod 7? -/
theorem number_theory_13269 : IsLeast {n | 0 < n ∧ n ∈ Finset.Icc 1000 9999 ∧ n % 7 = 6} 1000 := by 
  exact ⟨by decide, fun a ⟨ha₀, ha₁, ha₂⟩ => by
    norm_num at ha₁
    omega⟩