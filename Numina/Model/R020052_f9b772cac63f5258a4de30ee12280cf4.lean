import Mathlib

open Finset

theorem number_theory_22996 {f : ℕ → ℕ}
    (hf : ∀ x, f x = ∏ d ∈ (x.divisors.filter (fun y => y > 1 ∧ y ≠ x)), d) :
    f 12 = 144 := by
  have h12 : f 12 = ∏ d ∈ (12).divisors.filter (fun y => y > 1 ∧ y ≠ 12), d := hf 12
  rw [h12]
  native_decide