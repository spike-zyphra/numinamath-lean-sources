import Mathlib
open Finset

theorem number_theory_6303 {f : ℕ → ℕ} (hf : ∀ x, f (x + 3) = f x + 1) (hf' : ∀ x, f (x + 1) = f x + 1) (hf'' : f 0 = 1) (hf''' : f 1 = 1) : f 2020 = 5 := by
  have h1 : f 1 = f 0 + 1 := by
    specialize hf' 0
    simpa using hf'
  rw [hf''] at h1
  omega