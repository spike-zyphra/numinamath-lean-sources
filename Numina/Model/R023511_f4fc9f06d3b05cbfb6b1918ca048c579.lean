import Mathlib

open Finset

theorem number_theory_299080 {f : ℕ → ℕ} (hf : ∀ n, IsLeast {x | ¬(x ∣ n)} (f n)) :
    {k | ∃ m, f^[k] m = 2} = {1, 2, 3} := by
  have h1 := hf 0
  have h2 := h1.1
  simp at h2