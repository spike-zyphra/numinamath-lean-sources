import Mathlib

open Finset

theorem number_theory_32435 {f : ℕ → ℕ → ℕ}
    (hf1 : ∀ n, f n 1 = 1)
    (hfn : ∀ n, ∀ j ∈ Icc 1 (n / 2), f n (2 * j) = j)
    (hfn' : ∀ n k, f n (2 * k - 1) = if Odd n then k + f (k + 1) 1 else k + f (k + 1) (k + 1))
    (hfn'' : ∀ n k, f n (2 * k + 1) = if Odd n then k + f (k + 1) 1 else k + f (k + 1) (k + 1)) :
    ∀ n x, f n x = x ↔ ∃ d, 0 < d ∧ x = ((2 * n + 1) * (2 ^ d - 1)) / (2 ^ (d + 1) - 1) := by
  have h1 := hf1 2
  have h4 : f 2 2 = 1 := by
    have h5 := hfn 2 1
    simp at h5 ⊢
    all_goals tauto
  have h5 : f 2 1 = 1 := by 
    apply hf1 2
  have h6 := hfn' 2 1
  -- Expanding h6 gives f 2 1 = 1 + f 2 2 = 2
  have h7 : (2 * (1 : ℕ) - 1) = 1 := by
    omega
  simp [show ¬ (Odd (2 : ℕ)) by decide, show (1 + 1 : ℕ) = 2 by omega, h4] at h6 
  all_goals omega