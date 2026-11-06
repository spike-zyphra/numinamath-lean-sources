import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_150319 {f : ℝ → ℝ}
  (hf : Monotone f)
  (h : ∃ n0, ∀ x, f^[n0] x = -x) :
  ∀ x, f x = -x := by
  rcases h with ⟨n0, hn0⟩
  have h2 : Monotone (f^[n0]) := by 
    apply Monotone.iterate
    exact hf 
  have h3 : ∀ x, f^[n0] x = -x := hn0
  have h4 : ∀ x y : ℝ, x ≤ y → f^[n0] x ≤ f^[n0] y := by 
    intro x y hxy 
    apply h2 
    all_goals linarith 
  have h5 : ∀ x y : ℝ, x ≤ y → -x ≤ -y := by 
    intro x y hxy 
    have h1 : f^[n0] x ≤ f^[n0] y := h4 x y hxy 
    rw [h3 x, h3 y] at h1 
    all_goals linarith 
  have h6 := h5 0 1 (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
  norm_num at h6 
  all_goals linarith