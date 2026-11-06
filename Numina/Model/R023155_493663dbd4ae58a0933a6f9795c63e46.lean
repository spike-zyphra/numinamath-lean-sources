import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_71820
  (f : ℝ → ℝ)
  (g : ℝ → ℝ)
  (h : ℝ → ℝ)
  (h₀ : ∀ x, g x = f x + f (2 * x))
  (h₁ : ∀ x, h x = f x + f (4 * x))
  (h₂ : Continuous g)
  (h₃ : Continuous h) :
  Continuous f := by 
  have h4 : ∀ x, f x = (1 / 2) * (g x + h x - g (2 * x)) := by 
    intro x
    have eq1 := h₀ x
    have eq2 := h₁ x 
    have eq3 := h₀ (2 * x)
    ring_nf at eq1 eq2 eq3 ⊢ 
    linarith 
  have h5 : f = fun x => (1 / 2) * (g x + h x - g (2 * x)) := by 
    funext x 
    simpa using h4 x 
  rw [h5] 
  have h7 : Continuous (fun (x : ℝ) => (1 / 2) * (g x + h x - g (2 * x))) := by 
    have h3c : Continuous (fun (x : ℝ) => g x + h x - g (2 * x)) := by 
      have h8 : Continuous (fun (x : ℝ) => g x) := h₂ 
      have h9 : Continuous (fun (x : ℝ) => h x) := h₃ 
      have h10 : Continuous (fun (x : ℝ) => 2 * x) := by
        apply continuous_const.mul continuous_id 
      have h11 : Continuous (fun (x : ℝ) => g (2 * x)) := by 
        exact_mod_cast h₂.comp (by exact_mod_cast h10) 
      exact_mod_cast (h8.add h9).sub h11 
    have h8 : Continuous (fun (x : ℝ) => (1 / 2) * (g x + h x - g (2 * x))) := by 
      have h9 : Continuous (fun (x : ℝ) => g x + h x - g (2 * x)) := h3c 
      exact_mod_cast (continuous_const.mul h9)
    exact_mod_cast h8 
  simpa using h7