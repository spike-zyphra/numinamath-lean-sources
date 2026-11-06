import Mathlib

open Set

theorem other_232199 {X : Type*} :
    ¬ ∃ f : X → Set X, Function.Bijective f := by
  intro h
  rcases h with ⟨f, hf⟩
  have h1 : Function.Surjective f := hf.2
  have h2 : ∀ s : Set X, ∃ x : X, f x = s := h1
  have h3 : ∃ x : X, f x = {x | x ∉ f x} := by 
    apply h2
  rcases h3 with ⟨y, hy⟩
  have h4 : (y ∈ f y) ↔ (y ∈ {x | x ∉ f x}) := by 
    rw [hy]
  have h5 : (y ∈ {x | x ∉ f x}) ↔ (y ∉ f y) := by
    simp
  have h6 : (y ∈ f y) ↔ (y ∉ f y) := by 
    tauto
  -- The statement (y ∈ f y) ↔ (y ∉ f y) is a contradiction.
  have h19 : (y ∈ f y) ↔ (y ∉ f y) := h6
  -- We analyze both directions
  tauto