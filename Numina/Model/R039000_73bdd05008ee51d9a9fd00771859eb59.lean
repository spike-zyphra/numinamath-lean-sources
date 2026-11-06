import Mathlib

open Finset

theorem algebra_93183 {f g : ℕ → ℕ → ℕ}
    (hf : ∀ a b, f a b = max a b) (hg : ∀ a b, g a b = min a b) :
    ∀ a b c, f a b = f b a ∧ f a (f b c) = f (f a b) c ∧
    g a (f b c) = f (g a b) (g a c) := by 
  intro a b c 
  constructor 
  · -- Show that $f a b = f b a$ (commutativity of max)
    rw [hf, hf]
    simp [max_comm]
  constructor
  · -- Show that $f a (f b c) = f (f a b) c$ (associativity of max)
    rw [hf, hf, hf, hf]
    simp [max_assoc]
  · -- Show that $g a (f b c) = f (g a b) (g a c)$ (distributivity of min over max)
    rw [hg, hf, hf, hg, hg]
    simp [min_max_distrib_left]