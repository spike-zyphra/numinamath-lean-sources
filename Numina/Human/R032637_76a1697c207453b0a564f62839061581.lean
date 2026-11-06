import Mathlib

variable {T : Type*} (a : T) (Star : T → T → T)


open Classical Set
namespace Algebra_611297

infixl:70 " ⋆ " => Star
/-- Definition of the image of an element `a` under `⋆` operation. --/


def starImage : Set T := { c | ∃ b : T, c =  a ⋆ b}

end Algebra_611297

open Algebra_611297

/-- Theorem: If `c` is in the image of `a`, then `a ⋆ c = c`. --/
theorem Algebra_611297 {c : T} (h : ∃ b : T, c =  a ⋆ b) (ha : a ⋆ a = a) 
  (h_assoc :∀ (x : T), ∀ (y : T), ∀ (z : T), x ⋆ y ⋆ z = x ⋆ (y ⋆ z)) : a ⋆ c = c :=
  let ⟨b, hb⟩ := h
  calc
    a ⋆ c = a ⋆ (a ⋆ b) := by rw [hb]
    _ = (a ⋆ a) ⋆ b := Eq.symm (h_assoc a a b) -- this operation is associative
    _ = a ⋆ b := by rw [ha]
    _ = c := by rw [hb]