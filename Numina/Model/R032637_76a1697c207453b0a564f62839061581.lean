import Mathlib

variable {T : Type*} (a : T) (Star : T → T → T)


open Classical Set
namespace Algebra_611297

infixl:70 " ⋆ " => Star
/-- Definition of the image of an element `a` under `⋆` operation. --/


def starImage : Set T := { c | ∃ b : T, c =  a ⋆ b}

end Algebra_611297

open Algebra_611297

theorem Algebra_611297 {c : T} (h : ∃ b : T, c =  a ⋆ b) (ha : a ⋆ a = a) 
  (h_assoc :∀ (x : T), ∀ (y : T), ∀ (z : T), x ⋆ y ⋆ z = x ⋆ (y ⋆ z)) : a ⋆ c = c := by 
  rcases h with ⟨b, hb⟩
  calc
    a ⋆ c = a ⋆ (a ⋆ b) := by rw [hb]
    _ = (a ⋆ a) ⋆ b := by rw [h_assoc a a b]
    _ = a ⋆ b := by rw [ha]
    _ = c := by rw [hb]