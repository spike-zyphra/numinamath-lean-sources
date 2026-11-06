import Mathlib

theorem algebra_225882 {S : Type*} (f : S → S → S) (h : ∀ a b, f (f a b) a = b) :
    ∀ a b, f a (f b a) = b := by
  intro a b
  have eq1 : f (f (f b a) b) (f b a) = b := by 
    apply h 
  have eq2 : f (f b a) b = a := by 
    apply h 
  rw [eq2] at eq1 
  exact eq1