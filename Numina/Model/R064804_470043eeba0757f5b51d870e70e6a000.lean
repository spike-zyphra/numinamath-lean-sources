import Mathlib

open Finset

theorem algebra_167892 {f g : ℤ → ℤ → ℝ}
    (hf : ∀ x y, f x y = (f (x + 1) y + f (x - 1) y + f x (y + 1) + f x (y - 1)) / 4)
    (hg : ∀ x y, g x y = (g (x + 1) y + g (x - 1) y + g x (y + 1) + g x (y - 1)) / 4) :
    ∀ a b, ∀ x y, (a * f x y + b * g x y) = ((a * f (x + 1) y + b * g (x + 1) y) +
      (a * f (x - 1) y + b * g (x - 1) y) + (a * f x (y + 1) + b * g x (y + 1)) +
      (a * f x (y - 1) + b * g x (y - 1))) / 4 := by 
  intro a b x y
  have hfxy : f x y = (f (x + 1) y + f (x - 1) y + f x (y + 1) + f x (y - 1)) / 4 := hf x y
  have hgxy : g x y = (g (x + 1) y + g (x - 1) y + g x (y + 1) + g x (y - 1)) / 4 := hg x y
  calc
    a * f x y + b * g x y = a * ((f (x + 1) y + f (x - 1) y + f x (y + 1) + f x (y - 1)) / 4) + b * ((g (x + 1) y + g (x - 1) y + g x (y + 1) + g x (y - 1)) / 4) := by 
      rw [hfxy, hgxy]
    _ = ( (a * f (x + 1) y + b * g (x + 1) y) + (a * f (x - 1) y + b * g (x - 1) y) + (a * f x (y + 1) + b * g x (y + 1)) + (a * f x (y - 1) + b * g x (y - 1)) ) / 4 := by 
      ring