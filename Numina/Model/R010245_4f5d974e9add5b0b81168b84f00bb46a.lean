import Mathlib

/--
Define the binary operation a ⋆ b = ab - 2.
-/
def f (a b : ℤ) : ℤ := a * b - 2

/--
Let \( a \star b = ab - 2 \). Then compute:

\[ (((579 \star 569) \star 559) \star \cdots \star 19) \star 9 \mod 100 \]

We prove that the final result is 29.
-/
def L : List ℤ := 
  (List.range' 1 57).map (λ i => (579 : ℤ) - 10 * i)

-- #eval (L.foldl (fun a b => f a b) 579) % 100 

theorem combinatorics_610736 : (L.foldl (fun a b => f a b) 579) % 100 = 29 := by
  native_decide