import Mathlib

/- When counting from 3 to 201, 33 is the 51st number counted. When counting backwards from 201 to 3, 53 is the nth number counted. What is n?
(A) 146(B) 147(C) 148(D) 149(E) 150(A) 146(B) 147(C) 148(D) 149(E) 150 -/

theorem combinatorics_94512 (f : ℕ → ℤ) (h₁ : f 1 = 201) (hr : ∀ a, f (a + 1) = f a - 1) (hn : f n = 53) (hn' : n > 0) :
n = 149 := by 
  -- Note: the function f acts as a sequence to model the process of counting
  have f_formula : ∀ a > 0, f a = 202 - a := by
    -- We find a formula for f
    intro a ha
    -- Use induction starting at n=1
    induction a, ha using Nat.le_induction with
    | base => 
      rw [h₁]
      ring
    | succ b hb ih => 
      rw [hr, ih, Nat.cast_add, Nat.cast_one, sub_sub]
  -- Have a linear equation for n
  have : (202 : ℤ) - ↑n = 53 := by
    calc
      202 - ↑n = f n := symm (f_formula n hn')
      _ = 53 := hn
  linarith