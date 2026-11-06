import Mathlib

open Finset

theorem algebra_323504 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (f : ℕ → ℕ → ℕ) (h1 : ∀ x, f x 1 = x) (h2 : ∀ x y, f x (y + 1) = f x y + x) :
    f (a + b) c = f a c + f b c := by 
  have h3 : ∀ x c : ℕ, f x c = x * c := by 
    intro x c
    have h4 : ∀ (c : ℕ), f x c = x * c := by 
      intro c
      induction c with 
      | zero =>
        -- Base case: prove that f x 0 = x * 0
        have h5 : f x 0 = 0 := by 
          have h2' := h2 x 0 
          have h1' := h1 x 
          simp at h2' h1' 
          omega 
        simp [h5, Nat.mul_zero]
      | succ c ih =>
        -- Inductive step: prove that f x (c + 1) = x * (c + 1)
        have h4' : f x (c + 1) = f x c + x := by 
          specialize h2 x c 
          simpa using h2 
        rw [h4']
        rw [ih]
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        <;> ring 
    exact_mod_cast h4 c 
  have h4 : f (a + b) c = (a + b) * c := by 
    specialize h3 (a + b) c 
    simpa using h3 
  have h5 : f a c = a * c := by 
    specialize h3 a c 
    simpa using h3 
  have h6 : f b c = b * c := by 
    specialize h3 b c 
    simpa using h3 
  rw [h4, h5, h6]
  all_goals ring