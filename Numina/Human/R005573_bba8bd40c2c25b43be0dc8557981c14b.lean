import Mathlib

open Finset

/-
Tac is dressing his cat to go outside. He has four indistinguishable socks, four indistinguishable shoes, and 4 indistinguishable show-shoes. In a hurry, Tac randomly pulls pieces of clothing out of a door and tries to put them on a random one of his cat's legs; however, Tac never tries to put more than one of each type of clothing on each leg of his cat. What is the probability that, after Tac is done, the snow-shoe on each of his cat's legs is on top of the shoe, which is on top of the sock?
-/
theorem combinatorics_608915 :
    (card {f : Fin 4 → Equiv.Perm (Fin 3) | ∀ i,
    (f i) 0 < (f i) 1 ∧ (f i) 1 < (f i) 2}) / (6^4 : ℚ) = 1/1296 := by

  -- Prove that the number of valid permutations (strictly increasing) for each leg is exactly 1
  have h₁ : (card {f : Fin 4 → Equiv.Perm (Fin 3) | ∀ i, (f i) 0 < (f i) 1 ∧ (f i) 1 < (f i) 2}) = 1 := by
    native_decide

  -- Replace the numerator with 1 using the proven lemma
  rw [h₁]
  
  -- Simplify the denominator and verify the final equality
  norm_num 
  [Fin.forall_fin_succ, Equiv.Perm.sign_mul, Equiv.Perm.mul_apply, Fin.val_zero, Fin.val_succ,
   Fin.ext_iff, Equiv.Perm.sign_symm, Equiv.Perm.sign_swap, Nat.cast_add, Nat.cast_one, Nat.cast_mul]