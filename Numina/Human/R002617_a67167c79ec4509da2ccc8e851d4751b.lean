import Mathlib

/- The Dunbar family consists of a mother, a father, and some children. The average age of the members of the family is 
20, the father is 48 years old, and the average age of the mother and children is 16. How many children are in the 
family?
(A) 2 (B) 3 (C) 4 (D) 5 (E) 6-/
theorem algebra_96588 (n : ℕ) (h₁ : 48 + 16*(n+1)= 20 * (n+2) ) :
n = 6 := by {
  -- Simplify the hypothesis h₁.
  ring_nf at h₁
  -- Now we just need to rearrage the equation
  calc n = n * 4 / 4 := by simp
       _ = (n * 20 - n * 16) / 4 := by rw [←Nat.mul_sub]
       _ = (40 + n * 20 - 40 - n * 16) / 4 := by rw [Nat.sub_add_comm,Nat.sub_self, Nat.zero_add]; trivial 
       _ = (64 + n * 16 - 40 - n * 16) / 4 := by rw [←h₁]
       _ = (64 - 40) / 4 := by rw [Nat.sub_add_comm]; simp; trivial
       _ = 6 := by norm_num
}