import Mathlib

theorem algebra_18723 {x y : ℕ} (hxy : x * y = 1000) (hx : ¬10 ∣ x) (hy : ¬10 ∣ y) :
x + y = 133 := by 
  
  --We list the divisors of 1000.
  have d1000: Nat.divisors 1000 = {1,2,4,5,8,10,20,25,40,50,100,125,200,250,500,1000} := by native_decide

  have xd1000 : x ∣ 1000 := by use y; omega

  have xind : x ∈ Nat.divisors 1000 := by simp; exact xd1000
  rw [d1000] at xind
  simp at xind
  
  --By our assumption that x*y = 1000, we have that x is a divisor of 1000. We enumerate the value of x.
  rcases xind with xe | xe | xe | xe | xe | xe | xe | xe | xe | xe | xe | xe | xe | xe | xe | xe

  all_goals
  rw [xe] at hx
  norm_num at hx
  all_goals
  field_simp [xe] at hxy
  omega
  
