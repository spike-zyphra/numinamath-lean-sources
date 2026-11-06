import Mathlib

theorem algebra_169606 (margit_age : ℕ) (h : margit_age > 0) (mother_age grandmother_age : ℕ)
    (h_mother : mother_age = 30) (h_grandmother : grandmother_age = 62) (x : ℕ)
    (hx : x > 0) (h_mother_in_x : mother_age + x = 4 * (margit_age + x)) (h_grandmother_in_x : grandmother_age + x = 8 * (margit_age + x)) :
    margit_age = 6 := by 
  subst h_mother
  subst h_grandmother
  omega