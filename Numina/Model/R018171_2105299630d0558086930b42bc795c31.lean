import Mathlib

/- Four numbers $w$, $x$, $y$, $z$ satisfy $x-2001=y+2002=z-2003=w+2004$

, then the smallest number is ___          ___ ; the largest number is ___          ___. -/
theorem algebra_2802 {w x y z : ℤ} (h : x - 2001 = y + 2002) (h' : y + 2002 = z - 2003) (h'' : z - 2003 = w + 2004) :
    min (min w x) (min y z) = w ∧ max (max w x) (max y z) = z := by 
  -- Express $x$ and $z$ in terms of $y$
  have h1 : x = y + 4003 := by
    omega
  have h2 : z = y + 4005 := by
    omega
  have h3 : w = y - 2 := by 
    omega
  -- Establish inequalities 
  have hw1 : w < y := by 
    linarith [h3]
  have hw2 : w < x := by
    linarith [h3, h1]
  have hw3 : w < z := by 
    linarith [h3, h2]
  have hx1 : x > y := by 
    linarith [h1]
  have hz1 : z > y := by 
    linarith [h2]
  have hz2 : z > x := by 
    linarith [h1, h2]
  -- Now prove the statements about min and max 
  constructor
  · -- Prove min (min w x) (min y z) = w
    have h_min1 : min w x = w := by 
      apply min_eq_left 
      all_goals 
        omega
    have h_min2 : min y z = y := by 
      apply min_eq_left 
      all_goals 
        omega
    have h_min3 : min w y = w := by 
      apply min_eq_left 
      all_goals 
        omega
    rw [h_min1, h_min2]
    all_goals 
      omega
  · -- Prove max (max w x) (max y z) = z
    have h_max1 : max w x = x := by 
      apply max_eq_right 
      all_goals 
        omega
    have h_max2 : max y z = z := by 
      apply max_eq_right 
      all_goals 
        omega
    have h_max3 : max x z = z := by 
      apply max_eq_right 
      all_goals 
        omega
    rw [h_max1, h_max2]
    all_goals 
      omega