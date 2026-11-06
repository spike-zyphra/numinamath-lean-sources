import Mathlib 

/-Let $x, y \in \mathbb{R}$ be such that $x=y(3-y)^{2}$ and $y=x(3-x)^{2}$. Find all possible values of $x+y$.-/
theorem algebra_604568 {x y : ℝ} (h1 : x = y * (3 - y)^2) (h2 : y = x * (3 -x)^2 ) : 
  x + y = 0 ∨ x + y = 3 ∨ x + y = 4 ∨ x + y = 5 ∨ x + y = 8 := by 
    by_cases xeqy : x = y 
    · -- A pair $(x, x) \in \mathbb{R}^{2}$ satisfies the equations if and only if $x=x(3-x)^{2}$, and it is easy to see that this cubic equation has the solution set $\{0,2,4\}$. 
      simp [xeqy] at h1 ⊢
      have : y = 0 ∨ y = 2 ∨ y = 4 := by 
        by_cases y0 : y = 0 
        · tauto 
        · have : (3 - y)^2 = 1 := by 
            nth_rw 1 [← mul_one y] at h1
            rw [mul_eq_mul_left_iff] at h1
            tauto
          right
          simp at this
          rcases this with h1 | h1 
          · left; linarith
          · right; linarith 
      -- These pairs give us 0, 4, and 8 as possible values for $x+y$.
      rcases this with h | h | h <;> norm_num [h] 
    · -- Assuming $x \neq y$ let $s$ be the sum $x+y$ and $p$ be the product $x y$. 
      let s := x + y 
      let p := x * y 
      -- Subtracting the first equation from the second and cancelling out the term $x-y$ we get
      -- $$
      -- p=s^{2}-6 s+10 \text {. }
      -- $$
      have c1 : p = s^2 - 6 * s + 10 := by 
        have : x - y ≠ 0 := sub_ne_zero.2 xeqy
        suffices (x - y) * p = (x - y) * (s^2 - 6 * s + 10) by 
          simp at this
          tauto
        simp only [p, s]
        nlinarith
      -- Adding the two equations gives
      -- $$
      -- 0=s\left(s^{2}-3 p\right)-6\left(s^{2}-2 p\right)+8 s .
      -- $$
      have c2 : s * (s^2 - 3*p) - 6*(s^2 - 2*p) + 8 * s = 0 := by 
        simp only [p,s]; nlinarith
      -- Together the equations give
      -- $$
      -- 0=s^{3}-12 s^{2}+47 s-60=(s-3)(s-4)(s-5) \text {. }
      -- $$
      have : (s - 3) * (s - 4) * (s - 5) = 0 := by nlinarith
      simp [mul_eq_zero] at this
      simp only [s, sub_eq_zero] at this 
      rcases this with (h | h) | h <;> norm_num [h]
      