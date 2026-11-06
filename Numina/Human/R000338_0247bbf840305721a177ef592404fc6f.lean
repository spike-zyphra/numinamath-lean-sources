import Mathlib

/-
Problem

Given vectors $∘verrightarrow{a}=(4,2)$ and $\overrightarrow{b}=(m,3)$, if there exists a real number $\lambda$ such that $\overrightarrow{a}=\lambda\overrightarrow{b}$, then the value of the real number $m$ is ______.
-/

/-
Solution

To find the value of $m$ given that $∘verrightarrow{a} = \lambda\overrightarrow{b}$, we start by equating the given vectors:

Given: $\overrightarrow{a} = (4,2)$ and $\overrightarrow{b} = (m,3)$, and $\overrightarrow{a}=\lambda\overrightarrow{b}$ implies:

1. Equate the vectors component-wise:
   $$\left(4,2\right) = \left(m\lambda, 3\lambda\right)$$
      
      This gives us two equations based on the components of the vectors:

      2. From the first component:
         $$m\lambda = 4$$
            
            3. From the second component:
               $$3\lambda = 2$$
                  
                  4. Solve for $\lambda$ from the second equation:
                     $$\lambda = \frac{2}{3}$$
                        
                        5. Substitute the value of $\lambda$ into the first equation to find $m$:
                           $$m \cdot \frac{2}{3} = 4$$
                              Solving for $m$ gives:
                                 $$m = 4 \cdot \frac{3}{2}$$
                                    $$m = \frac{12}{2}$$
                                       $$m = 6$$

                                       Therefore, the value of the real number $m$ is $\boxed{6}$.
-/

theorem algebra_8975 (m : ℝ) (h : ∃ s, ((4 : ℝ), (2 : ℝ)) = (s * m, s * (3 : ℝ))) : m = 6 := by
  obtain ⟨s, seq⟩ := h
  -- get equation of first component
  obtain fst : 4 = s * m := by aesop
  -- get equation of second component
  obtain snd : 2 = s * 3 := by aesop
  -- to divide $s$ in sequential steps
  have sneq0 : s ≠ 0 := by
    intro seq0
    rw [seq0] at snd
    aesop
  -- divide $s$ since $s \neq 0$
  have by_fst : m = 4 / s := by 
    apply_fun (· / s) at fst
    rw [fst]
    aesop
  -- divide $s$ since $s \neq 0$
  have by_snd : s = 2 / 3 := by
    apply_fun (· / 3) at snd
    rw [snd]
    exact Eq.symm (mul_div_cancel_of_invertible s 3)
  rw [by_fst, by_snd]
  linarith