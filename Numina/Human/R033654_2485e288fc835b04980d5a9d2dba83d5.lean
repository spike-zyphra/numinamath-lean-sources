import Mathlib

/-The greatest common divisor of two integers is $(x+2)$ and their least common multiple is $x(x+2)$, where $x$ is a positive integer. If one of the integers is 24, what is the smallest possible value of the other one?-/
theorem number_theory_16288  :
  IsLeast {b | ∃ x, 0 < x ∧ (24).gcd b = x + 2 ∧ (24).lcm b = x * (x + 2)} 6 := by 
    constructor 
    · -- verify that 6 satisfy the condition.
      use 4
      norm_num 
    · intro a ha 
      simp at ha 
      obtain ⟨x, hx⟩ := ha 
      -- We know that $\gcd(m,n) \cdot \mathop{\text{lcm}}[m,n] = mn$ for all positive integers $m$ and $n$.  Hence, we get that (x + 2) * (x * (x + 2)) = 24 * a.
      have c1 := Nat.gcd_mul_lcm 24 a 
      simp [hx] at c1 
      -- because 24 ∣ (x + 2) * (x * (x + 2)), we have 4 ≤ x.
      have xge4 : 4 ≤ x := by 
        replace c1 : 24 ∣ (x + 2) * (x * (x + 2)) := Dvd.intro a (id (Eq.symm c1))
        contrapose! c1 
        interval_cases x <;> tauto
      -- when 4 ≤ x, 6 ≤ b.
      calc 
        6 = (4 + 2) * (4 * (4 + 2)) / 24 := by simp  
        _ ≤ (x + 2) * (x * (x + 2)) / 24 := by 
          apply Nat.div_le_div _ (by simp) (by simp)
          nlinarith
        _ = _ := (Nat.eq_div_of_mul_eq_right (by omega) c1.symm).symm 

