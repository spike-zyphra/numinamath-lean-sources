import Mathlib

/- On pose $n=2021$. Démontrer que le nombre $3^{2 n+1}+2^{n+2}$ est divisible par 35. -/
theorem number_theory_604197 (n : ℕ) (h : n = 2021) :
    35 ∣ 3^(2*n + 1) + 2^(n + 2) := by 

    have fmid : 5 ∣ 3^(2*n + 1) + 2^(n + 2) := by 
      rw [h]
      norm_num
    
    have ftail : 7 ∣ 3^(2*n + 1) + 2^(n + 2) := by 
      rw [h]
      norm_num
        
    have tar : 5*7 ∣ 3^(2*n + 1) + 2^(n + 2) := by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl fmid ftail
    have : 5*7 = 35 := by norm_num
    rw [this] at tar
    assumption
