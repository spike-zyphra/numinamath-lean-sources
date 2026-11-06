import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- For a positive integer $n$, let $S\left( n \right)$ represent the sum of its digits. If the difference between $S\left( n \right)$ and $S\left( n+1 \right)$ is greater than $2018$, then the minimum number of digits of $n$ is ___          ___. -/
theorem number_theory_7201 (n : ℕ) (h₀ : 0 < n) (h₁ : (Nat.digits 10 n).sum - (Nat.digits 10 (n + 1)).sum > 2018) :
    (Nat.digits 10 n).length ≥ 225 := by 
  by_contra h 
  push_neg at h 
  have h2 : (Nat.digits 10 n).length ≤ 224 := by
    omega 
  have h3 : (Nat.digits 10 n).sum - (Nat.digits 10 (n + 1)).sum ≤ 2016 := by
    have h4 : (Nat.digits 10 n).sum ≤ 2016 := by
      have h7 : (Nat.digits 10 n).length ≤ 224 := h2
      have h9 : (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length * 9 := by 
        have h10 : ∀ x ∈ (Nat.digits 10 n), x ≤ 9 := by
          intro x hx 
          have : x < 10 := by 
            exact Nat.digits_lt_base (by norm_num) hx
          omega
        have h13 : (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length * 9 := by 
          have : (Nat.digits 10 n).sum ≤ (List.length (Nat.digits 10 n)) * 9 := by
            apply List.sum_le_card_nsmul 
            all_goals 
            intro x hx 
            specialize h10 x hx 
            simpa using h10 
          simp [show List.length (Nat.digits 10 n) = (Nat.digits 10 n).length by simp] at this ⊢ 
          all_goals linarith 
        linarith
      omega 
    have h5 : (Nat.digits 10 (n + 1)).sum ≥ 0 := by 
      omega
    omega 
  omega