import Mathlib

/- If $m$ and $n$ are positive integers such that $\gcd(m,n) = 12$, then what is the smallest possible value of $\gcd(10m,15n)$? -/
theorem number_theory_16169 :
    IsLeast {x | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.gcd m n = 12 ∧ x = Nat.gcd (10 * m) (15 * n)} 60 := by
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- m = n = 12 satisfies the conditions.
    use 12
    simp
    use 12
    simp
  . -- No smaller value of gcd (10 * m, 15 * n) is possible.
    intro x m mpos n _ h₀ h₁
    have h₂ : 12 ∣ m := by
      rw [h₀.symm]
      apply gcd_dvd_left
    have h₃ : 12 ∣ n := by
      rw [h₀.symm]
      apply gcd_dvd_right
    -- We have 60 ∣ gcd (10m, 15n).
    have h₄ : 60 ∣ x := by
      rw [h₁]
      apply Nat.dvd_gcd
      rw [show 60 = 10 * 6 by norm_num]
      rw [Nat.mul_dvd_mul_iff_left]
      calc
        6 ∣ 12 := by norm_num
        _ ∣ m := by exact h₂
      norm_num
      rw [show 60 = 15 * 4 by norm_num]
      rw [Nat.mul_dvd_mul_iff_left]
      calc
        4 ∣ 12 := by norm_num
        _ ∣ n := by exact h₃
      norm_num
    apply Nat.le_of_dvd
    rw [h₁]
    apply Nat.gcd_pos_of_pos_left
    omega
    exact h₄
