import Mathlib

/-Find the units digit of $1! + 2! + 3! + 4! + \ldots + 50!$.-/
theorem number_theory_23062 : (∑ i in Finset.Icc 1 50, Nat.factorial i) % 10 = 3 := by
  -- show that Nat.facterial n % 10 = 0 (when n ≥ 5)
  have factorial₀ (n : ℕ) : Nat.factorial (5 + n) % 10 = 0 := by
    -- show that 5! ∣ n!
    have dvd5 : Nat.factorial 5 ∣ Nat.factorial (5 + n) := by
      apply Nat.factorial_dvd_factorial
      linarith only
    -- show that 10 ∣ 5!
    have dvd10 : 10 ∣ Nat.factorial 5 := by simp [Nat.factorial]; norm_num
    apply Nat.dvd_trans at dvd10
    apply dvd10 at dvd5
    -- show that Nat.factorial n % 10 = 0
    apply Nat.mod_eq_zero_of_dvd
    exact dvd5

  -- simplify the desired expression
  rw [Finset.sum_nat_mod]
  calc
    (∑ i in Finset.Icc 1 50, Nat.factorial i % 10) % 10 = (∑ i in Finset.Ico 1 51, Nat.factorial i % 10) % 10 := by
      congr
    _ = (∑ i in Finset.range 50, Nat.factorial (i + 1) % 10) % 10 := by
      congr 1
    -- split into Finset.range 4 and Finset.range 46
    _ = (∑ i in Finset.range 4, Nat.factorial (i + 1) % 10 + ∑ i in Finset.range 46, Nat.factorial (4 + i + 1) % 10) % 10 := by rw [<-Finset.sum_range_add]
    _ = (∑ i in Finset.range 4, Nat.factorial (i + 1) % 10 + ∑ i in Finset.range 46, Nat.factorial (5 + i) % 10) % 10 := by congr; ring_nf
    _ = (∑ i in Finset.range 4, Nat.factorial (i + 1) % 10 + ∑ i in Finset.range 46, 0) % 10 := by congr; ext n; rw [factorial₀]
    _ = (∑ i in Finset.range 4, Nat.factorial (i + 1) % 10 + 0) % 10 := by ring_nf
    _ = (1 % 10 + 2 % 10 + 6 % 10 + 24 % 10 + 0) % 10 := by simp [Finset.sum, Nat.factorial]
    _ = 3 := by norm_num