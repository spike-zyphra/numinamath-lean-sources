import Mathlib
/-For a given positive integer $n > 2^3$, what is the greatest common divisor of $n^3 + 3^2$ and $n + 2$?-/
theorem number_theory_11500 (n : ℕ) (hn : n > 2^3) :
    Nat.gcd (n^3 + 3^2) (n + 2) = 1 := by
  -- because we wish to solve for the gcd of two numbers, we will use a method like the Euclidean one, to eliminate one of them and get a normal number
  refine Eq.symm (Nat.gcd_greatest (Nat.one_dvd (n ^ 3 + 3 ^ 2)) (Nat.one_dvd (n + 2)) ?hd)
  intro e h₁ h₂
  -- first we get rid of the n^3 term
  have : e ∣ n ^ 2 * (n + 2) := Dvd.dvd.mul_left h₂ (n ^ 2)
  have sec : e ∣ (n ^ 2 * (n + 2) - (n ^ 3 + 3 ^ 2)) := Nat.dvd_sub' this h₁
  have : n ^ 2 * (n + 2) - (n ^ 3 + 3 ^ 2) = 2 * n ^ 2 - 9 := by
    refine (Nat.sub_eq_iff_eq_add ?h).mpr ?_
    nlinarith
    have : n ^ 2 * (n + 2) = n ^ 3 + 2 * n ^ 2 := by ring
    rw [this]
    have : 2 * n ^ 2 - 9 + (n ^ 3 + 3 ^ 2) = 2 * n ^ 2 + (n ^ 3 + 3 ^ 2) - 9 := by
      symm
      refine Nat.sub_add_comm ?h
      nlinarith
    rw [this]
    have : 2 * n ^ 2 + (n ^ 3 + 3 ^ 2) - 9 = 2 * n ^ 2 + n ^ 3 + 3 ^ 2 - 9 := by ring_nf
    rw [this]; simp only [Nat.reducePow, add_tsub_cancel_right]; rw [add_comm]
  rw [this] at sec
  -- then the n^2 term
  have r : (2 * n ^ 2 - 9) ≤ 2 * n * (n + 2) := by apply Nat.sub_le_of_le_add; nlinarith
  have sec : e ∣ (2 * n * (n + 2) - (2 * n ^ 2 - 9)) := by refine Nat.dvd_sub r (Dvd.dvd.mul_left h₂ (2 * n)) sec
  have : 2 * n * (n + 2) - (2 * n ^ 2 - 9) = 4 * n + 9 := by
    refine (Nat.sub_eq_iff_eq_add r).mpr ?_
    have j : 4 * n + 9 + (2 * n ^ 2 - 9) = (2 * n ^ 2 - 9 + 9) + 4 * n := by ring
    have : 2 * n ^ 2 - 9 + 9 = 2 * n ^ 2 := by
      apply Nat.sub_add_cancel
      nlinarith
    rw [j, this]; ring
  rw [this] at sec
  -- eliminate all n on one side and we get an 1, closing the discussion
  have sec : e ∣ ((4 * n + 9) - 4 * (n + 2)) := by
    refine Nat.dvd_sub ?H sec ?h₂
    linarith
    exact Dvd.dvd.mul_left h₂ 4
  have : (4 * n + 9) - 4 * (n + 2) = 1 := Eq.symm (Nat.eq_sub_of_add_eq' rfl)
  rw [this] at sec; exact sec