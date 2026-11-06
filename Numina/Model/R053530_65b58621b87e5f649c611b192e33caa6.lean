import Mathlib

/- Given that $k$ is a positive odd number less than $500$, if $5k^{2}+6k+1$ is divisible by $4$, find the number of possible values of $k$.

 -/
theorem number_theory_6257 :
    Set.ncard {k : ℕ | Odd k ∧ k < 500 ∧ 4 ∣ (5 * k ^ 2 + 6 * k + 1)} = 250 := by
  have h2 : {k : ℕ | Odd k ∧ k < 500 ∧ 4 ∣ (5 * k ^ 2 + 6 * k + 1)} = Finset.filter (fun k => Odd k ∧ k < 500 ∧ 4 ∣ (5 * k ^ 2 + 6 * k + 1)) (Finset.Icc 0 499) := by
    ext k
    simp
    <;> omega
  rw [h2]
  rw [Set.ncard_coe_Finset]
  native_decide