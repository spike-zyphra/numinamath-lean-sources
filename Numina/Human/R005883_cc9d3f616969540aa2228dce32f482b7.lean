import Mathlib
/-The English alphabet, which has 26 letters, is randomly permuted. Let $p_{1}$ be the probability that $\mathrm{AB}, \mathrm{CD}$, and EF all appear as contiguous substrings. Let $p_{2}$ be the probability that ABC and DEF both appear as contiguous substrings. Compute $\frac{p_{1}}{p_{2}}$.
-/

namespace PermutationProbability

/-!
### Favorable Outcomes for $p_1$

To calculate the number of permutations for $p_1$, we treat each required
substring as a single block.
- Block 1: "AB"
- Block 2: "CD"
- Block 3: "EF"

These 3 blocks involve 6 distinct letters. The remaining $26 - 6 = 20$ letters
are permuted along with the 3 blocks.
The total number of items to permute is $20 + 3 = 23$.
The number of such permutations is $23!$.
-/
def num_favorable_p1 : ℕ := Nat.factorial (26 - 6 + 3)

/-!
### Favorable Outcomes for $p_2$

Similarly, for $p_2$, we treat "ABC" and "DEF" as blocks.
- Block 1: "ABC"
- Block 2: "DEF"

These 2 blocks also involve 6 distinct letters. The remaining $26 - 6 = 20$
letters are permuted along with the 2 blocks.
The total number of items to permute is $20 + 2 = 22$.
The number of such permutations is $22!$.
-/
def num_favorable_p2 : ℕ := Nat.factorial (26 - 6 + 2)

theorem combinatorics_610494 :
    (num_favorable_p1 : ℝ) / (num_favorable_p2 : ℝ) = 23 := by
  simp only [num_favorable_p1, num_favorable_p2]
  norm_num
  rw [Nat.factorial_succ 22]
  rw [Nat.cast_mul]
  have h_denom_ne_zero : ((Nat.factorial 22) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 22)
  field_simp
  norm_num

end PermutationProbability
