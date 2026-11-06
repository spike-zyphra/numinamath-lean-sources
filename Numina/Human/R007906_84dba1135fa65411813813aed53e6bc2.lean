import Mathlib

open Finset

/- Determine whether the equation

$$
x^{4}+y^{3}=z !+7
$$

has an infinite number of solutions in positive integers. -/
theorem number_theory_606261 : let S := {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧
x ^ 4 + y ^ 3 = z.factorial + 7}; S.Finite := by
-- Prove the the $z$-coordinate of points in $S$ is less than $13$ by taking mod $13$ on both sides of the equation in question
  intro S; have auxsubs : S ⊆ {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ z < 13 ∧
  x ^ 4 + y ^ 3 < Nat.factorial 13 + 7} := by
    simp [S, Set.subset_def]; intro x y z xpos ypos zpos heq
    have : z < 13 := by
      by_contra!; apply_fun fun t => t % 13 at heq
      replace this : 13 ∣ z.factorial := by apply Nat.dvd_factorial; all_goals omega
      rcases this with ⟨k, hk⟩; rw [hk, Nat.mul_add_mod, Nat.add_mod, Nat.pow_mod] at heq
      nth_rw 2 [Nat.pow_mod] at heq
      have := Nat.mod_lt x (show 13>0 by simp); have := Nat.mod_lt y (show 13>0 by simp)
      interval_cases x % 13 <;> interval_cases y % 13; any_goals norm_num at heq
    split_ands; any_goals assumption
    rw [heq]; gcongr
-- Prove the solution set $S$ is finite by showing it is contained in some product set of finte sets
  have auxfin : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ z < 13 ∧
  x ^ 4 + y ^ 3 < Nat.factorial 13 + 7}.Finite := by
  -- Find the smallest number $t$ such that $t^4$ is larger than $Nat.factorial 13 + 7$
  -- and the smallest number $s$ such that $s^3$ is larger than $Nat.factorial 13 + 7$
    have EX1 : ∃ t, Nat.factorial 13 + 7 < t ^ 4 := by use 1000; simp [Nat.factorial]
    have EX2 : ∃ s, Nat.factorial 13 + 7 < s ^ 3 := by use 2000; simp [Nat.factorial]
    have ht := Nat.find_spec EX1; have letiff := Nat.le_find_iff EX1
    have hs := Nat.find_spec EX2; have lesiff := Nat.le_find_iff EX2
    set t := Nat.find EX1; set s := Nat.find EX2; simp at letiff lesiff
  -- Prove that the solution set is contained in the product set $range (t + 1) ×ˢ range (s + 1) ×ˢ range 13$
    have : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ z < 13 ∧
    x ^ 4 + y ^ 3 < Nat.factorial 13 + 7} ⊆ range (t + 1) ×ˢ range (s + 1) ×ˢ range 13 := by
      simp [Set.subset_def]; intro x y z xpos ypos zpos zlt hxy; split_ands
      · rw [Nat.lt_add_one_iff, letiff]; intros; calc
          _ ≤ x ^ 4 := by apply Nat.pow_le_pow_left; all_goals omega
          _ ≤ _ := by omega
      rw [Nat.lt_add_one_iff, lesiff]; intros; calc
        _ ≤ y ^ 3 := by apply Nat.pow_le_pow_left; all_goals omega
        _ ≤ _ := by omega
      exact zlt
    apply Set.Finite.subset _ this; apply Set.Finite.prod; apply finite_toSet
    apply Set.Finite.prod; apply finite_toSet; apply finite_toSet
-- Finish the finiteness goal by applying Set.Finite.subset
  exact Set.Finite.subset auxfin auxsubs