import Mathlib

/- minStep of Hanoi Tower n -/
def TowerOfHanoi_minSteps_eq_additionalMoves (n : ℕ) : ℕ := match n with
| 0 => 0
| n+1 => (TowerOfHanoi_minSteps_eq_additionalMoves n) + 1 + (TowerOfHanoi_minSteps_eq_additionalMoves n)

/- The Tower of Hanoi is a classic puzzle that became popular in the late nineteenth century. It consists of three pegs and eight rings of different sizes, arranged in order of size with the largest ring at the bottom, on one of the pegs. The objective of the puzzle is to move all the rings from the first peg to the second peg, one at a time, without ever placing a larger ring on top of a smaller ring. The third peg is available for use as an auxiliary peg.
a) We need to use mathematical induction to prove that the minimum number of moves required to transfer \( n \) rings from one peg to another is \( 2^{n} - 1 \). -/
theorem number_theory_4584_1 (n : ℕ) : (TowerOfHanoi_minSteps_eq_additionalMoves n)=2^n-1 := by
  induction n
  simp
  dsimp [TowerOfHanoi_minSteps_eq_additionalMoves]
  rename_i n hn
  -- use induction
  unfold TowerOfHanoi_minSteps_eq_additionalMoves
  rw [hn]
  -- prove 2^n>=1
  have h1:= @Nat.one_le_two_pow n
  rw [ Nat.sub_add_cancel h1]
  -- prove 2^n+2^n-1=2^(n+1)-1
  rw [pow_succ]
  rw [mul_comm,two_mul]
  rw [Nat.add_sub_assoc]
  exact h1


theorem number_theory_4584_2 : 
 (TowerOfHanoi_minSteps_eq_additionalMoves 64) = 18446744073709551615 := by native_decide