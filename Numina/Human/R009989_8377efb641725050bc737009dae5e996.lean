import Mathlib

def letter_value (c : Char) : ℤ := match (c.toNat - 'a'.toNat : ℤ) % 8 with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => -1
  | 5 => -2
  | 6 => -1
  | 7 => 0
  | _ => 0

/-The letters of the alphabet are given numeric values based on the two conditions below.

$\bullet$  Only the numeric values of $-2,$ $-1,$ $0,$ $1$ and $2$ are used.

$\bullet$  Starting with A and going through Z, a numeric value is assigned to each letter according to the following pattern: $$
1, 2, 1, 0, -1, -2, -1, 0, 1, 2, 1, 0, -1, -2, -1, 0,\ldots
$$

Two complete cycles of the pattern are shown above. The letter A has a value of $1,$ B has a value of $2,$ F has a value of $-2$ and Z has a value of $2.$ What is the sum of the numeric values of the letters in the word ``numeric''?-/
theorem number_theory_12927 (str : List Char) (hStr: str = ['n', 'u', 'm', 'e', 'r', 'i', 'c']) :
    ∑ (i : Fin str.length), letter_value (str.get i) = -1 := by
  rw [hStr]
  simp
  repeat rw [Fin.sum_univ_succ]; simp
  repeat rw [letter_value]; simp
