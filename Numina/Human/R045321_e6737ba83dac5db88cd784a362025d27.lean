import Mathlib

/- PROBLEM: A spider has one sock and one shoe for each of its eight legs. In how many different 
orders can the spider put on its socks and shoes, assuming that, on each leg, the sock must be 
put on before the shoe? -/
theorem combinatorics_95105 : 
  Nat.multinomial {1,2,3,4,5,6,7,8} 2 = Nat.factorial 16 / 2^8 := by {
  rw [Nat.multinomial]
  simp
}