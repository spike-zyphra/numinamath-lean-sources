import Mathlib

def seq : ℕ → ℤ
| 0 => 3
| n + 1 => seq n + 4

theorem algebra_113749 :
    seq 1 = 7 ∧ seq 2 = 11 ∧ seq 3 = 15 ∧
    2015 ∈ Set.range seq ∧
    ∑ i in Finset.range 100, seq i = 20100 := by
  constructor
  · -- Show that seq 1 = 7
    rfl

  constructor
  · -- Show that seq 2 = 11
    rfl

  constructor
  · -- Show that seq 3 = 15
    rfl

  constructor
  · -- Show 2015 is in the range of seq
    use 503
    native_decide

  · -- Show the sum of the first 100 terms is 20100
    native_decide