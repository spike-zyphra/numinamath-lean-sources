import Mathlib

def f : ℕ → ℕ
| 0 => 1
| n + 1 => Nat.lcm (f n) (n + 1)

theorem number_theory_262362 :
    Set.ncard {x | ∃ n, x = f n ∧ n < 100} = 36 := by
  have h1 : {x | ∃ n, x = f n ∧ n < 100} = Finset.image f (Finset.Iio (100 : ℕ)) := by
    ext x
    simp
    <;> aesop
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide