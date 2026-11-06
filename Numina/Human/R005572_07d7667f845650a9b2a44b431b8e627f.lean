import Mathlib

/-
Joe has written 5 questions of different difficulties for a test with problems numbered 1 though 5 . He wants to make sure that problem $i$ is harder than problem $j$ whenever $i-j \geq 3$. In how many ways can he order the problems for his test?
-/
theorem combinatorics_608914 : 
    ({p : Equiv.Perm (Fin 5) | ∀ i j, i.val - j.val ≥ 3 → p i ≥ p j} : Finset _).card = 25 := by 
  decide