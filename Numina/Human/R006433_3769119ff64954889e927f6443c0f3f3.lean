import Mathlib

/-
Let $P$ be a prime number from the set $\{3, 7, 11, 13, 17, 19\}$. Consider the number $N_0 = 3000003$. Show that there exist digits $d$ (replacing the hundred's place digit, which is 0) and $e$ (replacing the ten-thousand's place digit, which is 0), where $d,e \in \{0, \ldots, 9\}$, such that the number $N_0 + d \cdot 100 + e \cdot 10000$ is divisible by $P$.
-/

theorem number_theory_637023 (P N0 : ℕ) (hP: P ∈ {x:ℕ| x=3 ∨ x=7∨ x=11∨ x=13∨ x=17∨ x =19}) (hN0 : N0 = 3000003):
∃d e : ℕ, d ≤ 9 ∧ e ≤ 9 ∧ P ∣ N0 + d * 100 + e * 10000 := by
  simp at hP
  
  --We simply enumerate every case and give the values of d and e.
  rcases hP with (hP | hP | hP | hP | hP | hP)

  use 0, 0
  simp [hP, hN0]
  norm_num

  use 4, 0
  simp [hP, hN0]
  norm_num

  use 5, 0
  simp [hP, hN0]
  norm_num

  use 8, 0
  simp [hP, hN0]
  norm_num

  use 0, 1
  simp [hP, hN0]
  norm_num

  use 8, 0
  simp [hP, hN0]
  norm_num

