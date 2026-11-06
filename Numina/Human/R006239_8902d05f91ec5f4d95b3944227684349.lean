import Mathlib

/-"Let the 11 fixed digits of a UPC-like code be 9, 7, 8, 0, 9, 4, 1, 1, 0, 0, 6. Let $x$ be the $12^{\mathrm{th}}$ value in the code.
Let $S_O$ be the sum of the digits in the odd positions (1st, 3rd, ..., 11th). For the given digits, $S_O = 9+8+9+1+0+6=33$.
Let $S_{E'}$ be the sum of the digits in the even positions excluding the $12^{\mathrm{th}}$ position $x$ (so, 2nd, 4th, ..., 10th).
For the given digits, $S_{E'} = 7+0+4+1+0=12$.
Let $M$ be an integer greater than 1. A generalized code is valid if the sum $N = 3S_O + (S_{E'} + x)$ is divisible by $M$.
We require $x$ to be an integer such that $0 \leq x < M$.
Determine the value of $x$ for which this code will be valid. Show that the answer is $x = (-3S_O - S_{E'}) \pmod M$."
-/

theorem number_theory_635086 (M SO SE x: ℤ) (h2: 0 ≤ x) (h3: x < M) (h4: M ∣ 3 * SO + (SE + x)):
  x = (-3 * SO - SE) % M := by

  apply Int.emod_eq_zero_of_dvd at h4
  rw [show 3 * SO + (SE + x) = x - (- 3 * SO - SE) by ring] at h4
  suffices x % M = (-3 * SO - SE) % M by
    rw [← this]
    symm
    apply Int.emod_eq_of_lt
    omega
    omega
  rw [show x = x - (-3 * SO - SE) + (-3 * SO - SE) by ring]
  rw [Int.add_emod]
  rw [h4]
  simp