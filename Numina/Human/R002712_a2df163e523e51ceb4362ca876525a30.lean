import Mathlib

open Finset

/- Determine the number of integers $n$ such that $1 \leqslant n \leqslant 10^{10}$, and such that for all $k=1,2, \ldots, 10$, the integer $n$ is divisible by $k$. -/
theorem number_theory_103047 :
    #{n ∈ Icc 1 (10 ^ 10) | ∀ k ∈ Icc 1 10, k ∣ n} = 3968253 := by
  -- ∀ k ∈ [1, 10], k ∣ n ↔ [1, 10].lcm ∣ n
  simp [← Finset.lcm_dvd_iff, -mem_Icc]
  -- Compute the lcm of [1, 10] to be 2520
  rw [show (Icc 1 10).lcm (fun b => b) = 2520 by native_decide]
  -- Show that the function (n + 1) * 2520 is a bijection between [0, 3968253) and the required set
  -- All prolems are linear, so we can use `omega` to solve them
  apply Finset.card_eq_of_bijective (fun n _ => (n + 1) * 2520)
  . simp
    rintro n hn₁ hn₂ ⟨m, rfl⟩
    use m - 1
    omega
  . intro i hi
    simp
    omega
  . intro i j hi hj hij
    simpa using hij
