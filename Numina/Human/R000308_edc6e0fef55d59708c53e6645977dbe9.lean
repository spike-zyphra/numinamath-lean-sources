import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- For each positive integer  $n$  denote:
\[n!=1\cdot 2\cdot 3\dots n\]
Find all positive integers  $n$  for which  $1!+2!+3!+\cdots+n!$  is a perfect square.-/
theorem number_theory_8873 :
  {n : ℕ | 0 < n ∧ IsSquare (∑ i in Finset.Icc 1 n, (i : ℕ)!)} = {1, 3} := by
    ext n
    simp
    constructor <;> intro h
    · -- Let  $a(n)=1!+2!+\hdots+n!$ .
      let a (n : ℕ) := ∑ i ∈ Finset.Icc 1 n, i.factorial
      -- Since  $a(n)\equiv a(4)\equiv 3\pmod 5$  for  $n\geq 4$,  we only need to check  $n\leq 3$ .
      have h1 : ∀ n, 4 ≤ n → a n ≡ 3 [MOD 5] := by
        intro n hn
        generalize h1 : n = k
        revert n
        induction' k with k ih
        · intro _ h1 h2 ; simp [h2] at h1
        · intro n hn nk1
          by_cases n4 : n = 4
          · simp [n4, a, ←nk1,Finset.sum_Icc_succ_top]
            decide
          · simp [a, Finset.sum_Icc_succ_top]
            rw [←nk1]
            have : 5 ≤ n := by omega
            have c1 : n.factorial ≡ 0 [MOD 5] := by
              symm
              exact (Nat.modEq_iff_dvd' (by omega)).2 (by simp; refine dvd_factorial (by omega) this)
            have c2 := ih k (by omega) rfl
            simp [a] at c2
            exact Nat.ModEq.add c2 c1
      have h2 : n < 4 := by
        by_contra tmp
        simp at tmp
        have : IsSquare (a n) := h.2
        obtain ⟨r, hr⟩ := this
        have h2 : r * r ≡ 3 [MOD 5] := hr ▸ h1 n tmp
        rw [Nat.ModEq, ←pow_two,Nat.pow_mod] at h2
        simp at h2
        have : r % 5 < 5 := by refine mod_lt r (by simp)
        interval_cases r % 5 <;> simp at h2
      -- Check all $n < 4$, we find the solutions are  $n=1$  and  $n=3$ .
      interval_cases n <;> simp [Finset.sum_Icc_succ_top] at h
      · simp
      · exfalso
        exact IsSquare.not_prime h (Nat.prime_iff.1 Nat.prime_three)
      · simp
    · -- Verify that $n=1$  and  $n=3$ are actually both solutions.
      rcases h with h | h <;> simp [h, Finset.sum_Icc_succ_top]
      exact ⟨3, by decide⟩
