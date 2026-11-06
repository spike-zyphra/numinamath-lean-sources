import Mathlib

lemma l_dvd_mul_right_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ b * c :=
  Nat.dvd_trans h (Nat.dvd_mul_right _ _)

/- Theorem: Let $k$ be a natural number such that $k \ge 2$. Let $M = 10^k$. For any natural number $n$ such that $n \in [M/4 + 1, M/2]$, show that $n^2 = (M/2 - n)^2 + (n - M/4) \cdot M$. -/
theorem number_thory_635094
  (k : ℕ) (hk : 2 ≤ k)
  (M : ℕ) (hM : M = 10 ^ k)
  (n : ℕ) (hn : M / 4 + 1 ≤ n ∧ n ≤ M / 2)
  : n ^ 2 = (M / 2 - n) ^ 2 + (n - M / 4) * M :=
by
  have : 4 ∣ 2 ^ k := by
    rw [show 2 ^ k = 2 ^ 2 * 2 ^ (k - 2) by
          rw [←pow_add]
          field_simp
       ]
    exact Nat.dvd_mul_right 4 (2 ^ (k - 2))
  have : 4 ∣ M := by
    rw [hM]
    rw [show 10 = 2 * 5 by simp]
    rw [mul_pow]
    exact l_dvd_mul_right_of_dvd this (5 ^ k)
  qify
  rw [Nat.cast_sub, Nat.cast_sub, Nat.cast_div, Nat.cast_div]
  ring_nf
  . assumption
  . simp
  . rw [show 4 = 2 * 2 by simp] at this
    exact dvd_of_mul_right_dvd this
  . simp
  . omega
  . omega
