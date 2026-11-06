import Mathlib

/- $a_{0}=1$ and $a_{n}=2^{a_{n-1}}$ for $n \geq 1$. -/
def a : ℕ → ℕ
| 0 => 1
| n + 1 => 2 ^ a n

/- The recurrence relation -/
lemma a_def (n : ℕ) : a (n + 1) = 2 ^ a n := rfl

/- $2 \leq a_n$ for $n \geq 1$ by induction -/
lemma lemma_1 (n : ℕ) (hn : 1 ≤ n) : 2 ≤ a n := by
  induction n, hn using Nat.le_induction with
  | base => simp [a]
  | succ n hn ih => exact Nat.le_self_pow (Nat.not_eq_zero_of_lt ih) 2

/- $4 \mid a_n$ for $n \geq 2$ by induction -/
lemma lemma_2 (n : ℕ) (hn : 2 ≤ n) : 4 ∣ a n := by
  induction n, hn using Nat.le_induction with
  | base => simp [a]
  | succ n hn ih => exact Nat.pow_dvd_pow_iff_le_right'.mpr (lemma_1 n (Nat.one_le_of_lt hn))

/- $16^k \equiv 6 \pmod{10}$ for $k \geq 1$ by induction -/
lemma lemma_3 (k : ℕ) (hk : 1 ≤ k) : 16 ^ k % 10 = 6 := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih => rw [pow_succ, Nat.mul_mod, ih]

/- 58. A sequence is defined by $a_{0}=1$ and $a_{n}=2^{a_{n-1}}$ for $n \geq 1$. What is the last digit (in base 10) of $a_{15}$ ? -/
theorem number_theory_187953 :
    a 15 % 10 = 6 := by
  -- Let $k$ be the integer such that $a_{14} = 4k$
  rcases lemma_2 14 (by simp) with ⟨k, hk⟩
  -- $1 \leq k$ because $2 \leq a_{14}$
  have hk₂ : 1 ≤ k := by
    have := lemma_1 14 (by simp)
    omega
  -- So $a_{15} = 2^{a_{14}} = 2^{4k} = 16^k ≡ 6 \pmod{10}$
  conv_lhs =>
    left
    rw [a_def, hk, pow_mul,
        show 2 ^ 4 = 16 from rfl]
  rw [lemma_3 k hk₂]
