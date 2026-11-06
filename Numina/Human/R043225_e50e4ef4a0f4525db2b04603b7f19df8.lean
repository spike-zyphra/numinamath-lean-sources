import Mathlib

def f' : ℕ → ℕ
| 0 => 1
| n + 1 => if Even n then (f' n) + 1 else (f' n) * 2

/- The sequence 1, 2, 4, 5, 10, 11, 22, 23, 46, 47, $\dots$ is formed as follows:

$\bullet$ Start with the number 1.

$\bullet$ Add one to get 2.

$\bullet$ Double that to get 4.

$\bullet$ Add one to get 5.

$\bullet$ Double that to get 10, and so on.

We repeat the steps of "add one" and "double that", alternating between them.

The 100th term will be of the form $3 \cdot 2^k - 1.$  Compute $k.$ -/
theorem algebra_20871 : f' 99 = 3 * 2 ^ k - 1 ↔ k = 49 := by
  -- Find the general term.
  have h (k : ℕ) : f' (2 * k + 1) = 3 * 2 ^ k - 1 := by
    induction k with
    | zero =>
      rw [f', f']
      simp
    | succ k hk =>
      rw [f']
      simp
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring_nf, f']
      simp
      rw [hk, <-@Nat.add_right_cancel_iff ((3 * 2 ^ k - 1) * 2 + 1) (3 * 2 ^ (k + 1) - 1) 1, Nat.sub_add_cancel, Nat.mul_sub_right_distrib, mul_two 1, Nat.add_assoc, Nat.sub_add_cancel]
      ring_nf
      simp
      linarith only [show 2 ^ k ≥ 1 by apply Nat.one_le_pow; norm_num]
      linarith only [show 2 ^ (k + 1) ≥ 1 by apply Nat.one_le_pow; norm_num]
  -- Break the iff into two implications.
  apply Iff.intro
  . rw [h 49]
    intro h'
    replace h' : 3 * 2 ^ 49 = 3 * 2 ^ k := by
      omega
    rw [Nat.mul_right_inj] at h'
    apply Nat.pow_right_injective at h'
    exact h'.symm
    rfl
    norm_num
  . intro hk
    subst hk
    exact h 49
