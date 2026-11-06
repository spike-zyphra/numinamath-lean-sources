import Mathlib

open Finset Nat

/-!
Let $a_0$ be a non-negative integer and $d, k$ be positive integers such that $k$ is odd.
Let $S$ be the sum of an arithmetic progression with $k$ terms, starting term $a_0$,
and common difference $d$.

This theorem proves that the remainder when $S$ is divided by $kd$ is $k \cdot (a_0 \pmod d)$.
-/
theorem ap_sum_modulo (a0 d k : ℕ) (hd : d > 0) (hk : k > 0) (hk : k % 2 = 1) :
  let S := ∑ j in range k, (a0 + j * d)
  S % (k * d) = k * (a0 % d) := by

  let S := ∑ j in range k, (a0 + j * d)

  -- 1) closed form for S
  have h_sum : S = k * a0 + d * (k * (k - 1) / 2)  := by
    calc S
      = ∑ j in range k, (a0 + j * d) := rfl

        -- split the sum into two sums
      _ = ∑ j in range k, a0 + ∑ j in range k, (j * d) := by
        simp [sum_add_distrib]

        -- use the fact that `∑ j in range k, j = k * (k - 1) / 2`
      _ = k * a0 + d * (∑ j in range k, j) := by
        simp [sum_add_distrib, sum_const, card_range]
        rw [mul_comm d, Finset.sum_mul]

        -- use the fact that `∑ j in range k, j = k * (k - 1) / 2`
      _ = k * a0 + d * (k * (k - 1) / 2) := by
        simp [sum_range_id]

  -- 2) reduce mod (k * d), dropping the `d * _` term
  have h_dvd : 2 ∣ k - 1 := Nat.dvd_of_mod_eq_zero (by omega)

  -- 2.1) rearrange the term `d * (k * (k - 1) / 2)` to show it's a multiple of `k * d`
  have h_mul_dvd :  d * (k * (k - 1) / 2) = (k * d) * ((k - 1) / 2) := by
      rw [Nat.mul_div_assoc k h_dvd]
      ring

  -- 2.2) show that `d * (k * (k - 1) / 2)` is a multiple of `k * d`
  have h_mod_zero : d * (k * (k - 1) / 2) % (k * d) = 0 := by
    rw [h_mul_dvd]
    -- prove that `k * d` divides `k * d * ((k - 1) / 2)` by `Nat.dvd_mul_right`
    have: k * d ∣ k * d * ((k - 1) / 2) := by
      exact Nat.dvd_mul_right (k * d) ((k - 1) / 2)
    exact Nat.mod_eq_zero_of_dvd this

  -- 2.3) show that `S % (k * d) = (k * a0) % (k * d)`
  have h_mod : S % (k * d) = (k * a0) % (k * d) := by
    rw [h_sum]
    calc
      _ = (((k - 1) / 2) *(k * d) + k * a0) % (k * d) := by rw [h_mul_dvd]; ring_nf
      _ = (k * a0) % (k * d) := by apply Nat.mul_add_mod'


  -- 3) decompose `k * a0` via `div_add_mod` and finish
  have mul_mod_mul_self:  ∀(n a d : ℕ), (hd : d > 0)-> (hn : n > 0)->
  (n * a) % (n * d) = n * (a % d) := by
  -- Let a = q*d + r, where q = a/d and r = a%d.
  -- The definition of a % d and a / d gives a = d * (a / d) + a % d.

    intro n a d hd hn
    have h_mod_add_div : a = d * (a / d) + a % d := by exact Eq.symm (div_add_mod a d)
    calc
      _ = (n * (d * (a / d) + a % d)) % (n * d) := by nth_rw 1 [h_mod_add_div]
      _ = ((a / d) * (n * d) + n * (a % d)) % (n * d) := by ring_nf
      _ = (n * (a % d)) % (n * d) := by apply Nat.mul_add_mod'
      _ = n * (a % d) := by
        refine mod_eq_of_lt ?_
        gcongr
        exact Nat.mod_lt a hd

  -- 4) apply the lemma to show that `S % (k * d) = k * (a0 % d)`
  have h_key : (k * a0) % (k * d) = k * (a0 % d) := mul_mod_mul_self k a0 d (by positivity) (by positivity)
  have h_goal : S % (k * d) = k * (a0 % d) := by
    rw [h_mod, h_key]
  exact h_goal
  