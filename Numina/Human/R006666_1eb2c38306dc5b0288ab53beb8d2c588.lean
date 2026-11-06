import Mathlib

-- we show that for n % 10 = 7, the index of mod 100 is 20
lemma lemma_1 (n: ℕ): (10 * n + 7) ^ 20 % 100 = 1 := by
  set q:= n / 10
  set r:= n % 10
  have h: n = 10 * q + r := by
    omega
  have lr: r < 10 := by omega
  rw [h]
  clear h
  clear_value q r
  rw [show 10 * (10 * q + r) + 7 = 10 * r + 7 + 100 * q by ring]
  rw [Nat.pow_mod]
  rw [show (10 * r + 7 + 100 * q) % 100 = (10 * r + 7) % 100 by
    rw [Nat.add_mod]
    simp]
  interval_cases r
  all_goals norm_num


/-Let $k$ be a non-negative integer, and let $N = 10k+7$.
Determine the last two digits of $N^N$, written in base 10.
Show that these last two digits are given by the $(k \pmod{10})$-th term (0-indexed) of the sequence
$[43, 77, 3, 17, 63, 57, 23, 97, 83, 37]$.-/

theorem number_theory_639854 (k N: ℕ) (h: N = 10 * k + 7): N ^ N % 100 =
  match k % 10 with
  | 0 => 43
  | 1 => 77
  | 2 => 3
  | 3 => 17
  | 4 => 63
  | 5 => 57
  | 6 => 23
  | 7 => 97
  | 8 => 83
  | 9 => 37
  | _ => 0 := by

    rw [h]
    clear h

    -- prove by induction on k
    induction' k using Nat.strongRecOn with k ih
    by_cases l: k ≤ 9
    .
      interval_cases k
      all_goals simp
    .
      simp at l
      specialize ih (k - 10) (by omega)
      have u: k % 10 = (k - 10) % 10 := by
        nth_rewrite 1 [show k = k - 10 + 10 by omega]
        rw [Nat.add_mod]
        simp
      rw [u]
      clear u
      suffices (10 * k + 7) ^ (10 * k + 7) % 100 =
        (10 * (k - 10) + 7) ^ (10 * (k - 10) + 7) % 100 by
        rw [this]
        exact ih
      clear ih
      set n:= k - 10
      rw [show k = n + 10 by omega]
      clear_value n
      nth_rewrite 1 [Nat.pow_mod]
      have v: (10 * (n + 10) + 7) % 100 = (10 * n + 7) % 100 := by
        rw [show 10 * (n + 10) + 7 = (10 * n + 7) + 100 by ring]
        rw [Nat.add_mod]
        simp
      rw [v]
      clear v
      rw [show 10 * (n + 10) + 7 = 10 * n + 7 + 100 by ring]
      set p:= 10 * n + 7
      have i: (p % 100) ^ (p + 100) % 100 = (p ^ p % 100 * p ^ 100) % 100 := by
        clear_value p
        rw [Nat.pow_add]
        rw [Nat.mul_mod]
        rw [← Nat.pow_mod]
        rw [← Nat.pow_mod]
        rw [Nat.mul_mod]
        simp
      rw [i]
      suffices p ^ 100 % 100 = 1 by
        rw [Nat.mul_mod]
        rw [this]
        simp
      clear i
      suffices p ^ 20 % 100 = 1 by
        nth_rewrite 1 [show 100 = 20 * 5 by ring]
        rw [Nat.pow_mul]
        rw [Nat.pow_mod]
        rw [this]
      simp [p]
      exact lemma_1 n