import Mathlib

open Finset

/-- Let $S_n$ and $T_n$ be the respective sums of the first $n$ terms of two arithmetic series. If
$S_n:T_n=(7n+1):(4n+27)$ for all $n$, the ratio of the eleventh term of the first series to the
eleventh term of the second series is:

$\text{(A) } 4:3\quad \text{(B) } 3:2\quad \text{(C) } 7:4\quad \text{(D) } 78:71\quad \text{(E)
undetermined}$ -/
theorem algebra_96068 {S T s t : ℕ → ℝ} {p q : ℝ} (hs : ∀ n, s (n + 1) = s n + p)
    (hr : ∀ n, t (n + 1) = t n + q) (hS : ∀ n, S n = ∑ i ∈ Icc 1 n, s i)
    (hT : ∀ n, T n = ∑ i ∈ Icc 1 n, t i) (hST : ∀ n, S n / T n = (7 * n + 1) / (4 * n + 27)) :
    s 11 / t 11 = 4 / 3 := by

  -- Let $s$ and $t$ be the sequences corresponding to $S$ and $T$. Let $p$ and $q$ be the common
  -- differences of $s$ and $t$ respectively.

  -- First, let's observe that $T_1$, $T_2$ and $T_3$ are nonzero, so we can safely divide by them
  -- in our calculations.
  have hT1_ne_zero : T 1 ≠ 0 := by
    intro h
    have := hST 1
    rw [h] at this
    norm_num at this
  have : T 2 ≠ 0 := by
    intro h
    have := hST 2
    rw [h] at this
    norm_num at this
  have : T 3 ≠ 0 := by
    intro h
    have := hST 3
    rw [h] at this
    norm_num at this

  -- For $n = 1$, we have $S 1 / T 1 = 8 / 31$.
  have : S 1 / T 1 = 8 / 31 := by simp [hST]; norm_num

  -- This means that $S_1 = 8 a$ and $T_1 = 31 a$ for some $a$.
  have : ∃ a, S 1 = 8 * a ∧ T 1 = 31 * a := by
    use T 1 / 31
    field_simp at this ⊢
    assumption
  rcases this with ⟨a, hS1, hT1⟩

  -- By the definitions of $S$ and $T$, $S_1 = s_1$ and $T_1 = t_1$. So the first term of the
  -- sequences $s$ and $t$ are $8 a$ and $31 a$ respectively.
  have hs1 : s 1 = 8 * a := by rw [←hS1]; simp [hS]
  have ht1 : t 1 = 31 * a := by rw [←hT1]; simp [hT]

  -- For $n = 2$, we have $S_2 / T_2 = 3 / 7$.
  have : S 2 / T 2 = 3 / 7 := by simp [hST]; norm_num

  -- This means that $S_2 = 3 b$ and $T_2 = 7 b$ for some $b$.
  have : ∃ b, S 2 = 3 * b ∧ T 2 = 7 * b := by
    use T 2 / 7
    field_simp at this ⊢
    assumption
  rcases this with ⟨b, hS2, hT2⟩

  -- By the definitions of $S$ and $T$, $S_2 = s_1 + s_2$ and $T_2 = t_1 + t_2$. So the second term
  -- of the sequences $s$ and $t$ are $3 b - 8 a$ and $7 b - 31 a$ respectively.
  have hs2 : s 2 = 3 * b - 8 * a := by rw [←hS2, ←hs1]; simp [hS, sum_Icc_succ_top]
  have ht2 : t 2 = 7 * b - 31 * a := by rw [←hT2, ←ht1]; simp [hT, sum_Icc_succ_top]

  -- So the common differences of $s$ and $t$ are $3 b - 16 a$ and $7 b - 62 a$ respectively.
  have hp : p = 3 * b - 16 * a := by
    calc _ = s 2 - s 1 := by rw [hs 1]; ring
         _ = 3 * b - 8 * a - (8 * a) := by rw [hs2, hs1]
         _ = _ := by ring
  have hq : q = 7 * b - 62 * a := by
    calc _ = t 2 - t 1 := by rw [hr 1]; ring
         _ = 7 * b - 31 * a - (31 * a) := by rw [ht2, ht1]
         _ = _ := by ring

  -- For $n = 3$, we have $S_3 / T_3 = 22 / 39$. Or, equivalently, $39 S_3 = 22 T_3$.
  have hST3 : S 3 / T 3 = 22 / 39 := by simp [hST]; norm_num
  field_simp at hST3; rw [mul_comm] at hST3

  -- Using the first term and the common difference of the sequence $s$, we can write:
  have hS3 : S 3 = 9 * b - 24 * a := by
    -- $S_3 = s_1 + s_2 + s_3$
    calc _ = s 1 + s 2 + s 3 := by simp [hS, sum_Icc_succ_top]
    -- $ = s_1 + s_2 + s_3 + p$
         _ = s 1 + s 2 + (s 2 + p) := by rw [hs 2]
    -- $ = 9 b - 24 a.$
         _ = _ := by rw [hs1, hs2, hp]; ring

  -- Using the first term and the common difference of the sequence $t$, we can write:
  have hT3 : T 3 = 21 * b - 93 * a := by
    -- $T_3 = t_1 + t_2 + t_3$
    calc _ = t 1 + t 2 + t 3 := by simp [hT, sum_Icc_succ_top]
    -- $ = t_1 + t_2 + t_3 + q$
         _ = t 1 + t 2 + (t 2 + q) := by rw [hr 2]
    -- $ = 21 b - 93 a.$
         _ = _ := by rw [ht1, ht2, hq]; ring

  -- Then combining the above two equations for $S_3$ and $T_3$, with the equation $39 S_3 = 22 T_3$,
  -- and then simplifying, we get $b = 10 a$.
  have hba : b = 10 * a := by
    rw [hS3, hT3] at hST3
    nlinarith only [hST3]

  -- Then, the common difference of $s$ is $3b - 16a = 3(10a) - 16a = 14a$.
  replace hp : p = 14 * a := by rw [hp, hba]; ring

  -- And, the common difference of $t$ is $7b - 62a = 7(10a) - 62a = 8a$.
  replace hq : q = 8 * a := by rw [hq, hba]; ring

  -- Using the arithmetic sequences formula, we can write the general term of $s$ as
  -- $s_n = 8 a + (n - 1) 14 a = (14 n - 6) a$.
  have hsn {n : ℕ} (hn : 1 ≤ n) : s n = (14 * n - 6) * a := by
    induction' n with n ih
    · contradiction

    by_cases hn : n = 0
    · rw [hn, hs1]; ring

    rw [hs n, ih (by omega), hp, Nat.cast_add]
    ring

  -- Using the arithmetic sequences formula, we can write the general term of $t$ as
  -- $t_n = 31 a + (n - 1) 8 a = (8 n + 23) a$.
  have htn {n : ℕ} (hn : 1 ≤ n) : t n = (8 * n + 23) * a := by
    induction' n with n ih
    · contradiction

    by_cases hn : n = 0
    · rw [hn, ht1]; ring

    rw [hr n, ih (by omega), hq, Nat.cast_add]
    ring

  -- Substituting $n = 11$ in the above two equations, we get $s_11 = 148a$ and $t_11 = 111a$. So,
  -- $s_11 / t_11 = 148 / 111 = 4 / 3$.
  rw [hsn (by norm_num), htn (by norm_num)]

  have : a ≠ 0 := by
    intro h
    rw [hT1, h] at hT1_ne_zero
    norm_num at hT1_ne_zero

  field_simp
  ring