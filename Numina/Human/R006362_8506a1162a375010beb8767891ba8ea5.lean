import Mathlib

/- Let $j$ be a positive integer and $M$ be a positive real number. Let $k=2j$.
Let $f:\mathbb{Z}_+\to\mathbb{Z}_+$ be a function defined as follows:
\[
f(x)=\begin{cases}
3x+1,& \text{if } x \text{ is odd}\\
x/2, & \text{if } x \text{ is even.}
\end{cases}
\]
Let $f^i(x)$ denote the $i$-th iteration of $f$ on $x$ (for example, $f^1(x)=f(x)$ and $f^{i+1}(x)=f(f^i(x))$).
Prove that if $M < (3/2)^j$, then there exists a positive integer $x$ such that $f^k(x) > M x$. -/
theorem number_theory_636266 {j: ℕ} (jpos: 0 < j) {f: ℕ → ℕ}
  (hf: ∀n, 0 < n → f n = if Odd n then 3*n+1 else n/2 ):
  ∀(M:ℝ), M < (3/2)^j → (∃ x:ℕ, 0 < x ∧ f^[2*j] x > M * x) := by

  -- consider x = 2^j - 1, calculate f apply to it.
  have {i: ℕ} (hi: i ≤ j):
    f^[2*i] (2^j-1) = 3^i * 2^(j-i) - 1 := by
    induction' i with i ih
    · simp
    · rw [show 2*(i+1) = 2*i+1+1 by ring]
      simp only [Function.iterate_succ', Function.comp_apply]
      rw [ih (by omega)]
      -- clearly, 3^i 2^(j-i) - 1 is odd and > 0.
      have h1: Odd (3^i * 2^(j-i) - 1) := by
        suffices Even (3^i * 2^(j-i)) by
          refine Nat.Even.sub_odd ?_ this ?_
          · exact NeZero.one_le
          · exact Nat.odd_iff.mpr rfl
        suffices Even (2^(j-i)) by
          exact Even.mul_left this (3 ^ i)
        refine (Nat.even_pow' ?_).mpr (Nat.even_iff.mpr rfl)
        omega
      have h2: 0 < 3^i * 2^(j-i) - 1 := by
        suffices 1 < 3^i * 2^(j-i) by
          exact Nat.zero_lt_sub_of_lt this
        suffices 1 < 2^(j-i) by
          refine Right.one_lt_mul_of_le_of_lt ?_ this
          exact Nat.one_le_pow' i 2
        refine Nat.one_lt_two_pow_iff.mpr ?_
        omega
      rw [hf _ h2, if_pos h1]
      -- 3 (3^i 2^(j-i) - 1) + 1 = 3^(i+1) 2^(j-i) - 2 = 2(3^(i+1) 2^(j-i-1) - 1)
      have h3: 3 * (3^i * 2^(j-i) - 1) + 1 =
        2 * (3^(i+1) * 2^(j-(i+1)) - 1) := by
        have hh1: 1 ≤ 3^i * 2^(j-i) := by
          exact NeZero.one_le
        have hh2: 1 ≤ 3^(i+1) * 2^(j-(i+1)) := by
          exact NeZero.one_le
        have hh3: 2^(j-i) = 2 * 2^(j-(i+1)) := by
          rw [← Nat.pow_succ']
          congr 1
          omega
        zify
        rw [Nat.cast_sub hh1, Nat.cast_sub hh2, hh3]
        push_cast
        ring
      have h4: 0 < 2 * (3^(i+1) * 2^(j-(i+1)) - 1) := by
        simp [← h3]
      have h5: ¬ Odd (2 * (3^(i+1) * 2^(j-(i+1)) - 1) ) := by
        refine Nat.not_odd_iff_even.mpr ?_
        apply even_two_mul
      rw [h3, hf _ h4, if_neg h5, Nat.mul_div_right _ (by norm_num)]

  -- thus 3^j - 1 = (3/2)^j 2^j - (3/2)^j (2/3)^j > (3/2)^j (2^j - 1)
  intro M Mlt
  use (2^j - 1)
  have hh: 0 < 2^j - 1 := by
    suffices 1 < 2^j by
      exact Nat.zero_lt_sub_of_lt this
    rw [show 1 = 2^0 by simp]
    refine Nat.pow_lt_pow_of_lt (by norm_num) jpos
  refine ⟨hh, ?_⟩
  rw [this le_rfl, Nat.cast_sub (by exact NeZero.one_le),
  Nat.cast_sub (by exact Nat.one_le_two_pow), Nat.sub_self, pow_zero, mul_one]
  push_cast
  have h1: (3:ℝ)^j - 1 = (3/2)^j * (2^j - (2/3)^j) := by
    rw [mul_sub, ← mul_pow, ← mul_pow]
    simp
  have h2: (2:ℝ)^j - (2/3)^j > 2^j - 1 := by
    suffices (2/3: ℝ)^j < 1 by
      linarith only [this]
    apply pow_lt_one₀ ?_ ?_ jpos.ne'
    <;> norm_num
  rw [h1]
  apply mul_lt_mul Mlt h2.le ?_ ?_
  · apply sub_pos.mpr ?_
    suffices (1:ℕ) < 2^j by
      rify at this
      exact this
    exact Nat.succ_lt_of_lt_pred hh
  · apply pow_nonneg ?_
    norm_num