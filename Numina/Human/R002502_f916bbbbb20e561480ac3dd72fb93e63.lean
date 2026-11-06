import Mathlib

open Rat Nat

/-- For how many integers $n$ is $\dfrac n{20-n}$ the
[square](https://artofproblemsolving.com/wiki/index.php/Perfect_square) of an
integer?
$\mathrm{(A)}\ 1 \qquad\mathrm{(B)}\ 2 \qquad\mathrm{(C)}\ 3
\qquad\mathrm{(D)}\ 4 \qquad\mathrm{(E)}\ 10$ -/
theorem number_theory_1125 : {n : ℤ | n ≠ 20 ∧ ∃ x : ℕ, x^2 = (n:ℚ) / (20 - n)}.ncard = 4 := by

  -- We will show that $n = 0, 10, 16, 18$ are the only solutions.
  suffices {n : ℤ | n ≠ 20 ∧ ∃ x : ℕ, x^2 = (n:ℚ) / (20 - n)} = {0, 10, 16, 18}
  from by rw [this]; norm_num

  ext n
  constructor; swap

  -- Each of $n = 0, 10, 16, 18$ works.
  · rintro (rfl | rfl | rfl | rfl)
    . exact ⟨by norm_num, 0, by norm_num⟩
    · exact ⟨by norm_num, 1, by norm_num⟩
    · exact ⟨by norm_num, 2, by norm_num⟩
    · exact ⟨by norm_num, 3, by norm_num⟩

  -- Let $n$ be a solution.
  · intro hn
    rcases hn with ⟨hn, x, hx⟩

    -- $n$ must be nonnegative because $x^2$ is nonnegative.
    have hnneg : 0 ≤ n := by
      by_contra! h
      suffices (x:ℚ)^2 < 0 from by nlinarith
      rw [hx]
      exact div_neg_of_neg_of_pos (by norm_cast) (by norm_cast; nlinarith)

    -- $n$ cannot be $20$ because the denominator must be nonzero.
    have : (n:ℚ) ≠ 20 := by norm_cast
    have : 20 - (n:ℚ) ≠ 0 := by
      intro h
      apply this
      calc _ = (n:ℚ) + 0 := by simp
           _ = (n:ℚ) + (20 - (n:ℚ)) := by rw [h]
           _ = 20 := by simp

    -- Rewrite $n$ in terms of $x$.
    have : n = 20 * (x:ℚ)^2 / (x^2 + 1) := by rw [hx]; field_simp [hn]

    -- This means that $x^2 + 1$ divides $20 x^2$
    have hn : (n:ℚ) * (x^2 + 1) = 20 * x^2 := by field_simp [this]
    have : n * (x^2 + 1) = 20 * x^2 := by norm_cast at hn
    have hxdvd : x^2 + 1 ∣ 20 * x^2 := by
      rw [dvd_def]
      use n.natAbs
      rw [←Int.natAbs_of_nonneg hnneg] at this
      norm_cast at this
      rw [←this]
      ring

    -- $x^2$ and $x^2 + 1$ are coprime
    have : Nat.gcd (x^2) (x^2 + 1) = 1 := by
      rw [gcd_eq_iff]
      refine ⟨by omega, by omega, ?_⟩
      intro d hd1 hd2
      calc d ∣ (x^2 + 1) - x^2 := by apply dvd_sub' hd2 hd1
           _ = 1 := by simp

    -- This means that $x^2 + 1$ divides $20$
    replace hxdvd : x^2 + 1 ∣ 20 := by
      refine Coprime.dvd_of_dvd_mul_right ?_ hxdvd
      apply Coprime.symm
      rw [coprime_iff_gcd_eq_one]
      exact this

    -- The factors of $20$ are $1, 2, 4, 5, 10, 20$.
    have : divisors 20 = {1, 2, 4, 5, 10, 20} := by decide
    -- So, $x^2 + 1$ is $1, 2, 4, 5, 10$ or $20$.
    have : x^2 + 1 ∈ ({1, 2, 4, 5, 10, 20} : Finset ℕ) := by
      rw [←this, mem_divisors]
      exact ⟨hxdvd, by norm_num⟩
    -- Or equivalently, $x^2$ is $0, 1, 3, 4, 9$ or $19$.
    have : x^2 ∈ ({0, 1, 3, 4, 9, 19} : Finset ℕ) := by
      simp at this ⊢
      exact this

    -- Therefore, $x$ is $0, 1, 2, 3$.
    have : x ∈ ({0, 1, 2, 3} : Finset ℕ) := by
      simp at this ⊢
      rcases this with (rfl | h | h | h | h | h)
      · trivial
      · right; left; nlinarith
      · right; left
        nlinarith
      · right; right; left; nlinarith
      · right; right; right; nlinarith
      · exfalso
        have : x = 4 := by
          calc x = (19).sqrt := by rw [←h, pow_two, Nat.sqrt_eq]
               _ = 4 := by norm_num
        rw [this] at h
        contradiction

    -- Now, substituting $x = 0, 1, 2, 3$ back into $n = 20 x^2 / (x^2 + 1)$,
    --  gives $n = 0, 10, 16, 18$.
    simp at this ⊢
    rcases this with (rfl | rfl | rfl | rfl)
    · simp at hn
      left; exact hn
    · simp at hn
      norm_cast at hn
      push_cast at hn
      right; left; nlinarith
    · simp at hn
      norm_cast at hn
      push_cast at hn
      right; right; left; nlinarith
    · simp at hn
      norm_cast at hn
      push_cast at hn
      right; right; right; nlinarith