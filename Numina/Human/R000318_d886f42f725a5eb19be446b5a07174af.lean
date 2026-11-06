import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all integer triples  $(a,b,c)$  with  $a>0>b>c$  whose sum equal  $0$  such that
    the number  $$ N=2017-a^3b-b^3c-c^3a $$   is a perfect square of an integer.-/
theorem number_theory_8910 :
  {(a, b, c) : ℤ × ℤ × ℤ | 0 < a ∧ b < 0 ∧ c < b ∧ a + b + c = 0 ∧
    ∃ n : ℕ, n^2 = 2017 - a^3 * b - b^3 * c - c^3 * a} = {(36, -12, -24)} := by
    ext x
    simp
    -- In this proof, `x.1` means $a$, `x.2.1` means $b$ and `x.2.2` means $c$.
    set a := x.1
    set b := x.2.1
    set c := x.2.2
    constructor
    · intro ⟨apos, bneg, cltb, c1, c2⟩
      obtain ⟨t, c2 ⟩ := c2
      --  Let \(a = m + n\), \(b = -m\), and \(c = -n\),
      -- where \(m\) and \(n\) are positive integers with \(m < n\).
      -- This ensures \(a > 0\), \(b < 0\), and \(c < 0\).
      let m := -b
      let n := -c
      have c3 : a = m + n := by omega
      -- Substituting these values into the expression for \(N\) gives:
      -- \[
      -- N = 2017 + (m^2 + mn + n^2)^2
      -- \]
      --   For \(N\) to be a perfect square, there must exist an integer \(t\) such that:
      -- \[
      -- t^2 = 2017 + S^2
      -- \]
      have c4 : t^2 = 2017 + (m^2 + m*n + n^2)^2 := by
        rw [c2, c3]; simp [m, n]; nlinarith
      -- Let \(S = m^2 + mn + n^2\), so \(N = 2017 + S^2\).
      set s := (m^2 + m*n + n^2).natAbs with hs
      have : s < t := by
        have : s^2 < t^2 := by
          simp [s,]; zify; rw [c4, sq_abs]; omega
        exact (Nat.pow_lt_pow_iff_left (by omega)).1 this
      -- This can be rewritten as:
      -- \[
      -- t^2 - S^2 = 2017 \implies (t - S)(t + S) = 2017
      -- \]
      have c5 : (t - s) * (t + s) = 2017 := by
        zify; rw [Nat.cast_sub (le_of_lt this)]; simp [s];
        ring_nf
        simp [c4]
        ring
      have h1 := Nat.prime_mul_iff.1 (c5.symm ▸ (show Nat.Prime 2017 by native_decide))
      simp at h1
      -- Since 2017 is a prime number, the only positive integer solutions are \(t - S = 1\)
      -- and \(t + S = 2017\).
      replace h1 : Nat.Prime (t + s) ∧ t - s = 1 := by
        refine (or_iff_right ?_).1 h1
        simp
        intro h
        have : 1 < t - s := Nat.Prime.one_lt h
        omega
      -- Solving these gives \(t = 1009\) and \(S = 1008\).
      have c6 : t = 1009 ∧ s = 1008 := by
        have : t + s = 2017 := by simp [h1] at c5; assumption
        omega
      --  We now solve the equation:
      -- \[
      -- m^2 + mn + n^2 = 1008
      -- \]
      have c7 : m ^ 2 + m * n + n ^ 2 = 1008 := by
        have h2 : (m ^ 2 + m * n + n ^ 2).natAbs = 1008 := by rw [←hs, c6.2]
        have h3 : 0 < m ^ 2 + m * n + n ^ 2 := by simp [m,n]; nlinarith
        rw [Int.natAbs_eq_iff] at h2
        omega
      -- Through systematic testing, it is found that \(m = 12\) and
      -- \(n = 24\) satisfy this equation.
      have h2 : m = 12 ∧ n = 24 := by
        have mpos : 0 < m := by omega
        have mltn : m < n := by omega
        have : m < 19 := by nlinarith
        have : n < 32 := by nlinarith
        interval_cases m <;> (interval_cases n <;> simp at c7 <;> tauto)
      --  Substituting back, we obtain:
      -- \[
      -- a = 12 + 24 = 36,\quad b = -12,\quad c = -24
      -- \]
      ext <;> simp <;> omega
    · -- Verify that
      -- \[
      -- a = 12 + 24 = 36,\quad b = -12,\quad c = -24
      -- \] satisfies the condition.
      intro h
      simp [Prod.eq_iff_fst_eq_snd_eq] at h
      simp [a, b, c, h]
      exact ⟨1009, by decide⟩
