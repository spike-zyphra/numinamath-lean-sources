import Mathlib

/- The arithmetic progressions $\{2, 5, 8, 11, \ldots\}$ and $\{3, 10, 17, 24, \ldots \}$ have some common values. What is the largest value less than 500 that they have in common?

The final answer is $ \boxed{479} $-/
theorem number_theory_16345 :
  let a (n : ℕ) := 3 * n + 2
  let b (n : ℕ) := 7 * n + 3
  IsGreatest {x | ∃ m n, x = a m ∧ x = b n ∧ x < 500} 479 := by
    intro a b
    constructor
    · -- Verify that 479 is a common value of two arithmetic progressions.
      simp
      exact ⟨ ⟨159, by simp⟩, ⟨68, by simp⟩ ⟩
    · -- Let $a$ be a common term. We know that \begin{align*}
      -- a&\equiv 2\pmod 3\\
      -- a&\equiv 3\pmod 7
      -- \end{align*}
      intro c hc
      simp at hc
      obtain ⟨ ⟨m, hm⟩, ⟨n, hn⟩, hc ⟩ := hc
      -- by_contra!
      simp [a, b] at hm hn
      have cmod3 : c ≡ 2 [ZMOD 3] := by
        simp [hm]; refine Int.ModEq.symm (Int.modEq_of_dvd ?_); simp
      have cmod7 : c ≡ 3 [ZMOD 7] := by
        simp [hn]; refine Int.ModEq.symm (Int.modEq_of_dvd ?_); simp
      -- Subtracting $17$ from both sides of both congruences gives \begin{align*}
      -- a-17&\equiv -15\equiv 0\pmod 3\nonumber\\
      -- a-17&\equiv -14\equiv 0\pmod 7\nonumber
      -- \end{align*}
      have cmod3' : c - 17 ≡ 0 [ZMOD 3] := Int.ModEq.sub cmod3 rfl
      have cmod7' : c - 17 ≡ 0 [ZMOD 7] := Int.ModEq.sub cmod7 rfl
      -- Since $\gcd(3,7)$, we get $a-17\equiv 0\pmod{3\cdot 7}$, that is, $a\equiv 17\pmod{21}$.
      have h1 := (Int.modEq_and_modEq_iff_modEq_mul (by simp; decide)).1 ⟨cmod3', cmod7'⟩
      -- So all common terms must be of the form $17+21m$ for some non-negative integer $m$. Note that any number of the form also satisfies the original congruences.
      -- The largest such number less than $500$ is $17+21\cdot 22=\boxed{479}$.
      by_contra!
      interval_cases c <;> simp at h1 <;> tauto
