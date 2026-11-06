import Mathlib

/- Нека је низ $\left(a_{n}\right)_{n \geqslant 1}$ дефинисан са $a_{1}=3, a_{2}=11$ и $a_{n}=4 a_{n-1}-a_{n-2}$, за $n \geqslant 3$.
 Доказати да је сваки члан овог низа облика $a^{2}+2 b^{2}$ за неке природне $a$ и $b$.

(Ђорђе Баралић) -/
theorem number_theory_608058 {a: ℕ → ℤ} (ha0: a 0 = 3)
  (ha1: a 1 = 11) (han: ∀n, n ≥ 2 → a n = 4 * (a (n-1)) - a (n-2)):
  ∀n, ∃ (a' b': ℕ), a n = a' ^ 2 + 2 * b' ^ 2 := by
  -- by definition, the third term a2 = 4a1 - a0 = 41
  have ha2: a 2 = 41 := by
    rw [han 2 le_rfl]
    simp [ha0, ha1]
  -- the fourth term a3 = 4a2 - a1 = 153
  have ha3: a 3 = 153 := by
    rw [han 3 (by norm_num)]
    simp [ha2, ha1]
  -- then, use induction, we prove
  -- a_{2n-1} = a_{n-1}^2 + 2 ((a_{n}-a_{n-1})/2)^2,
  -- a_{2n} = a_n^2 + 2 ((a_n - a_{n-1})/2)^2
  have: ∀n, n ≥ 1 → (a (2*n):ℚ) = (a (n-1))^2 + 2 * ((a n - a (n-1))/2)^2 ∧
    (a (2*n + 1):ℚ) = (a n)^2 + 2 * ((a n - a (n-1))/2)^2 := by
    intro n nge
    induction' n,nge using Nat.le_induction with n nge ih
    · rw [ha0, ha2, ha3, ha1]
      norm_num
    · -- express a_{n+1} in terms of an and a_{n-1}
      have h1: (a (n+1):ℚ) = 4 * a n - a (n-1) := by
        rw [han (n+1) (by linarith [nge])]
        push_cast; congr
      have hleft: (a (2*(n+1)):ℚ) = (a n)^2 + 2 * ((a (n+1) - a n)/2)^2 := by
        -- 2(n+1) = 2n+2, by han, we can express it in terms of a_2n and 2_{2n+1}
        have hh1: 2*n+1 = (2*(n+1)) - 1 := by omega
        have hh2: 2*n = 2*(n+1) - 2 := by omega
        rw [han (2*(n+1)) (by simp), ← hh1, ← hh2]
        -- then we can use indutive hypothesis.
        push_cast
        rw [ih.left, ih.right, h1]
        field_simp
        ring
      have hright: (a (2*(n+1)+1):ℚ) = (a (n+1))^2 + 2 * ((a (n+1) - a n)/2)^2 := by
        -- 2(n+1)+1 = 2n+3, by han, we can express it in terms of a_2n and 2_{2n+1}
        have hh1: 2*(n+1) = 2*(n+1)+1 - 1 := by simp
        have hh2: 2*n+1 = 2*(n+1)+1 - 2 := by omega
        rw [han (2*(n+1)+1) (by linarith [nge]), ← hh1, ← hh2]
        -- use inductive hypothesis
        push_cast
        rw [hleft, h1, ih.right]
        field_simp
        ring
      exact ⟨hleft, hright⟩
  -- note that (an - a_{n-1})/2 is integer.
  have hdvd(n:ℕ)(hn: n ≥ 1): 2 ∣ a n - a (n-1) := by
    induction' n,hn using Nat.le_induction with n hn ih
    · rw [ha1, ha0]
      norm_num
    · rw [han (n+1) (by linarith [hn])]
      simp only [add_tsub_cancel_right]
      have: 4*a n - a (n+1-2) - a n =
        (a n - a (n-1)) + 2*a n := by
        have: n+1-2 = n-1 := by omega
        rw [this]; ring
      rw [this]
      apply Int.dvd_add ih (Int.dvd_mul_right _ _)
  intro n
  -- exist natural number square is same to exist integer square
  suffices (∃(a' b':ℤ), a n = a'^2 + 2*b'^2) by
    rcases this with ⟨a',b',hab⟩
    use a'.natAbs, b'.natAbs
    rw [hab]
    simp only [Int.natCast_natAbs, sq_abs]
  -- done.
  rcases (Nat.even_or_odd' n) with ⟨m, (rfl | rfl)⟩
  · by_cases hm: m = 0
    · use 1,1
      simp [hm, ha0]
    replace hm: m ≥ 1 := by omega
    qify
    rw [(this m hm).left]
    use (a (m-1)), (((a m) - (a (m-1)))/2)
    rw [Int.cast_div (hdvd m hm) (by norm_num)]
    simp only [Int.cast_sub, Int.cast_ofNat]
  · by_cases hm: m = 0
    · use 3,1
      simp [hm, ha1]
    replace hm: m ≥ 1 := by omega
    qify
    rw [(this m hm).right]
    use (a m), (((a m) - (a (m-1)))/2)
    rw [Int.cast_div (hdvd m hm) (by norm_num)]
    simp only [Int.cast_sub, Int.cast_ofNat]