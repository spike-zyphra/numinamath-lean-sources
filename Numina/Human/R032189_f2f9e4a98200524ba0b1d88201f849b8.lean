import Mathlib

/- 10,11 [ Binary numeral system ]

Can three different numbers of the form $2^{n}+1$, where $n$ is a natural number, be consecutive terms of a geometric progression

# -/
theorem number_theory_182650 :
    ¬ ∃ a b c : ℕ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∃ m n p : ℕ, a = 2 ^ m + 1 ∧ b = 2 ^ n + 1 ∧ c = 2 ^ p + 1 ∧
     ∃ r : ℚ, b = a * r ∧ c = b * r := by
  -- first normalize the negation, and bring out all assumptions
  push_neg
  rintro a b c hab hac hbc m n p ham hbn hcp r habr hbcr
  -- prove r ≠ 0 as that'd make 2^n + 1 = 0
  have : r ≠ 0 := by
    rintro hr
    rw [hr, hbn] at habr
    ring_nf at habr
    norm_cast at habr
    linarith [show 2 ^ n + 1 > 0 by positivity]
  -- we'll prove by assuming a ≤ b wlog
  wlog h : a ≤ b
    -- for wlog when a > b, we can use the theorem with a, b, c flipped in order
  . apply this c b a (hbc.symm) (hac.symm) (hab.symm)
    . exact hcp
    . exact hbn
    . exact ham
    . change b = c * (1/r)
      rw [hbcr]
      field_simp
    . change a = b * (1/r)
      rw [habr]
      field_simp
    . simp
      assumption
    . simp at h
      qify at h ⊢
      rw [habr] at h
      nth_rw 2 [show (a:ℚ) = a * 1 by simp] at h
      have : r < 1 := by
        refine (mul_lt_mul_left ?_).mp h
        rw [ham]
        positivity
      rw [hbcr]
      nth_rw 2 [show (b:ℚ) = b * 1 by simp]
      gcongr
  -- due to geometric ratio, ac = b^2
  have habc : a * c = b^2 := by
    qify
    rw [hbcr, habr]
    ring
  rw [ham, hbn, hcp] at habc
  ring_nf at habc
  -- a < b < c as we are givne a ≠ b and b ≠ c and by proving r > 1
  have h : a < b := by exact Nat.lt_of_le_of_ne h hab
  have h' : b < c := by
    qify at h ⊢
    rw [habr] at h
    nth_rw 1 [show (a:ℚ) = a * 1 by simp] at h
    have : 1 < r := by
      refine (mul_lt_mul_left ?_).mp h
      rw [ham]
      positivity
    rw [hbcr]
    nth_rw 1 [show (b:ℚ) = b * 1 by simp]
    gcongr
    norm_cast; rw [hbn]; positivity
  rw [ham, hbn] at h
  rw [hbn, hcp] at h'
  -- let's express all in terms of m, n, p
  have h : m < n := by exact pow_lt_pow_iff_right₀ (show 1 < 2 by norm_num) |>.mp (by linarith)
  have h' : n < p := by exact pow_lt_pow_iff_right₀ (show 1 < 2 by norm_num) |>.mp (by linarith)
  clear * - h h' habc
  have habc : 2 ^ m * (1 + 2 ^ p + 2 ^ (p - m)) = 2^m * (2^(n - m) * 2 + 2^ (n*2 -m)) := by
    ring_nf
    nth_rw 2 [← pow_add]; nth_rw 2 [← pow_add]; nth_rw 2 [← pow_add]
    rw [show m + (p - m) = p by omega, show m + (n - m) = n by omega, show m + (n*2 - m) = n*2 by omega]
    linarith
  simp at habc
  -- now after dividing by 2^m, we have left side odd, right side even, contradiction
  have h₁ : Even (2 ^ (n - m) * 2 + 2 ^ (n * 2 - m)) := by
    use 2^ (n-m) + 2^(n*2-m-1)
    ring_nf
    congr
    rw [← pow_succ]
    congr; omega
  have h₂ : Odd (1 + 2 ^ p + 2 ^ (p - m)) := by
    use 2^(p-1) + 2^(p-m-1)
    ring_nf
    congr
    repeat
      rw [← pow_succ]
      congr; omega
  rw [← habc] at h₁
  absurd (Nat.not_odd_iff_even.mpr h₁) h₂; trivial