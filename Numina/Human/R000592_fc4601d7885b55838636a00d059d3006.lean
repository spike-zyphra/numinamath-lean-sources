import Mathlib

open Real

/- Let $a_0=-2,b_0=1$, and for $n\geq 0$, let
\begin{align*}a_{n+1}&=a_n+b_n+\sqrt{a_n^2+b_n^2},\\b_{n+1}&=a_n+b_n-\sqrt{a_n^2+b_n^2}.\end{align*}Find $\frac{1}{a_{2012}} + \frac{1}{b_{2012}}.$ -/
theorem algebra_13034 {a b : ℕ → ℝ}
    (ha0 : a 0 = -2) (hb0 : b 0 = 1)
    (han : ∀ n, a (n + 1) = a n + b n + sqrt (a n ^ 2 + b n ^ 2))
    (hbn : ∀ n, b (n + 1) = a n + b n - sqrt (a n ^ 2 + b n ^ 2)) :
    1 / a 2012 + 1 / b 2012 = 1 / 2 := by
  -- notice that 1/a_{n+1} + 1/b_{n+1} = 1/a_n + 1/b_n
  have h1: ∀n:ℕ,
    1 / (a (n+1)) + 1 / (b (n+1)) = 1 / (a n) + 1 / (b n) := by
    intro n
    rw [han n, hbn n]
    -- we will use (c+d)(c-d) = d^2-d^2 to simplifty.
    let c := a n + b n
    have c_def: c = a n + b n := rfl
    let d := √(a n ^2 + b n ^2)
    have d_def: d = √(a n ^2 + b n ^2) := rfl
    rw [← c_def, ← d_def]
    -- since c+d and c-d is at the denominator. before going on, we should show they are nonzero.
    -- a n + b n < 0
    have ht1: ∀n:ℕ, a n + b n < 0 := by
      intro n
      induction' n with e he
      · rw [ha0, hb0]; simp
      · rw [han e, hbn e]
        simp; linarith [he]
    -- we show c+d > 0 and c < d using induction.
    have ht2: a n + b n + √(a n ^2 + b n ^2) > 0 ∧
      a n + b n < √(a n ^2 + b n ^2):= by
      induction' n with e he
      · rw [ha0, hb0]; simp; norm_num
        have tt1: 1^2 < (5:ℝ) := by norm_num
        have tt2: 0 < √5 := by norm_num
        constructor
        · exact lt_sqrt_of_sq_lt tt1
        · linarith [tt2]
      · rw [han e, hbn e]; simp at he
        let ssum := a e + b e
        have ssum_def: ssum = a e + b e := rfl
        let ssqrt := √(a e ^ 2 + b e ^ 2)
        have ssqrt_def: ssqrt = √(a e ^ 2 + b e ^ 2) := rfl
        rw [← ssum_def, ← ssqrt_def]
        rw [← ssum_def, ← ssqrt_def] at he
        simp
        have tt1: (ssum+ssqrt)^2+(ssum-ssqrt)^2 = 2*(ssum^2+ssqrt^2) := by
          ring
        rw [tt1]
        have tt2: √(2*(ssum^2 + ssqrt^2)) > 2*|ssum| := by
          have hh1: ssqrt^2 > ssum^2 := by
            apply sq_lt_sq.mpr
            apply abs_lt.mpr
            have: |ssqrt| = ssqrt := by
              have: 0 ≤ ssqrt := by
                rw [ssqrt_def]
                exact sqrt_nonneg (a e ^ 2 + b e ^ 2)
              exact abs_of_nonneg this
            rw [this]
            constructor <;> linarith [he.left, he.right]
          have hh2: 2*(ssum^2 + ssqrt^2) > (2*ssum)^2 := calc
            2*(ssum^2+ssqrt^2) > 2*(ssum^2+ssum^2) := by linarith [hh1]
            _ = (2*ssum)^2 := by ring
          have hh3: √((2*ssum)^2) = 2*|ssum| := by
            have htt1: √((2*ssum)^2) = |2*ssum| := by
              exact sqrt_sq_eq_abs (2 * ssum)
            have htt2: |2*ssum| = -(2*ssum) := by
              have: 2*ssum ≤ 0 := by
                have: ssum < 0 := by
                  rw [ssum_def]
                  apply ht1 e
                linarith [this]
              apply abs_of_nonpos this
            have htt3: |ssum| = -ssum := by
              apply abs_of_nonpos (by linarith [ht1 e])
            rw [htt1, htt2, htt3]; ring
          rw [← hh3]
          apply sqrt_lt_sqrt (sq_nonneg (2*ssum)) hh2
        have tt3: ssum + ssum = -2*|ssum| := by
          have: |ssum| = -ssum := by
            apply abs_of_nonpos (by linarith [ht1 e])
          rw [this]; ring
        rw [tt3]
        constructor
        · linarith [tt2]
        · have: -2*|ssum| < 2*|ssum| := by
            have hh1: 0 < |ssum| := by
              have: |ssum| = -ssum := by
                apply abs_of_nonpos (by linarith [ht1 e])
              rw [this, ssum_def]
              linarith [ht1 e]
            linarith [hh1]
          linarith [tt2, this]
    -- therefore we have c+d ≠ 0 and c-d ≠ 0
    have ht3: c+d ≠ 0 := by
      rw [c_def, d_def]; linarith [ht2.left]
    have ht4: c-d ≠ 0 := by
      rw [c_def, d_def]; linarith [ht2.right]
    -- multiply (c+d)(c-d) to 1/(c+d) and 1/(c-d)
    have ht5: 1/(c+d) + 1/(c-d) = 2*c/(c^2-d^2) := by
      have tt1: c^2-d^2 = (c+d)*(c-d) := by ring
      rw [tt1]; field_simp [ht3, ht4]; ring
    -- d^2=(an^2+bn^2)
    have ht6: d^2 = a n ^ 2 + b n ^ 2 := by
      rw [d_def]
      have: 0 ≤ a n ^ 2 + b n ^ 2 := by
        linarith [sq_nonneg (a n), sq_nonneg (b n)]
      exact sq_sqrt this
    -- c^2-d^2=(an+bn)^2-(an^2+bn^2)=2anbn
    have ht7: c^2-d^2 = 2 * (a n * b n) := by
      rw [c_def, ht6]; ring
    -- therefore 2c/(c^2-d^2) = (an+bn)/(anbn) = 1/an+1/bn
    have hnez: c^2-d^2 ≠ 0 := by
      have: c^2-d^2 = (c+d)*(c-d) := by ring
      rw [this]
      by_contra! hc
      have: c+d = 0 ∨ c-d = 0 := mul_eq_zero.mp hc
      tauto
    have hha: a n ≠ 0 := by
      by_contra! hc
      rw [ht7, hc] at hnez; simp at hnez
    have hhb: b n ≠ 0 := by
      by_contra! hc
      rw [ht7, hc] at hnez; simp at hnez
    have ht8: 2*c/(c^2-d^2) = 1/(a n) + 1/(b n) := by
      rw [ht7, c_def]; field_simp [hha, hhb]
      ring
    rw [ht5, ht8]
  -- since 1/a_{n+1} + 1/b_{n+1} = 1/a_n + 1/b_n, it must be constant. we show it by induction.
  have h2: ∀n:ℕ, 1/(a n) + 1/(b n) = 1/(a 0) + 1/(b 0) := by
    intro n
    induction' n with d hd
    · simp
    · rw [h1 d, hd]
  rw [h2 2012]
  -- therefore 1/a2012 + 1/b2012 = 1/a0 + 1/b0 = 1/-2 + 1/1 = 1/2
  rw [ha0, hb0]; field_simp; ring