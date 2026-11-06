import Mathlib

theorem Other_5738 (n : ℤ) :
  ¬ ∃ x, x^3 = 3 * n^2 + 3 * n + 7 := by 
  --Suppose that there exist integers $n$ and $m$ such that $m^{3}=3 n^{2}+3 n+7$.
  push_neg
  intro m
  by_contra h1
  --Then from $m^{3} \equiv 1(\bmod 3)$
  have h2 : m ^ 3 ≡ 1 [ZMOD 3] := by
    rw [h1, Int.modEq_iff_dvd]
    have h3 : 1 - (3 * n ^ 2 + 3 * n + 7) = 3 * (- n ^ 2 + -n + -2) := by ring
    exact Dvd.intro (-n ^ 2 + -n + -2) (id (Eq.symm h3))
  --it follows that $m=3 k+1$ for some $k \in \mathbb{Z}$.
  have h4 : m ≡ 1 [ZMOD 3] := by
    by_cases h5 : m % 3 = 1
    · exact h5
    · by_cases h6 : m % 3 = 0
      · have h7 : m ^ 3 ≡ 0 [ZMOD 3] := by
          rw [Int.modEq_iff_dvd]
          simp only [zero_sub, dvd_neg]
          apply Dvd.dvd.pow
          exact Int.dvd_of_emod_eq_zero h6
          norm_num
        have : 1 ≡ 0 [ZMOD 3] := by
          exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h7)) h2)
        contradiction
      · have h7 : m % 3 = 2 := by omega
        have h8 : m ^ 3 ≡ 2 [ZMOD 3] := by
          simp only [Int.ModEq, pow_three, Int.mul_emod, h7, Int.reduceMul, Int.reduceMod, mul_one]
        have : 1 ≡ 2 [ZMOD 3] := by
          exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h8)) h2)
        contradiction
  have h9 : ∃ (k : ℤ), m = 3 * k + 1 := by
    have : 3 ∣ (m - 1) := by
      exact Int.dvd_sub_of_emod_eq h4
    have : ∃ (k : ℤ), m - 1 = 3 * k := by
      exact this
    obtain ⟨k, hk⟩ := this
    use k
    linarith
  obtain ⟨k, hk⟩ := h9
  --Substituting into the initial equation we obtain $3 k\left(3 k^{2}+3 k+1\right)=n^{2}+$ $n+2$.
  rw [hk] at h1
  ring_nf at h1
  have h10 : 3 * k * (3 * k ^ 2 + 3 * k + 1) = n ^ 2 + n + 2 := by
    have h11 : 3 * (3 * k) * (3 * k ^ 2 + 3 * k + 1) = 3 * (n ^ 2 + n + 2) := by 
      ring_nf
      calc
        _ = 1 + k * 9 + k ^ 2 * 27 + k ^ 3 * 27 - 1 := by ring_nf
        _ = 7 + n * 3 + n ^ 2 * 3 - 1 := by rw [h1]
        _ = _ := by ring_nf
    linarith
  have h11 : 3 ∣ (n ^ 2 + n + 2) := by
    rw [← h10, mul_assoc]
    simp only [dvd_mul_right]
  --It is easy to check that $n^{2}+n+2$ cannot be divisible by 3 ,
  by_cases h12 : n % 3 = 0
  · have h13 : 3 ∣ n := by
      exact Int.dvd_of_emod_eq_zero h12
    have h14 : 3 ∣ n ^ 2 := by
      apply Dvd.dvd.pow h13
      norm_num
    have h15 : 3 ∣ n ^ 2 + n := by
      exact (Int.dvd_add_right h14).mpr h13
    have h16 : 3 ∣ (2 : ℤ) := by
      have : 2 = (n ^ 2 + n + 2) - (n ^ 2 + n) := by omega
      rw [this]
      exact Int.dvd_sub h11 h15
    contradiction
  · by_cases h13 : n % 3 = 1
    · have : n ≡ 1 [ZMOD 3] := by
        exact h13
      have h17 : n ^ 2 + n + 2 ≡ 1 ^ 2 + 1 + 2 [ZMOD 3] := by 
        apply Int.ModEq.add
        · apply Int.ModEq.add
          · exact Int.ModEq.pow 2 h13
          · exact this
        · exact Int.ModEq.refl 2
      simp only [one_pow, Int.reduceAdd] at h17
      have h18 : n ^ 2 + n + 2 ≡ 0 [ZMOD 3] := by
        exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int h11)
      have : 4 ≡ 0 [ZMOD 3] := by
        exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h18)) h17)
      contradiction
    · have h19 : n % 3 = 2 := by omega
      have h20 : n ^ 2 + n + 2 ≡ 2 ^ 2 + 2 + 2 [ZMOD 3] := by
        apply Int.ModEq.add
        · apply Int.ModEq.add
          · exact Int.ModEq.pow 2 h19
          · exact h19 
        · exact Int.ModEq.refl 2
      simp only [Int.reducePow, Int.reduceAdd] at h20
      have h21 : n ^ 2 + n + 2 ≡ 0 [ZMOD 3] := by
        exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int h11)
      have : 8 ≡ 0 [ZMOD 3] := by
        exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h21)) h20)
      contradiction
    --and so this equality cannot be true. Therefore our equation has no solutions in integers.