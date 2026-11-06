import Mathlib

/-Find all triples $(a, b, c)$ of integers satisfying $a^{2}+b^{2}+c^{2}=20122012$.-/
theorem number_theory_604726 : 
  {(a, b, c) : ℤ × ℤ × ℤ | a ^ 2 + b ^ 2 + c ^ 2 = 20122012} = ∅ := by
  ext ⟨a, b, c⟩
  simp
  by_contra! h
  -- show that a, b, c are all even
  -- first show that a ^ 2 ≡ 0 [ZMOD 4] or 1 [ZMOD 4]
  have h1 (x : ℤ) : x ^ 2 ≡ 0 [ZMOD 4] ∨ x ^ 2 ≡ 1 [ZMOD 4] := by
    have hx := Int.even_or_odd x
    cases hx with
    | inr hx => -- when Odd x
      simp [Odd] at hx
      obtain ⟨k, hk⟩ := hx
      -- show that x ≡ 1 [ZMOD 4]
      right
      rw [hk]
      simp [Int.modEq_iff_dvd]
      use (-k ^ 2 - k)
      ring_nf
    | inl hx => -- when Even x
      simp [Even] at hx
      obtain ⟨k, hk⟩ := hx
      -- show that x ≡ 0 [ZMOD 4]
      left
      rw [hk]
      simp [Int.modEq_iff_dvd]
      use (k ^ 2)
      ring_nf
  -- show that ¬a ^ 2 + b ^ 2 ≡ 3 [ZMOD 4]
  have h2 (x y : ℤ) : ¬x ^ 2 + y ^ 2 ≡ 3 [ZMOD 4] := by
    by_contra! h2
    -- depend on the case of x, y, we devide the proof into 4 cases
    have hx := h1 x
    have hy := h1 y
    rcases hx with (hx | hx)
    all_goals
      rcases hy with (hy | hy)
    -- for all the case, show that x ^ 2 + y ^ 2 ≠ 3 [ZMOD 4]
    all_goals
      have hxy := Int.ModEq.add hx hy
      simp at hxy
      replace hxy := Int.ModEq.trans hxy.symm h2
      contradiction
  -- show that a is even when a ^ 2 + b ^ 2 + c ^ 2 ≡ 0 [ZMOD 4]
  have h3 (x y z : ℤ) (h : x ^ 2 + y ^ 2 + z ^ 2 ≡ 0 [ZMOD 4]) : Even x := by
    -- proof by contradiction
    by_contra! hx
    -- show that x = 2k + 1
    simp [Odd] at hx
    obtain ⟨k, hk⟩ := hx
    -- show that y ^ 2 + z ^ 2 ≡ 3 [ZMOD 4], so that we get a contradiction
    rw [hk] at h
    have _ : y ^ 2 + z ^ 2 ≡ 3 [ZMOD 4] := by
      calc
        y ^ 2 + z ^ 2 ≡ ((2 * k + 1) ^ 2 + y ^ 2 + z ^ 2) - (2 * k + 1) ^ 2 [ZMOD 4] := by ring_nf; simp
        _ ≡ -(2 * k + 1) ^ 2 [ZMOD 4] := by rw [Int.modEq_iff_dvd] at h ⊢; ring_nf at h ⊢; exact h
        _ ≡ -(4 * k ^ 2 + 4 * k + 1) [ZMOD 4] := by ring_nf; simp
        _ ≡ 3 [ZMOD 4] := by rw [Int.modEq_iff_dvd]; use (1 + k ^ 2 + k); ring_nf
    have _ := h2 y z
    contradiction -- contradiction
  -- show that a ^ 2 + b ^ 2 + c ^ 2 ≡ 0 [ZMOD 4]
  have h' : a ^ 2 + b ^ 2 + c ^ 2 ≡ 0 [ZMOD 4] := by
    calc
      a ^ 2 + b ^ 2 + c ^ 2 ≡ 20122012 [ZMOD 4] := by rw [h]
      _ ≡ 0 [ZMOD 4] := by rw [Int.modEq_iff_dvd]; norm_num
  -- so that a, b and c are all even
  have ha := h3 a b c h'
  have hb := h3 b a c (show b ^ 2 + a ^ 2 + c ^ 2 ≡ 0 [ZMOD 4] by ring_nf at h' ⊢; exact h')
  have hc := h3 c a b (show c ^ 2 + a ^ 2 + b ^ 2 ≡ 0 [ZMOD 4] by ring_nf at h' ⊢; exact h')
  clear h3
  -- simplify the expression to a1 ^ 2 + b1 ^ 2 + c1 ^ 2 = 5030503
  simp [Even] at ha hb hc
  obtain ⟨a1, ha1⟩ := ha
  obtain ⟨b1, hb1⟩ := hb
  obtain ⟨c1, hc1⟩ := hc
  replace h : a1 ^ 2 + b1 ^ 2 + c1 ^ 2 = 5030503 := by
    rw [ha1, hb1, hc1] at h
    linarith only [h]
  clear ha1 hb1 hc1
  -- simutanously show that a1 ^ 2 + b1 ^ 2 + c1 ^ 2 ≡ 7 [ZMOD 8]
  replace h' : a1 ^ 2 + b1 ^ 2 + c1 ^ 2 ≡ 7 [ZMOD 8] := by
    rw [h]
    rw [Int.modEq_iff_dvd]
    norm_num
  -- show that a ^ 2 ≡ 0 or 1 or 4 [ZMOD 8]
  replace h1 (x : ℤ) : x ^ 2 ≡ 0 [ZMOD 8] ∨ x ^ 2 ≡ 1 [ZMOD 8] ∨ x ^ 2 ≡ 4 [ZMOD 8] := by
    have hx := Int.even_or_odd x
    -- show that ∃r, n * (n + 1) = r + r
    have hsucc := Int.even_mul_succ_self
    simp [Even] at hsucc
    -- develop the case of x (Odd or Even)
    cases hx with
    | inr hx => -- when Odd x
      simp [Odd] at hx
      obtain ⟨k, hk⟩ := hx
      -- show that x ≡ 1 [ZMOD 8]
      right; left
      rw [hk]
      simp [Int.modEq_iff_dvd]
      have hsucc := hsucc k -- get r + r = k * (k + 1)
      obtain ⟨r, hr⟩ := hsucc
      use (-r)
      linarith only [hr]
    | inl hx => -- when Even x
      simp [Even] at hx
      obtain ⟨k, hk⟩ := hx
      have hk' := Int.even_or_odd k
      -- devide the case of k (Odd or Even)
      cases hk' with
      | inr hk' => -- when Odd k
        simp [Odd] at hk'
        obtain ⟨r, hr⟩ := hk'
        -- show that x ≡ 4 [ZMOD 8]
        right; right
        rw [hk, hr]
        simp [Int.modEq_iff_dvd]
        use (-2 * (r ^ 2 + r))
        ring_nf
      | inl hk' => -- when Even k
        simp [Even] at hk'
        obtain ⟨r, hr⟩ := hk'
        -- show that x ≡ 0 [ZMOD 8]
        left
        rw [hk, hr]
        simp [Int.modEq_iff_dvd]
        use (2 * r ^ 2)
        ring_nf
  replace h2 (x y z : ℤ) : ¬x ^ 2 + y ^ 2 + z ^ 2 ≡ 7 [ZMOD 8] := by
    by_contra! h2
    -- depend on the case of x, y, z, we devide the proof into 27 cases
    have hx := h1 x
    have hy := h1 y
    have hz := h1 z
    rcases hx with (hx | hx | hx)
    all_goals
      rcases hy with (hy | hy | hy)
    all_goals
      rcases hz with (hz | hz | hz)
    -- for all the case, show that x ^ 2 + y ^ 2 + z ^ 2 ≠ 7 [ZMOD 8]
    all_goals
      have hxyz := Int.ModEq.add (Int.ModEq.add hx hy) hz
      simp at hxyz
      replace hxyz := Int.ModEq.trans hxyz.symm h2
      contradiction
  -- finally get the contradiction
  specialize h2 a1 b1 c1
  contradiction