import Mathlib

/- Example 11 (25th IMO Shortlist) Find the last two digits of $\left[(\sqrt{29}+\sqrt{21})^{1984}\right]$.

Translate the above text into English, please keep the original text's line breaks and format, and output the translation result directly. -/
theorem number_theory_274181 : (Nat.floor ((Real.sqrt 29 + Real.sqrt 21)^1984)) % 100 = 71 := by
  -- Let a = (√29 + √21)^2
  set a := (√29 + √21) ^ 2
  -- Let b = (√29 - √21)^2
  set b := (√29 - √21) ^ 2
  -- Define s(k) = a^k + b^k.
  set s : ℕ → ℝ := fun k => a ^ k + b ^ k
  -- We need to compute last two digits of ⌊a^992⌋ = ⌊s(992) - b^992⌋.
  -- We have a + b = 100.
  have hab1 : a + b = 100 := by
    dsimp [a, b]
    ring_nf
    repeat rw [Real.sq_sqrt (by norm_num)]
    norm_num
  -- We have a * b = 64.
  have hab2 : a * b = 64 := by
    dsimp [a, b]
    rw [← mul_pow, ← sq_sub_sq]
    repeat rw [Real.sq_sqrt (by norm_num)]
    norm_num
  -- Prove the following recursive formula for s:
  -- s (k + 2) = 100 * s (k + 1) - 64 * s k
  have hs k : s (k + 2) = 100 * s (k + 1) - 64 * s k := by
    -- The result follows from the definition of s(n):
    -- s(k + 2) = a^(k + 2) + b^(k + 2) = (a + b) * (a^(k + 1) + b^(k + 1)) - a * b * (a^k + b^k)
    --          = 100 * s(k + 1) - 64 * s(k).
    rw [← one_mul (s k), ← hab1, ← hab2]
    simp_rw [s]
    ring
  -- Show that s(k) is an integer for all k and s(k) % 100 = 2 * 6^k % 100 for all even k.
  let rec h : (k : ℕ) → ∃ n : ℤ, s k = n ∧ (Odd k ∨ n % 100 = 2 * 6 ^ k % 100)
  | 0 => by
    -- If k = 0 then s(0) = 2 and s(0) % 100 = 2 * 6^0.
    use 2
    simp [s]
    norm_num
  | 1 => by
    -- If k = 1 then s(0) = a + b = 100.
    use 100
    simp [s, hab1]
  | k + 2 => by
    -- Consider k + 2.
    -- We have s(k) = n0 and s(k + 1) = n1 for some integers n0 and n1.
    -- Moreover, if k is even then n0 % 100 = 2 * 6^k % 100.
    have ⟨n0, hs0, hn0⟩ := h k
    have ⟨n1, hs1, hn1⟩ := h (k + 1)
    -- Show that s(k + 2) = 100 * n1 - 64 * n0.
    use 100 * n1 - 64 * n0
    -- This follows from the recursive formula for s.
    simp [hs, hs0, hs1]
    cases' Nat.even_or_odd k with hk hk
    · right
      -- If k is even then k + 2 is also even.
      -- Show that s(k + 2) % 100 = (100 * n1  - 64 * n0) % 100 = 2 * 6^(k + 2) % 100.
      -- We know that n0 % 100 = 2 * 6^k % 100.
      simp_rw [← Nat.not_even_iff_odd, hk, not_true_eq_false, false_or] at hn0
      rw [show (100 : ℤ) = (100 : ℕ) by simp] at hn0 ⊢
      -- Consider identities for s(k + 2) % 100 and n0 % 100 as idenities over ℤ_100.
      rw [← ZMod.intCast_eq_intCast_iff'] at hn0 ⊢
      push_cast at hn0 ⊢
      -- We get s(k + 2) = 100 * n1 - 64 * n0 (mod 100)
      --                 = 100 * n1 - 64 * (2 * 6^k) (mod 100)
      --                 = 36 * (2 * 6^k) (mod 100)
      --                 = 2 * (6^2 * 6^k) (mod 100)
      --                 = 2 * 6^(k + 2) (mod 100).
      rw [hn0, pow_add]
      reduce_mod_char
      ring
    · simp [Odd.add_even hk even_two]
  -- Consider s(992) = n, n % 100 = 2 * 6^992 % 100 = 72.
  have ⟨n, hsn, hn⟩ := h 992
  norm_num at hn
  rw [← Nat.not_even_iff_odd, show 992 = 2 * 496 by norm_num] at hn
  simp only [even_two_mul, not_true_eq_false, false_or] at hn
  zify
  rw [Int.natCast_floor_eq_floor (by positivity)]
  -- It is enough to show that ⌊(√29 + √21) ^ 1984⌋ = n - 1.
  suffices ⌊(√29 + √21) ^ 1984⌋ = n - 1 by
    rw [this, Int.sub_emod, hn]
    norm_num
  calc
    -- We have ⌊(√29 + √21) ^ 1984⌋ = ⌊s(992) - b^992⌋.
    ⌊(√29 + √21) ^ 1984⌋ = ⌊s 992 - b ^ 992⌋ := by
        congr
        simp [s, a, ← pow_mul]
    -- ⌊s(992) - b^992⌋ = n + ⌊-b^992⌋ (because s(992) = n ∈ ℤ).
    _ = n + ⌊-(b ^ 992)⌋ := by
        simp [hsn, sub_eq_add_neg]
    -- It is left to show that ⌊-b^992⌋ = -1.
    _ = n - 1 := by
        congr
        -- To show that ⌊-b^992⌋ = -1 we have to show that 0 < b^992 ≤ -1.
        simp [Int.floor_eq_iff]
        constructor
        · simp [b]
          -- Show that b^992 ≤ 1.
          -- We need to show that b = (√29 - √21)^2 ≤ 1.
          rw [pow_le_one_iff_of_nonneg (by positivity) (by norm_num)]
          ring_nf
          repeat rw [Real.sq_sqrt (by positivity)]
          -- Simplify the expression and get 49 ≤ 2√609
          rw [add_assoc, neg_add_le_iff_le_add, ← sub_le_iff_le_add, ← Real.sqrt_mul (by norm_num)]
          norm_num
          -- Square both sides of 49 ≤ 2√609 and get 49^2 = 2401 ≤ 4 * 609 = 2436.
          apply le_of_sq_le_sq _ (by positivity)
          rw [mul_pow, Real.sq_sqrt (by norm_num)]
          norm_num
        -- Show that 0 < b^992.
        · simp [b, ← pow_mul]
          -- It is enough to show that 0 < √29 - √21.
          apply pow_pos
          rw [sub_pos]
          exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)