import Mathlib

/- (3) For the number $(3+\sqrt{8})^{2 n}\left(n \in \mathbf{N}^{*}\right.$ and $\left.n \geqslant 2009\right)$, let $[x]$ be the integer part of $x$. Then the remainder when $\left[(3+\sqrt{8})^{2 n}\right]$ is divided by 8 is $(\quad)$.
(A) 1
(B) 3
(C) 4
(D) 7 -/
theorem number_theory_248527 (n : ℕ) (hn : n ≥ 2009) :
    (Nat.floor ((3 + Real.sqrt 8)^(2 * n))) % 8 = 1 := by
  -- Let a = (3 + √8)^2
  set a := (3 + √8) ^ 2
  -- Let b = (3 - √8)^2
  set b := (3 - √8) ^ 2
  -- Define s(k) = a^k + b^k.
  set s : ℕ → ℝ := fun k => a ^ k + b ^ k
  -- We need to compute ⌊a^(2 * n)⌋ % 8 = ⌊s(n) - b^n⌋.
  -- We have a + b = 100.
  have hab1 : a + b = 34 := by
    dsimp [a, b]
    ring_nf
    repeat rw [Real.sq_sqrt (by norm_num)]
    norm_num
  -- We have a * b = 1.
  have hab2 : a * b = 1 := by
    dsimp [a, b]
    rw [← mul_pow, ← sq_sub_sq]
    repeat rw [Real.sq_sqrt (by norm_num)]
    norm_num
  -- Prove the following recursive formula for s:
  -- s (k + 2) = 34 * s (k + 1) - s k
  have hs k : s (k + 2) = 34 * s (k + 1) - s k := by
    -- The result follows from the definition of s(n):
    -- s(k + 2) = a^(k + 2) + b^(k + 2) = (a + b) * (a^(k + 1) + b^(k + 1)) - a * b * (a^k + b^k)
    --          = 34 * s(k + 1) - s(k).
    rw [← one_mul (s k), ← hab1, ← hab2]
    simp_rw [s]
    ring
  -- Show that s(k) is an integer for all k and s(k) % 8 = 2 for all k.
  let rec h : (k : ℕ) → ∃ n : ℤ, s k = n ∧ n % 8 = 2
  | 0 => by
    -- If k = 0 then s(0) = 2 and s(0) % 8 = 2.
    use 2
    simp [s]
    norm_num
  | 1 => by
    -- If k = 1 then s(1) = a + b = 34.
    use 34
    simp [s, hab1]
  | k + 2 => by
    -- Consider k + 2.
    -- We have s(k) = n0 and s(k + 1) = n1 for some integers n0 and n1.
    -- Moreover, n0 % 8 = 2 and n1 % 8 = 2.
    have ⟨n0, hs0, hn0⟩ := h k
    have ⟨n1, hs1, hn1⟩ := h (k + 1)
    -- Show that s(k + 2) = 34 * n1 - n0.
    use 34 * n1 - n0
    -- This follows from the recursive formula for s.
    simp [hs, hs0, hs1]
    rw [Int.sub_emod, hn0, Int.mul_emod, hn1]
    norm_num
  -- Consider s(n) = k, k % 8 = 2.
  have ⟨k, hsk, hk⟩ := h n
  zify
  rw [Int.natCast_floor_eq_floor (by positivity)]
  -- It is enough to show that ⌊(3 + √8)^(2 * n)⌋ = k - 1.
  suffices ⌊(3 + √8) ^ (2 * n)⌋ = k - 1 by
    rw [this, Int.sub_emod, hk]
    norm_num
  calc
    -- We have ⌊(3 + √8)^(2 * n)⌋ = ⌊s(n) - b^n⌋.
    ⌊(3 + √8) ^ (2 * n)⌋ = ⌊s n - b ^ n⌋ := by
        congr
        simp [s, a, ← pow_mul]
    -- ⌊s(n) - b^n⌋ = k + ⌊-b^n⌋ (because s(n) = k ∈ ℤ).
    _ = k + ⌊-(b ^ n)⌋ := by
        simp [hsk, sub_eq_add_neg]
    -- It is left to show that ⌊-(b^n)⌋ = -1.
    _ = k - 1 := by
        congr
        -- To show that ⌊-b^n⌋ = -1 we have to show that 0 < b^n ≤ 1.
        simp [Int.floor_eq_iff]
        constructor
        · simp [b]
          -- Show that b^n ≤ 1.
          -- We need to show that b = (3 - √8)^2 ≤ 1.
          rw [pow_le_one_iff_of_nonneg (by positivity) (by linarith)]
          ring_nf
          repeat rw [Real.sq_sqrt (by positivity)]
          -- It is enough to show that 16 / 6 ≤ √8.
          suffices 16 / 6 ≤ √8 by linarith
          rw [← sq_le_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity)]
          norm_num
        -- Show that 0 < b^n.
        · simp [b, ← pow_mul]
          -- It is enough to show that 0 < 3 - √8
          apply pow_pos
          rw [sub_pos, show 3 = √(3 ^ 2) by simp]
          apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)