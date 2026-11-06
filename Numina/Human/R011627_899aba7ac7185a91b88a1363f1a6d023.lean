import Mathlib

-- Show that (√a + b)^(2n + 1) - (√a - b)^(2n + 1) is an integer for all natural
-- numbers a, b, and n.
lemma lemma_1 (a b n : ℕ) : ∃ k : ℤ, (√a + b)^(2 * n + 1) - (√a - b)^(2 * n + 1) = k := by
  -- Prove a stronger statement:
  -- (√a + b)^(2 * n + 1) - (√a - b)^(2 * n + 1) = s for some integer s and
  -- (√a + b)^(2 * n + 1) + (√a - b)^(2 * n + 1) = p * √a for some integer p.
  suffices ∃ s p : ℤ, (√a + b)^(2 * n + 1) - (√a - b)^(2 * n + 1) = s ∧ (√a + b)^(2 * n + 1) + (√a - b)^(2 * n + 1) = p * √a by
    tauto
  -- Proof by induction
  induction n with
  -- If n = 0 then s = 2 * b and p = 2.
  | zero => use 2 * b, 2; simp [two_mul]
  | succ n ih =>
    -- Consider 2 * (n + 1) + 1.
    -- Let x = (√a + b) ^ (2 * n + 1) and y = (√a - b) ^ (2 * n + 1).
    -- The induction hypothesis implies that x - y = s and x + y = p * √a with s, p ∈ ℤ
    have ⟨s, p, h1, h2⟩ := ih
    set x := (√a + b) ^ (2 * n + 1) with hx
    set y := (√a - b) ^ (2 * n + 1) with hy
    -- Show that p' = (a + b^2) * s + 2 * b * (a * p) and s' = (a + b^2) * p + 2 * b * s
    -- work for 2 * (n + 1) + 1.
    use (a + b^2) * s + 2 * b * (a * p), (a + b^2) * p + 2 * b * s
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add (n := 2)]
    rw [← hx, pow_add, ← hy]
    push_cast
    rw [show (√a + b)^2 = a + b^2 + 2 * b * √a by ring_nf; simp; ring_nf]
    rw [show (√a - b)^2 = a + b^2 - 2 * b * √a by ring_nf; simp; ring_nf]
    constructor
    · calc
        _ = (x - y) * (a + b^2) + 2 * b * (√a * (x + y)) := by ring
        _ = (a + b^2) * s + 2 * b * (a * p) := by
          rw [h1, h2, show √a * (p * √a) = a * p by ring_nf; simp [mul_comm], mul_comm]
    · calc
        _ = (x + y) * (a + b^2) + 2 * b * √a * (x - y) := by ring
        _ = ((a + b^2) * p + 2 * b * s) * √a := by
          rw [h1, h2]
          ring

-- Show that 1 < ⌊(√10 + 3)^n⌋ for all n ≠ 0.
lemma lemma_2 {n : ℕ} (hn : n ≠ 0) : 1 < ⌊(√10 + 3)^n⌋ := by
  -- It is necessary to show that 2 ≤ (√10 + 3)^n.
  simp [Int.lt_floor_iff]
  -- Show that 2 ≤ √10 + 3 ≤ (√10 + 3)^n.
  trans √10 + 3
  · rw [← sub_nonneg, show √10 + 3 - (1 + 1) = 1 + √10 by ring]
    positivity
  · apply le_self_pow₀ _ hn
    rw [← sub_nonneg, show √10 + 3 - 1 = 2 + √10 by ring]
    positivity

-- Let x be a real number. Show that |x| < 1 and x is an integer imply that x = 0.
lemma lemma_3 {x : ℝ} {k : ℤ} (hx : |x| < 1) (hxk : x = k) : x = 0 := by
  rw [abs_lt] at hx
  -- Consider three cases: k < 0, k = 0, and 0 < k.
  rcases lt_trichotomy k 0 with h | h | h
  -- If k < 0 then k ≤ -1 and |x| ≥ 1, a contradiction.
  · replace h : k ≤ -1 := by omega
    rify at h
    linarith
  -- If k = 0 then x = 0.
  · simp [hxk, h]
  -- If 0 < k then 1 ≤ k and |x| ≥ 1, a contradiction.
  · replace h : 1 ≤ k := by omega
    rify at h
    linarith

/- 8. The integer part and decimal part of $(\sqrt{10}+3)^{2 n+1}(n \in \mathbf{N})$ are $I$ and $F$, respectively, then the value of $P(I$ $+F)$ is $\qquad$ -/
theorem number_theory_295118 (n : ℕ) (I F : ℝ)
    (hI : I = ⌊(√10 + 3)^(2 * n + 1)⌋)
    (hF : F = Int.fract ((√10 + 3)^(2 * n + 1))) :
    F * (I + F) = 1 := by
  -- lemma_1 implies that (√10 + 3)^(2 * n + 1) - (√10 - 3)^(2 * n + 1) = k with k ∈ ℤ.
  have ⟨k, hk⟩ := lemma_1 10 3 n
  push_cast at hk
  -- Let x = (√10 + 3)^(2 * n + 1) and y = (√10 - 3)^(2 * n + 1).
  set x := (√10 + 3)^(2 * n + 1)
  set y := (√10 - 3)^(2 * n + 1)
  -- We have x = I + F.
  have hx : x = I + F := by rw [hI, hF, Int.floor_add_fract]
  -- Show that x * y = 1.
  have eq1 : x * y = 1 := by
    -- The result follows from (√10 + 3) * (√10 - 3) = 1.
    simp_rw [x, y, ← mul_pow, ← sq_sub_sq, Real.sq_sqrt (x := 10) (by norm_num)]
    norm_num
  -- Show that 1 < I + F.
  have hineq1 : 1 < I + F := by
    -- It is enough to show that I = ⌊x⌋ > 1 because F ≥ 0.
    suffices 1 < ⌊x⌋ by
      rify at this
      linarith [Int.fract_nonneg x]
    -- The result follows from lemma_2 since 2 * n + 1 ≠ 0.
    apply lemma_2 (by omega)
  -- Show that |F - 1 / (I + F)| < 1.
  have hineq : |F - 1 / (I + F)| < 1 := by
    -- We have 0 ≤ F < 1.
    have h1 := Int.fract_nonneg x
    have h2 := Int.fract_lt_one x
    -- It is enough to show that 0 < 1 / (I + F) < 1.
    suffices 0 < 1 / (I + F) ∧ 1 / (I + F) < 1 by
      rw [abs_lt]
      constructor <;> linarith
    -- 1 < I + F implies that 1 / (I + F) < 1 and 0 < 1 / (I + F).
    refine ⟨div_pos (by norm_num) (by linarith), ?_⟩
    rw [div_lt_one] <;> linarith
  -- F * (I + F) = 1 follows from F - 1 / (I + F) = 0.
  suffices F - 1 / (I + F) = 0 by
    field_simp at this
    linarith
  -- We proved that |F - 1 / (I + F)| < 1 so we can apply lemma_3 to F - 1 / (I + F).
  apply lemma_3 (k := k - ⌊x⌋) hineq
  -- It is left to show that F - 1 / (I + F) = k - I.
  field_simp [← hx, ← hk, sub_mul, mul_comm y, eq1]
  rw [show F = x - ⌊x⌋ by linarith]
  ring