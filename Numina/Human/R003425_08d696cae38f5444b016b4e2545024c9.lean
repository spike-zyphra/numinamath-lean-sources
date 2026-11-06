import Mathlib

open Real

-- Show that if a ≠ 0 and a^2 * b is a square, then b is also a square.
theorem lemma_1 {a b k : ℤ} (ha : a ≠ 0) (hk : a^2 * b = k^2) : ∃ m, b = m^2 := by
  -- a² divides k² implies that a divides k
  have h₁ : a ∣ k := by
    have h : a^2 ∣ k^2 := by use b; rw [hk]
    rwa [Int.pow_dvd_pow_iff (by norm_num)] at h
  -- We get k = a * t
  rcases h₁ with ⟨t, rfl⟩
  -- Show that b = t^2.
  use t
  rw [← mul_right_inj' (show a^2 ≠ 0 by positivity)]
  linear_combination hk

/- 1. On the graph of a polynomial function with integer coefficients, two points with integer coordinates are chosen. Prove that if the distance between them is an integer, then the segment connecting them is parallel to the x-axis. -/
theorem number_theory_179506 {P : Polynomial ℤ}
    (x1 x2 : ℤ) (y1 y2 : ℤ) (h1 : P.eval x1 = y1) (h2 : P.eval x2 = y2)
    (h3 : ∃ d : ℤ, sqrt ((x2 - x1)^2 + (y2 - y1)^2) = d) :
    y1 = y2 := by
  -- We have x2 - x1 ∣ P(x2) - P(x1), so y2 - y1 = k * (x2 - x1) for some k ∈ ℤ.
  have ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub x2 x1 P
  rw [h1, h2] at hk
  have ⟨d, hd⟩ := h3
  -- We get (x2 - x1)^2 * (1 + k^2) = d^2 for d ∈ ℤ.
  have h : (x2 - x1)^2 * (1 + k^2) = d^2 := by
    rify at hk ⊢
    apply_fun (· ^ 2) at hd
    rw [← hd, sq_sqrt (by positivity), hk]
    ring
  by_cases hx : x1 = x2
  · -- If x1 = x2 then y1 = y2.
    subst x1
    rw [← h1, ← h2]
  -- Assume that x1 ≠ x2.
  -- lemma_1 implies that 1 + k^2 = m^2 for some m.
  replace ⟨m, hm⟩ := lemma_1 (by contrapose! hx; linarith) h
  -- Show that k = 0.
  have hk0 : k = 0 := by
    -- We can rewrite 1 + k^2 = m^2 as 1 + |k|^2 + |m|^2.
    replace hm : 1 + k.natAbs ^ 2 = m.natAbs ^ 2 := by
      zify
      simp_rw [sq_abs, hm]
    have h1 := congr_arg Nat.sqrt hm
    -- Assume that k ≠ 0 and show that 1 + |k|^2 ≠ |m|^2.
    contrapose! hm
    -- We have |k| ≠ 0.
    replace hm : k.natAbs ≠ 0 := by
      zify
      simp [hm]
    -- We have Nat.sqrt (1 + |k|^2) = |k| (because 1 ≤ 2 * |k|)
    -- and Nat.sqrt (|m|^2) = |m|.
    -- So |k| = |m|.
    rw [add_comm, Nat.sqrt_add_eq' _ (by omega), Nat.sqrt_eq'] at h1
    -- |k| = |m| implies that 1 + |k|^2 ≠ |m|^2.
    rw [h1]
    linarith
  -- k = 0 implies that y2 - y1 = 0, y1 = y2.
  subst k
  linarith