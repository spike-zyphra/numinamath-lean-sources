import Mathlib

/- 44th Putnam 1983 Problem B4 Let f(n) = n + [√n]. Define the sequence a i by a 0 = m, a n+1 = f(a n ). Prove that it contains at least one square. -/
theorem number_theory_145831 {f : ℕ → ℕ} (hf : ∀ n, f n = n + ⌊Real.sqrt n⌋)
    (m : ℕ) (a : ℕ → ℕ) (ha0 : a 0 = m) (han : ∀ n, a (n + 1) = f (a n)) :
    ∃ i, IsSquare (a i) := by
  -- f(n) = n + ⌊√n⌋ can be written as f(n) = n + n.sqrt
  replace hf : ∀ n, f n = n + n.sqrt := by
    intro n
    specialize hf n
    rw [Real.floor_real_sqrt_eq_nat_sqrt] at hf
    zify
    exact hf
  -- Find q and r such that m = q * q + r and r ≤ 2q.
  have ⟨q, r, hm, hr⟩ : ∃ q r, m = q * q + r ∧ r ≤ 2 * q := by
    -- Take q = m.sqrt and r = m - m.sqrt^2.
    use m.sqrt, m - m.sqrt * m.sqrt
    -- We have m.sqrt^2 ≤ m for all m.
    have := Nat.sqrt_le m
    constructor
    · omega
    · rw [Nat.sub_le_iff_le_add]
      -- We need to show m ≤ m.sqrt^2 + 2 * m.sqrt.
      -- It is enough to show that m < m.sqrt^2 + 2 * m.sqrt + 1 = (m.sqrt + 1)^2.
      suffices m < m.sqrt * m.sqrt + 2 * m.sqrt + 1 by omega
      rw [show m.sqrt * m.sqrt + 2 * m.sqrt + 1 = (m.sqrt + 1) * (m.sqrt + 1) by ring]
      -- m < (m.sqrt + 1)^2 for all m.
      exact Nat.lt_succ_sqrt m
  -- Use strong induction on r to prove that there exists i such that a(i) is a square.
  induction r using Nat.strongRec generalizing m q a with
  | ind r ih =>
    -- Assume that everything holds for all x < r and for all m', q', a' such that
    -- a(0) = m', m' = q' * q' + x and a'(n + 1) = f(a'(n)).
    -- Show that the result holds for a with a(0) = m = q * q + r.
    -- Consider 3 cases: r = 0, r ∈ [1, q], and r ∈ [q + 1, 2 * q].
    rcases show r = 0 ∨ 0 < r ∧ r ≤ q ∨ q < r ∧ q ≤ 2 * q by omega with h | h | h
    -- If r = 0 then a(0) = m = q * q is a square.
    · use 0, q
      rw [ha0, hm, h, add_zero]
    -- If 1 ≤ r ≤ q then
    -- a(1) = f(q^2 + r) = q^2 + r + (q^2 + r).sqrt = q^2 + r + q (because r ≤ 2q).
    -- a(2) = f(q^2 + (r + q)) = q^2 + r + q + (q^2 + (r + q)).sqrt = q^2 + r + q + q (because r + q ≤ 2q).
    --      = (q + 1)^2 + (r - 1).
    · have ha2 : a 2 = (q + 1) * (q + 1) + (r - 1) := by
        have ha1 : a 1 = q * q + (q + r) := by
          rw [han, ha0, hm, hf, Nat.sqrt_add_eq q (by omega)]
          ring
        rw [han, ha1, hf, Nat.sqrt_add_eq q (by omega)]
        zify [h]
        ring
      -- Let a'(i) = a(i + 2) then a'(n + 1) = f(a'(n)) for all n.
      have han' : ∀ n, a ((n + 1) + 2) = f (a (n + 2)) := by simp [han]
      -- Apply the induction hypothesis with x = r - 1 < r, m' = (q + 1)^2 + (r - 1), q' = (q + 1), and a'.
      have ⟨i, hi⟩ := ih (r - 1) (by omega) ((q + 1) * (q + 1) + (r - 1))
                        (fun i => a (i + 2)) ha2 han' (q + 1) rfl (by omega)
      -- We get i such that a'(i) is a square. a'(i) = a(i + 2) so a(i + 2) is a square.
      use i + 2
    -- If q + 1 ≤ r ≤ 2q then
    -- a(1) = f(q^2 + r) = q^2 + r + (q^2 + r).sqrt = q^2 + r + q (because r ≤ 2q)
    --      = (q + 1)^2 + (r - q - 1).
    · have ha1 : a 1 = (q + 1) * (q + 1) + (r - q - 1) := by
        rw [han, ha0, hm, hf, Nat.sqrt_add_eq q (by omega)]
        zify [show r ≥ q ∧ r - q ≥ 1 by omega]
        ring
      -- Let a'(i) = a(i + 1) then a'(n + 1) = f(a'(n)) for all n.
      have han' : ∀ n, a ((n + 1) + 1) = f (a (n + 1)) := by simp [han]
      -- Apply the induction hypothesis with x = r - q - 1 < r, m' = (q + 1)^2 + (r - q - 1),
      -- q' = (q + 1), and a'.
      have ⟨i, hi⟩:= ih (r - q - 1) (by omega) ((q + 1) * (q + 1) + (r - q - 1))
                        (fun i => a (i + 1)) ha1 han' (q + 1) rfl (by omega)
      -- We get i such that a'(i) is a square. a'(i) = a(i + 1) so a(i + 1) is a square.
      use i + 1