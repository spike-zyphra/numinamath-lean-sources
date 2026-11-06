import Mathlib

/- A strictly increasing sequence of positive integers a1​, a2​, a3​, ⋯
has the property that for every positive integer k, the subsequence a_{2k−1}​, a_{2k}​, a_{2k+1}
is geometric and the subsequence a_{2k}​, a_{2k+1}​, a_{2k+2}​ is arithmetic.
Suppose that a13=2016. Find a1​. -/
theorem algebra_96560 (a : ℕ → ℤ) (ha : StrictMono a) (hpos : ∀ n > 0, 0 < a n)
    (hge : ∀ k > 0, ∃ r : ℚ, a (2 * k - 1) * r = a (2 * k) ∧ a (2 * k) * r = a (2 * k + 1))
    (har : ∀ k > 0, ∃ d, a (2 * k) + d = a (2 * k + 1) ∧ a (2 * k + 1) + d = a (2 * k + 2)) :
    a 13 = 2016 → a 1 = 504 := by
  -- a (2 * k), a (2 * k + 1), a (2 * k + 2) form an arithmetic sequence
  -- so we get a (2 * k + 2) = 2 * a (2 * k + 1) - a (2 * k).
  replace har : ∀ k > 0, a (2 * k + 2) = 2 * a (2 * k + 1) - a (2 * k) := by
    intro k hk
    have ⟨d, hd1, hd2⟩ := har k hk
    linarith
  -- We have a 2 = r * a 1 and a 3 = r * a 2 for some r ∈ ℚ.
  have ⟨r, hr⟩ := hge 1 zero_lt_one
  norm_num at hr
  -- Let x = a 1.
  set x := a 1 with hx
  -- Clearly, 0 < x.
  have hx_pos : 0 < x := hpos 1 zero_lt_one
  -- 1 < r because the sequence is strictly increasing and a 2 = r * a 1.
  have hr1 : 1 < r := by
    have h12 := ha one_lt_two
    qify at h12 hx_pos
    nlinarith
  -- Prove that a (2 * n + 1) = (n * r - (n - 1)) ^ 2 * x and a (2 * n + 2) = ((n + 1) * r - n) * (n * r - (n - 1)) * x
  -- for all n.
  have h (n : ℕ) : a (2 * n + 1) = (n * r - (n - 1)) ^ 2 * x ∧ a (2 * n + 2) = ((n + 1) * r - n) * (n * r - (n - 1)) * x := by
    -- A proof by induction.
    induction n with
    -- n = 0 is trivial.
    | zero => norm_num [← hr.1, mul_comm]
    -- Assume that the induction hypothesis holds for n and prove the result for n + 1.
    | succ n ih =>
      -- We have a (2 * (n + 1)) = y * a (2 * n + 1) and a (2 * (n + 1) + 1) = y * a (2 * (n + 1)).
      have ⟨y, hy1, hy2⟩ := hge (n + 1) (by omega)
      have ⟨h1, h2⟩ := ih
      push_cast
      rw [show 2 * n + 2 = 2 * (n + 1) by omega] at h2
      rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega] at hy1
      -- Show that y * (n * r - (n - 1)) = (n + 1) * r - n.
      have hy : y * (n * r - (n - 1)) = (n + 1) * r - n := by
        have := hpos (2 * n + 1) (by omega)
        qify at this
        apply mul_left_cancel₀ (ne_of_gt this)
        -- The result follows from the induction hypothesis.
        rw [← mul_assoc, hy1, h1, h2]
        ring
      -- Now show that a (2 * (n + 1) + 1) = ((n + 1) * r - n) ^ 2 * x
      have eq1 : a (2 * (n + 1) + 1) = ((n + 1) * r - n) ^ 2 * x := by
        rw [← hy2, h2]
        have : n * r - (n - 1) ≠ 0 := by
          apply ne_of_gt
          nlinarith
        apply mul_right_cancel₀ this
        simp_rw [mul_assoc, hy]
        ring
      simp_rw [show (n : ℚ) + 1 - 1 = n by linarith, ←eq1, true_and]
      -- It is left to show that a (2 * (n + 1) + 2) = ((n + 2) * r - (n + 1)) * ((n + 1) * r - n) * x.
      -- We know that a (2 * (n + 1) + 2) = 2 * a (2 * (n + 1) + 1) - a (2 * (n + 1))
      -- and the result follows from the expressions for a (2 * (n + 1) + 1) and a (2 * (n + 1)).
      rw [har (n + 1) (by omega)]
      push_cast
      rw [eq1, h2]
      ring
  qify
  -- Use the previous result to prove that a 13 = a (2 * 6 + 1) = (6 * r - 5) ^ 2 * x.
  have ha13 : a 13 = (6 * r - 5) ^ 2 * x := by
    rw [show 13 = 2 * 6 + 1 by norm_num, (h 6).1]
    norm_num
  rw [ha13]
  intro h
  clear * - h hr1 hx_pos hr hpos
  -- Let p = |r.num| (the absolute value of the numerator of r).
  set p := r.num.natAbs
  -- Let q = r.den (the denominator of r).
  set q := r.den
  -- Let x' = |x|.
  set x' := x.natAbs
  -- It is easy to show that x = x' because x = a 1 > 0.
  have hx' : x = x' := by simp_rw [x', Int.natAbs_of_nonneg (le_of_lt hx_pos)]
  -- We have r = p / q because r > 0.
  have hrpq : r = p / q := by
    have hp : p = r.num := by
      dsimp [p]
      rw [Int.natAbs_of_nonneg]
      rw [Rat.num_nonneg]
      linarith
    rw [← Rat.num_div_den r, ←hp]
    simp only [Int.cast_natCast, q]
  -- p and q are coprime.
  have hpq : p.Coprime q := r.reduced
  have hq_pos : 0 < q := Rat.den_pos r
  -- Show that q ^ 2 divides x'.
  have hqx : q ^ 2 ∣ x' := by
    -- We have a 3 = r ^ 2 * x' = (p / q) ^ 2 * x'.
    have eq1 : a 3 = ((p : ℚ) / q) ^ 2 * x' := by
      rw [← hr.2, ← hr.1, hx', hrpq]
      norm_cast
      ring
    -- We have p ^ 2 * a 3 = q ^ 2 * x'.
    field_simp at eq1
    -- a 3 is a positive integer.
    lift a 3 to ℕ using (le_of_lt $ hpos 3 (by norm_num)) with z
    norm_cast at eq1
    -- q ^ 2 divides p ^ 2 * x'
    have : q ^ 2 ∣ p ^ 2 * x' := by use z; rw [← eq1]; ring
    -- p and q are coprime, so q ^ 2 must divide x'.
    exact (hpq.symm.pow 2 2).dvd_of_dvd_mul_left this
  -- 1 < r = p / q implies that q < p (or q + 1 ≤ p).
  have hpq1 : q + 1 ≤ p := by
    suffices q < p by omega
    rw [hrpq, one_lt_div (by norm_cast)] at hr1
    qify
    exact hr1
  -- We have the inequality 7 ≤ 6 * p - 5 * q
  -- (it follows from 6 * p - 5 * q ≥ 6 * (q + 1) - 5 * q = q + 6 ≥ 7).
  have hpq2 : 7 ≤ 6 * p - 5 * q := by omega
  -- Show that (6 * p - 5 * q) ^ 2 divides 2016
  have hsq : (6 * p - 5 * q) ^ 2 ∣ 2016 := by
    have ⟨k, hk⟩ := hqx
    -- 2016 = a 13 = (6 * r - 5) ^ 2 * x so
    -- (6 * p - 5 * q) ^ 2 * x = 2016 * q ^ 2.
    -- We proved that q ^ 2 divides x' and x = x', so we get
    -- (6 * p - 5 * q) ^ 2 * (q ^ 2 * k) = 2016 * q ^ 2 for some k.
    field_simp [hrpq, hx', hk] at h
    rw [mul_comm _ (k : ℚ), ← mul_assoc] at h
    have hq : (q : ℚ) ^ 2 ≠ 0 := by
      have : q ≠ 0 := ne_of_gt hq_pos
      contrapose! this
      rw [← sq_eq_zero_iff]
      qify
      exact this
    -- Cancel q ^ 2 ≠ 0 and get (6 * p - 5 * q) ^ 2 * k = 2016.
    apply mul_right_cancel₀ hq at h
    -- We conclude that (6 * p - 5 * q) ^ 2 divides 2016
    use k
    qify [show 5 * q ≤ 6 * p by omega]
    linear_combination -h
  -- Consider divisors d of 2016 such that 7^2 ≤ d and d is a square.
  set ds := Finset.filter (fun d => 49 ≤ d ∧ IsSquare d) (2016).divisors
  -- It is easy to see that (6 * p - 5 * q) ^ 2 ∈ ds (because 7 ≤ 6 * p - 5 * q).
  have hpq3 : (6 * p - 5 * q) ^ 2 ∈ ds := by
    simp [ds, hsq, IsSquare.sq]
    rw [show 49 = 7 ^ 2 by norm_num, sq_le_sq₀ (by norm_num) (Nat.zero_le _)]
    exact hpq2
  -- Compute that ds = {144} = {12^2}.
  have hds_eq : ds = {12 ^ 2} := by native_decide
  -- We get 6 * p - 5 * q = 12.
  simp only [hds_eq, Finset.mem_singleton] at hpq3
  rw [sq_eq_sq₀ (Nat.zero_le _) (by norm_num)] at hpq3
  -- The equation 6 * p - 5 * q = 12 has only one solution with 0 < q < p:
  -- q = 6 and p = 7.
  have hq : q = 6 := by omega
  have hp : p = 7 := by omega
  -- We get r = 7 / 6, so 4 * x = 2016 and x = 504.
  rw [hrpq, hp, hq] at h
  norm_num at h
  linarith