import Mathlib

open Real

/- 12. For any positive integer $n$, prove: $\arctan \frac{1}{2}+\arctan \frac{1}{8}+\cdots+\arctan \frac{1}{2 n^{2}}=$ $\arctan \frac{n}{n+1}$. -/
theorem algebra_234889' (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, arctan (1 / (2 * i ^ 2)) = arctan (n / (n + 1)) := by
  -- The result holds for n = 0 so we do not assume that 0 < n.
  -- Proof by induction on n.
  induction n with
  -- If n = 0 then the result follows from arctan 0 = 0.
  | zero => simp
  | succ n ih =>
    -- Consider n + 1.
    -- We have ∑ i ∈ [1, n + 1], arctan (1/(2*i^2))
    --    = ∑ i ∈ [1, n], arctan (1/(2*i^2)) + arctan (1/(2*(n + 1)^2))
    --    = arctan (n / (n + 1)) + arctan (1/(2*(n + 1)^2)) (by the induction hypothesis).
    -- We need to show that
    -- arctan (n / (n + 1)) + arctan (1/(2*(n + 1)^2)) = arctan ((n + 1) / (n + 2)).
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    /- A short proof which uses the formula for the sum of arctans:
    push_cast [add_assoc, show (1 + 1 : ℝ) = 2 by norm_num]
    have ineq : 0 < (n + 1 : ℝ) * (2 * (n + 1) ^ 2) - n := by
      rw [sub_pos]
      norm_cast
      ring_nf
      nlinarith
    rw [arctan_add]
    · congr 1
      field_simp [ineq]
      ring
    · field_simp
      rw [div_lt_one (by positivity), ← sub_pos]
      exact ineq
    -/
    -- Rewrite the goal as
    -- arctan (1/(2*(n + 1)^2)) = arctan ((n + 1) / (n + 2)) - arctan (n / (n + 1)).
    rw [show ∀ a b c : ℝ, a + b = c ↔ b = c - a by intros; constructor <;> intros <;> linarith]
    push_cast [add_assoc, show (1 + 1 : ℝ) = 2 by norm_num]
    -- Let x = n / (n + 1).
    set x := (n : ℝ) / (n + 1)
    -- Let y = (n + 1) / (n + 2).
    set y := (n + 1 : ℝ) / (n + 2)
    -- We have x < y.
    have hxy : x < y := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    -- We have arctan y - arctan x < π / 2 (because 0 < arctan x and arctan y < π / 2).
    have h1 : arctan y - arctan x < π / 2 := by
      suffices 0 ≤ arctan x by linarith [arctan_lt_pi_div_two y]
      rw [← arctan_zero]
      apply arctan_strictMono.monotone
      positivity
    -- We have 0 < arctan y - arctan x (because x < y).
    have h2 : 0 < arctan y - arctan x := by
      rw [sub_pos]
      exact arctan_strictMono hxy
    -- For all t and integer k we have arctan t ≠ (2 * k + 1) * π / 2.
    have h3 t : ∀ k : ℤ, arctan t ≠ (2 * k + 1) * π / 2 := by
      intro k
      have h3 := neg_pi_div_two_lt_arctan t
      have h4 := arctan_lt_pi_div_two t
      -- Consider 2 cases: k < 0, k ≥ 0.
      rcases show k < 0 ∨ k ≥ 0 by omega with hk | hk
      -- If k < 0 then (2 * k + 1) ≤ -1, so (2 * k + 1) * π / 2 ≤ -π / 2 < arctan t.
      · apply ne_of_gt
        suffices (2 * k + 1) * π / 2 ≤ (-1) * π / 2 by linarith
        gcongr
        norm_cast
        simp
        omega
      -- If k ≥ 0 then (2 * k + 1) * π / 2 ≥ π / 2 > arctan t.
      · apply ne_of_lt
        suffices 1 * π / 2 ≤ (2 * k + 1) * π / 2 by linarith
        gcongr
        rify at hk
        linarith
    -- tan is injective on (-π / 2, π / 2), so the goal is equivalent to
    -- tan (arctan (1 / (2 * (↑n + 1) ^ 2))) = tan (arctan y - arctan x).
    apply tan_inj_of_lt_of_lt_pi_div_two (neg_pi_div_two_lt_arctan _) (arctan_lt_pi_div_two _) (by linarith) h1
    -- tan (arctan t) = t for all t.
    rw [tan_arctan, show ∀ a b : ℝ, a - b = a + (-b) by intros; ring]
    -- tan (arctan x - arctan y) = (x - y) / (1 + x * y).
    rw [tan_add' ⟨h3 y, ?_⟩]
    swap
    · intro k
      specialize h3 x (-k - 1)
      push_cast at h3
      contrapose! h3
      linarith
    simp_rw [tan_neg, tan_arctan, y, x]
    -- It is left to prove that 1 / (2 * (n + 1)^2) = (x - y) / (1 + x * y).
    -- The result follows from algebraic simplifications.
    field_simp
    ring_nf