import Mathlib

open Real

/- Given x, y ∈ [0, 1], then x ^ 2 + y ^ 2 ≤ x ^ 2 * y + 1. -/
lemma Real_sq_add_eq_le_sq_mul_add_one {x y : ℝ}
  (xh : x ∈ Set.Icc 0 1) (yh : y ∈ Set.Icc 0 1)
  : x ^ 2 + y ^ 2 ≤ x ^ 2 * y + 1 := by
    -- move terms to RHS, group into two factors
    suffices : 0 ≤ (1 - y) * (1 + y - x ^ 2)
    · linarith

    -- normalize bounds
    norm_num at xh yh

    -- left factor is non-negative
    have left_pos : 0 ≤ (1 - y) := by linarith

    -- right factor is non-negative
    have right_pos : 0 ≤ (1 + y - x ^ 2) := by nlinarith

    -- so the product is non-negative
    positivity

/- 4. Find the largest constant $k$, such that for all real numbers $a, b, c, d$ in $[0,1]$, the inequality $a^{2} b+b^{2} c+c^{2} d+d^{2} a+4 \geqslant k\left(a^{3}+b^{3}+c^{3}+d^{3}\right)$ holds. -/
theorem inequalities_162998 :
    IsGreatest {k | ∀ a b c d : ℝ, a ∈ Set.Icc 0 1 → b ∈ Set.Icc 0 1 → c ∈ Set.Icc 0 1 → d ∈ Set.Icc 0 1 →
      a^2 * b + b^2 * c + c^2 * d + d^2 * a + 4 ≥ k * (a^3 + b^3 + c^3 + d^3)} 2
  := by

    -- Use definitions of "greatest number" and "upper-bounds"
    unfold IsGreatest upperBounds

    -- we'll prove both parts
    split_ands
    -- we prove that 2 is a lower bound for k
    · simp only [Set.mem_setOf]
      intro a b c d ah bh ch dh

      -- use ≤ instead of ≥
      simp only [ge_iff_le]

      -- we can change exponents of LHS from 3 to 2, it won't decrease the LHS
      trans 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
      · gcongr 2 * ?_
        -- we'll use the bounds on a b c d
        norm_num at ah bh ch dh

        -- prove term wise
        iterate 3 apply add_le_add
        -- if 0 ≤ x ≤ 1, then decreasing exponent increases the value
        · exact pow_le_pow_of_le_one (by tauto) (by tauto) (by omega)
        · exact pow_le_pow_of_le_one (by tauto) (by tauto) (by omega)
        · exact pow_le_pow_of_le_one (by tauto) (by tauto) (by omega)
        · exact pow_le_pow_of_le_one (by tauto) (by tauto) (by omega)

      -- group terms on both sides to apply bound on x ^ 2 + y ^ 2
      convert_to (a ^ 2 + b ^ 2) + (b ^ 2 + c ^ 2) + (c ^ 2 + d ^ 2) + (d ^ 2 + a ^ 2) ≤ (a ^ 2 * b + 1) + (b ^ 2 * c + 1) +  (c ^ 2 * d + 1) +  (d ^ 2 * a + 1)
      · ring
      · ring

      -- bound holds term-wise
      iterate 3 apply add_le_add
      exact Real_sq_add_eq_le_sq_mul_add_one ah bh
      exact Real_sq_add_eq_le_sq_mul_add_one bh ch
      exact Real_sq_add_eq_le_sq_mul_add_one ch dh
      exact Real_sq_add_eq_le_sq_mul_add_one dh ah


    -- we have a b c d which achieve k ≤ 2
    · simp only [Set.mem_setOf]
      intro k h
      -- a = b = c = d = 1 works
      replace h := h 1 1 1 1
      norm_num at h
      linarith