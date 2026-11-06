import Mathlib

/- For which positive integer values of $k$ does $kx^2+20x+k=0$ have rational solutions? Express your answers separated by commas and in increasing order. -/
unseal Nat.sqrt.iter in
theorem algebra_10581 (k : ℕ) (hk : k > 0) :
  (∃ x : ℝ, k * x ^ 2 + 20 * x + k = 0 ∧ ¬Irrational x) ↔ k = 6 ∨ k = 8 ∨ k = 10 := by

  -- proof of if $x$ is irrational .iff $|x|$ is irrational
  have irrational_abs_iff {x : ℝ} : Irrational x ↔ Irrational |x| := by
    constructor
    .
      intro hx
      if hxcond : 0 ≤ x then
        rw [← abs_eq_self] at hxcond
        rw [hxcond]
        exact hx
      else
        replace hxcond : x ≤ 0 := by linarith
        rw [← abs_eq_neg_self] at hxcond
        rw [hxcond]
        apply Irrational.neg
        exact hx
    .
      intro hx
      if hxcond : 0 ≤ x then
        rw [← abs_eq_self] at hxcond
        rw [← hxcond]
        exact hx
      else
        replace hxcond : x ≤ 0 := by linarith
        rw [← abs_eq_neg_self] at hxcond
        rw [← irrational_neg_iff]
        rw [← hxcond]
        exact hx

  -- if $a, b, c ∈ ℚ$ and discrim is not square of some rational, then root is irrational for quadratic equation
  have rational_root {a b c : ℚ} (ha : a ≠ 0) (x : ℝ) (hx : a * x * x + b * x + c = 0) : ¬IsSquare (discrim a b c) → Irrational x := by
    intro hs
    -- using quadratic has root imply discrim equal square
    rw [mul_assoc, quadratic_eq_zero_iff_discrim_eq_sq] at hx
    -- proof of a ≠ 0
    swap; norm_cast

    -- if discrim ≥ 0, then it will be real root in quadratic equation
    if hd : 0 ≤ discrim a b c then
      rw [← irrational_sqrt_ratCast_iff_of_nonneg] at hs
      apply_fun (√.) at hx
      rw [discrim] at hs hx
      push_cast at hs
      rw [hx] at hs
      rw [Real.sqrt_sq_eq_abs] at hs
      rw [←irrational_abs_iff] at hs
      rw [irrational_add_rat_iff] at hs
      rw [show 2 * ↑a * x = (x * ((2 * a) : ℚ)) by
        push_cast
        ring_nf
      ] at hs
      rw [irrational_mul_rat_iff] at hs
      exact hs.right
      exact hd
    -- if discrim < 0, no real root, so there is no rational root
    else
      -- proof of $(2 * a * x + b) ^ 2 ≥ 0$
      have nonneg := calc
        discrim ↑a ↑b ↑c = (2 * ↑a * x + ↑b) ^ 2 := hx
        _ ≥ 0 := by
          rw [ge_iff_le]
          apply sq_nonneg
      -- but discrim < 0, and $discrim = (2 * a * x + b) ^ 2$, contradiction
      rw [discrim] at nonneg hd
      have xxx : b ^ 2 - 4 * a * c = ((b ^ 2 - 4 * a * c) : ℝ) := by
        simp
      exfalso
      rw [not_le] at hd
      apply_fun (fun (x : ℚ) => (x : ℝ)) at hd; beta_reduce at hd
      push_cast at hd
      linarith
      mono

  constructor
  . -- proof of $k * x ^ 2 + 20 * x + k = 0$ has rational solutions → k = 6 ∨ k = 8 ∨ k = 10
    intro hx
    rcases hx with ⟨x, ⟨heq, hrat⟩⟩
    -- By considering the expression $\frac{-b\pm\sqrt{b^2-4ac}}{2a}$ for the solutions of $ax^2+bx+c=0$, we find that the solutions are rational if and only if the discriminant $b^2-4ac$ has a rational square root.
    rw [show ↑k * ↑x ^ 2 + 20 * ↑x + ↑k = ↑k * x * x + 20 * x + ↑k  by ring_nf] at heq
    have ho := heq
    -- rational root hypothesis
    have hrr := rational_root (show (k : ℚ) ≠ 0 by norm_cast; linarith) x ho

    -- we compute discrim to get the range of k
    rw [mul_assoc, quadratic_eq_zero_iff_discrim_eq_sq] at heq
    swap;
    intro keq0
    aesop
    rw [discrim] at heq;
    norm_num at heq

    -- proof of k ≤ 10
    have hd := calc
      400 - 4 * ↑k * ↑k = (2 * ↑k * x + 20) ^ 2 := heq
      _ ≥ 0 := by
        rw [ge_iff_le]
        apply pow_two_nonneg

    rw [ge_iff_le] at hd
    apply_fun (fun (t : ℝ) => (t + 4 * ↑k * ↑k) / 4) at hd; ring_nf at hd

    swap
    intro a b hab; beta_reduce; linarith

    norm_cast at hd;
    rw [pow_two, ← Nat.le_sqrt, ← Nat.lt_add_one_iff] at hd
    norm_num at hd

    -- we iterate k from 0 to 10
    rw [← Finset.mem_range] at hd
    fin_cases hd
    contradiction
    any_goals tauto
    all_goals
      -- we use rational root hypothesis above to get contradiction
      rw [discrim] at hrr; norm_num at hrr
      have hirrx : Irrational x := by
        apply hrr
        decide
      contradiction
  . -- proof of k = 6 ∨ k = 8 ∨ k = 10 → $k * x ^ 2 + 20 * x + k = 0$ has rational solutions
    intro hkval
    rcases hkval with hk6 | hk8 | hk10
    -- k = 6
    exists (√(discrim k 20 k) - 20) /  (2 * k)
    rw [hk6, discrim]; norm_num
    rw [show √256 = √(16 ^ 2) by ring_nf, Real.sqrt_sq]
    norm_num
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by simp]
    rw [irrational_div_nat_iff]
    rw [not_and_or]
    right
    exact not_irrational_one
    linarith
    -- k = 8
    exists (√(discrim k 20 k) - 20) /  (2 * k)
    rw [hk8, discrim]; norm_num
    rw [show √144 = √(12 ^ 2) by ring_nf, Real.sqrt_sq]
    norm_num
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by simp]
    rw [irrational_div_nat_iff]
    rw [not_and_or]
    right
    exact not_irrational_one
    linarith
    -- k = 10
    exists (√(discrim k 20 k) - 20) /  (2 * k)
    rw [hk10, discrim]; norm_num
