import Mathlib

open Real

/- 3. Let `x + 1/x = 2 cos φ`. Prove that `xⁿ + 1/xⁿ = 2 cos (n φ)` for every natural number `n`. -/
theorem algebra_253311 {x φ : ℝ} (hx : x ≠ 0) (h : x + 1/x = 2 * cos φ) :
    ∀ n : ℕ, x ^ n + 1 / x ^ n = 2 * cos (n * φ) := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero =>
    -- Base case: n = 0
    -- Simplify x^0 + 1/x^0 = 1 + 1 = 2
    simp only [pow_zero, div_one, one_add_one_eq_two]
    rw [Nat.cast_zero, zero_mul, cos_zero]
    norm_num
  | succ n' =>
    cases n' with
    | zero =>
      -- Base case: n = 1
      -- Need to show x^1 + 1/x^1 = 2 * cos(φ)
      simp
      rw [inv_eq_one_div]
      exact h
    | succ k =>
      -- Inductive step: prove for n = k + 2 using hypotheses for k and k + 1
      -- Apply induction hypothesis for k
      have ih_k : x ^ k + 1 / x ^ k = 2 * cos (k * φ) := by
        exact ih k (Nat.lt_succ_of_lt (Nat.lt_succ_self (k)))
      -- Apply induction hypothesis for k + 1
      have ih_k_plus_1 : x ^ (k + 1) + 1 / x ^ (k + 1) = 2 * cos ((k + 1) * φ) := by
        have rewrite_cast : (↑(k + 1) : ℝ) = (↑k + 1) := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [<-rewrite_cast]
        exact ih (k + 1) (Nat.lt_succ_self (k + 1))
      -- Establish the recurrence relation
      have recurrence : x ^ (k + 2) + 1 / x ^ (k + 2) =
          (x ^ (k + 1) + 1 / x ^ (k + 1)) * (x + 1 / x) - (x ^ k + 1 / x ^ k) := by
        field_simp [hx]
        ring
      -- Substitute the recurrence relation and apply known identities
      rw [recurrence, ih_k_plus_1, h, ih_k]
      ring_nf
      -- Prove the trigonometric identity
      have trig : cos (φ * (k + 2)) = 2 * cos (φ * (k + 1)) * cos φ - cos (φ * k) := by
        -- Use cosine product formula
        have cos_product : 2 * cos (φ * (k + 1)) * cos φ =
            cos (φ * (k + 2)) + cos (φ * k) := by
          rw [Real.two_mul_cos_mul_cos]
          -- Simplify φ * (k + 1) - φ = φ * k
          have simplify_sub : φ * (k + 1) - φ = φ * k := by
            ring_nf
          -- Simplify φ * (k + 1) + φ = φ * (k + 2)
          have simplify_add : φ * (k + 1) + φ = φ * (k + 2) := by
            ring_nf
          rw [simplify_add, simplify_sub]
          ring
        rw [cos_product]
        ring_nf
      rw [Nat.add_comm]
      rw [Nat.cast_add]
      rw [Nat.cast_two]
      rw [trig]
      ring_nf