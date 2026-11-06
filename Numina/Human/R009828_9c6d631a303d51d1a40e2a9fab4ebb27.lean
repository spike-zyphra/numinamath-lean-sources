import Mathlib

open Real Set

/- Extension 2 Given $\alpha, \beta \in\left(0, \frac{\pi}{2}\right)$, then the necessary and sufficient condition for $\alpha+\beta=\frac{\pi}{2}$ is: $\frac{\sin ^{k+2} \alpha}{\cos ^{k} \beta}+\frac{\cos ^{k+2} \alpha}{\sin ^{k} \beta}=1, k \in \mathbf{N}^{*}$.
The necessity is obvious. -/
theorem algebra_261012 {k : ℕ} (hk : k > 0) (α β : ℝ) (h₀ : α ∈ Ioo 0 (π/2)) (h₁ : β ∈ Ioo 0 (π/2)) :
    α + β = π / 2 ↔ sin α^(k+2) / cos β^k + cos α^(k+2) / sin β^k = 1 := by
  -- 0 < cos x for any x ∈ (0, π / 2).
  have hcos_pos {x : ℝ} (hx : x ∈ Ioo 0 (π / 2)) : 0 < cos x := by
    apply cos_pos_of_mem_Ioo
    simp only [mem_Ioo] at hx ⊢
    constructor <;> linarith
  -- 0 < sin x for any x ∈ (0, π / 2).
  have hsin_pos {x : ℝ} (hx : x ∈ Ioo 0 (π / 2)) : 0 < sin x := by
    apply sin_pos_of_mem_Ioo
    simp only [mem_Ioo] at hx ⊢
    constructor <;> linarith
  constructor
  -- Show that α + β = π / 2 implies that sin α^(k+2) / cos β^k + cos α^(k+2) / sin β^k = 1.
  · intro h
    -- We have α = π / 2 - β, sin (π / 2 - β) = cos β and cos (π / 2 - β) = sin β
    rw [show α = π / 2 - β by linarith, sin_pi_div_two_sub, cos_pi_div_two_sub]
    rw [pow_add, pow_add]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero k $ ne_of_gt $ hcos_pos h₁), mul_div_cancel_left₀ _ (pow_ne_zero k $ ne_of_gt $ hsin_pos h₁)]
    -- Simplify the goal and get sin β^2 + cos β^2 = 1.
    rw [add_comm, sin_sq_add_cos_sq]
  -- Suppose that sin α^(k+2) / cos β^k + cos α^(k+2) / sin β^k = 1 and show that α + β = π / 2.
  intro h
  -- Prove the following inequality for all 0 < x and 0 < y:
  -- (k + 1) * x ^ 2 ≤ x ^ (k + 2) / y ^ k + k * x * y.
  have hineq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : (k + 1) * x ^ 2 ≤ x ^ (k + 2) / y ^ k + k * x * y := by
    -- Let w(i) = 1.
    set w : ℕ → ℝ := fun _ => 1
    -- Let z(i) = x * y if i ≠ k and z(k) = x ^ (k + 2) / y ^ k.
    set z : ℕ → ℝ := fun i => if i = k then x ^ (k + 2) / y ^ k else x * y
    -- 0 ≤ w i.
    have hw i : 0 ≤ w i := by simp [w]
    -- The sum of w i for i ∈ [0, k] is k + 1.
    have hw_sum : ∑ i ∈ Finset.range (k + 1), w i = (k + 1) := by simp [w]
    -- 0 ≤ z i.
    have hz i : 0 ≤ z i := by
      simp [z]
      split_ifs <;> positivity
    -- The sum of w i * z i = z i for i ∈ [0, k] is x ^ (k + 2) / y ^ k + k * x * y.
    have hwz_sum : ∑ i ∈ Finset.range (k + 1), w i * z i = x ^ (k + 2) / y ^ k + k * x * y := by
      simp [Finset.sum_range_succ, w]
      rw [add_comm]
      congr 1
      · simp [z]
      · simp_rw [show k = ∑ i ∈ Finset.range k, (1 : ℝ) by simp, Finset.sum_mul]
        apply Finset.sum_congr rfl
        simp only [Finset.mem_range, one_mul]
        intro i hi
        simp [z, show i ≠ k by omega]
    -- The product of z i ^ w i = z i for i ∈ [0, k] is x ^ (k + 2) / y ^ k * (x * y) ^ k = x ^ (2 * (k + 1)).
    have hwz_prod : ∏ i ∈ Finset.range (k + 1), z i ^ w i = x ^ (k + 2) * x ^ k := by
      simp [w, Finset.prod_range_succ]
      have eq : ∏ i ∈ Finset.range k, z i = ∏ i ∈ Finset.range k, x * y := by
        apply Finset.prod_congr rfl
        simp only [Finset.mem_range]
        intro i hi
        simp [z, show i ≠ k by omega]
      simp [eq, z]
      field_simp
      ring
    -- Apply the AM-GM inequality to w and z and get:
    -- (∏ i ∈ [0, k], z i ^ w i) ^ (∑ i ∈ [0, k], w i)⁻¹ ≤ (∑ i ∈ [0, k], w i * z i) / ∑ i ∈ [0, k], w i.
    have ineq := geom_mean_le_arith_mean (Finset.range (k + 1)) w z (fun i _ => hw i) (by linarith) (fun i _ => hz i)
    -- Plug in the computed sums and products to this inequality and get:
    -- x ^ (2 * (k + 1)) ^ (k + 1)⁻¹ ≤ (x ^ (k + 2) / y ^ k + k * x * y) / (k + 1).
    rw [hw_sum, hwz_sum, hwz_prod, ← pow_add, show k + 2 + k = 2 * (k + 1) by ring] at ineq
    rw [pow_mul, ← Real.rpow_natCast_mul (by positivity)] at ineq
    -- The inequality simplifies to x ^ 2 ≤ (x ^ (k + 2) / y ^ k + k * x * y) / (k + 1).
    rw [show (k + 1 : ℕ) * (k + 1 : ℝ)⁻¹ = 1 by field_simp, rpow_one] at ineq
    -- The result follows after multiplying both sides of the inequality by k + 1.
    rw [le_div_iff₀ (by linarith)] at ineq
    rw [mul_comm]
    exact ineq
  -- Derive the following inequality:
  -- k + 1 ≤ k * sin (α + β) + 1.
  replace hineq : k + 1 ≤ k * sin (α + β) + 1 := by
    -- Use hineq with x = sin α and y = cos β and get
    -- (k + 1) * sin α ^ 2 ≤ sin α ^ (k + 2) / cos β ^ k + k * sin α * cos β.
    have h1 := hineq (hsin_pos h₀) (hcos_pos h₁)
    -- Use hineq with x = cos α and y = sin β and get
    -- (k + 1) * cos α ^ 2 ≤ cos α ^ (k + 2) / sin β ^ k + k * cos α * sin β.
    have h2 := hineq (hcos_pos h₀) (hsin_pos h₁)
    calc
      -- We have k + 1 = (k + 1) * (sin α ^ 2 + cos α ^ 2)
      --               ≤ (sin α ^ (k + 2) / cos β ^ k + cos α ^ (k + 2) / sin β ^ k) + k * sin (α + β)
      -- (from h1 and h2 and from sin (α + β) = sin α * cos β + cos α * sin β)
      --               = k * sin (α + β) + 1
      -- (because sin α ^ (k + 2) / cos β ^ k + cos α ^ (k + 2) / sin β ^ k) = 1).
      k + 1 = (k + 1) * (sin α ^ 2 + cos α ^ 2) := by rw [sin_sq_add_cos_sq, mul_one]
      _ ≤ (sin α ^ (k + 2) / cos β ^ k + k * sin α * cos β) + (cos α ^ (k + 2) / sin β ^ k + k * cos α * sin β) := by
          linear_combination h1 + h2
      _ = (sin α ^ (k + 2) / cos β ^ k + cos α ^ (k + 2) / sin β ^ k) + k * sin (α + β) := by
          rw [sin_add]; ring
      _ = k * sin (α + β) + 1 := by rw [h]; ring
  -- k + 1 ≤ k * sin (α + β) + 1 implies that 1 ≤ sin (α + β). But sin (α + β) ≤ 1 so sin (α + β) = 1.
  have hsin : sin (α + β) = 1 := by rify at hk; nlinarith [sin_le_one (α + β)]
  -- From sin (α + β) = 1 we obtain α + β = π / 2 + k * (2π) for some integer k.
  -- Show that k = 0.
  rw [sin_eq_one_iff] at hsin
  clear * - h₀ h₁ hsin
  have ⟨k, hk⟩ := hsin
  simp at h₀ h₁
  rcases show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega with h | h | h
  -- If k ≤ -1 then α + β < 0, a contradiction.
  · rify at h
    nlinarith
  · subst k
    linarith
  -- If 1 ≤ k then α + β > π, a contradiction.
  · rify at h
    nlinarith