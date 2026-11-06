import Mathlib

/- Find all functions $f: \mathbb{R}^{+} \rightarrow \mathbb{R}$ and $g: \mathbb{R}^{+} \rightarrow \mathbb{R}$ such that

$$
f\left(x^{2}+y^{2}\right)=g(x y)
$$

holds for all $x, y \in \mathbb{R}^{+}$.

## Proposed by Greece -/
theorem algebra_606020 :
  {(f, g) : ({x : ℝ // x > 0} → ℝ) × ({x : ℝ // x > 0} → ℝ) | ∀ x y (hx : x > 0) (hy : y > 0), f (⟨x ^ 2 + y ^ 2, by positivity⟩) = g (⟨x * y, by positivity⟩)} = {(fun _ ↦ c, fun _ ↦ c) | c : ℝ} := by
  ext ⟨f, g⟩
  simp
  constructor
  -- We first verify that constant functions satisfy the condition.
  swap
  . rintro ⟨c, rfl, rfl⟩
    simp
  -- Now let f and g be two functions that satisfy the condition.
  . intro H
    -- First, we show that f(u) = g(1) for all u ≥ 2.
    have K₁ u (hu : u ≥ 2) : f ⟨u, by linarith⟩ = g ⟨1, Real.zero_lt_one⟩ := by
      -- We can find some a, b > 0 such that a + b = u and ab = 1.
      obtain ⟨a, b, ha, hb, hsum, hprod⟩ : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = u ∧ a * b = 1 := by
        -- Set u = u / 2 + √((u / 2) ^ 2 - 1) and v = u / 2 - √((u / 2) ^ 2 - 1).
        use u / 2 + √((u / 2) ^ 2 - 1), u / 2 - √((u / 2) ^ 2 - 1)
        have h : (u / 2) ^ 2 - 1 ≥ 0 := by
          nlinarith only [hu]
        simp [← pow_two_sub_pow_two, h]
        refine ⟨by positivity, ?_⟩
        rw [Real.sqrt_lt' (by positivity)]
        simp
      have ha' := le_of_lt ha
      have hb' := le_of_lt hb
      -- Now we set x = √a and y = √b in the given equation.
      specialize H √a √b (Real.sqrt_pos_of_pos ha) (Real.sqrt_pos_of_pos hb)
      have hprod' : √a * √b = 1 := by
        rw [← Real.sqrt_mul ha' _]
        simp [hprod]
      -- Now we get f(u) = g(1).
      simp [ha', hb', hprod', hsum] at H
      exact H
    -- Now we show that g(t) = g(1) for all t > 0.
    have K₂ (t : ℝ) (ht : t > 0) : g ⟨t, ht⟩ = g ⟨1, Real.zero_lt_one⟩ := by
      -- Set x = t / 2 and y = 2 in the given equation.
      -- We get f((t / 2) ^ 2 + 2 ^ 2) = g(t)
      specialize H (t / 2) 2 (by linarith) (by simp)
      simp at H
      -- Use the previous result to get g(t) = g(1).
      specialize K₁ ((t / 2) ^ 2 + 2 ^ 2) (by linarith [sq_nonneg t])
      rw [H] at K₁
      exact K₁
    -- We can now conclude that any f(t₁) or g(t₂) equals g(1).
    use g ⟨1, Real.zero_lt_one⟩
    constructor
    . ext ⟨x, hx⟩
      -- Any number can be written as a sum of two squares.
      -- x = a ^ 2 + b ^ 2 for some a, b > 0.
      obtain ⟨a, b, ha, hb, h⟩ : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = x := by
        use √(x / 2), √(x / 2)
        refine ⟨Real.sqrt_pos.mpr (half_pos hx), Real.sqrt_pos.mpr (half_pos hx), ?_⟩
        rw [show √(x / 2) ^ 2 = x / 2 from Real.sq_sqrt (le_of_lt (half_pos hx))]
        simp
      -- Put (a, b) into the given equation, and we get f(x) = g(1).
      specialize H a b ha hb
      simp [h] at H
      rw [K₂] at H
      exact H.symm
    . -- We have already shown that g(t) = g(1) for all t > 0.
      ext ⟨x, hx⟩
      exact (K₂ x hx).symm
