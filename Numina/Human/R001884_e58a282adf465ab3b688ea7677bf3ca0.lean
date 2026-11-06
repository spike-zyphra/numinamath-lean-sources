import Mathlib

open Real Set
open scoped Real

/- Prove that among any four distinct numbers from the interval $ (0,\frac{\pi}{2})$ there are two, say $ x,y,$ such that:

$ 8 \cos x \cos y \cos (x\minus{}y)\plus{}1>4(\cos ^2 x\plus{}\cos ^2 y).$ -/
theorem inequalities_42334 (s : Finset ℝ) (h₀ : s.card = 4)
  (h₁ : ∀ x ∈ s, x ∈ Ioo 0 (π/2)) :
  ∃ x ∈ s, ∃ y ∈ s, 8 * cos x * cos y * cos (x - y) + 1 > 4 * (cos x^2 + cos y^2) := by
  -- We first prove an algebraic identity to simplify the inequality.
  have inequality_iff : ∀ x y : ℝ,
      8 * cos x * cos y * cos (x - y) + 1 > 4 * (cos x ^ 2 + cos y ^ 2) ↔
      cos (x - y) ^ 2 > 3 / 4 := by
    -- For any x, y, we will show the equivalence.
    intro x y
    -- First, we rewrite the term with 8 * cos x * cos y using product-to-sum identities.
    have eq1 : 8 * cos x * cos y * cos (x - y) = 4 * cos (x + y) * cos (x - y) + 4 * cos (x - y) ^ 2 := by
      calc
        8 * Real.cos x * Real.cos y * Real.cos (x - y)
        = 4 * (2 * Real.cos x * Real.cos y) * Real.cos (x - y) := by ring
        -- Apply the product-to-sum formula: 2 * cos(a) * cos(b) = cos(a + b) + cos(a - b).
        _ = 4 * (Real.cos (x + y) + Real.cos (x - y)) * Real.cos (x - y) := by 
          rw [Real.cos_add, Real.cos_sub]; ring
        -- Distribute the term.
        _ = 4 * Real.cos (x + y) * Real.cos (x - y) + 4 * Real.cos (x - y) ^ 2 := by ring
    -- Next, we rewrite the term 4 * cos(x + y) * cos(x - y) using another product-to-sum identity.
    have eq2 : 4 * cos (x + y) * cos (x - y) = 2 * (cos (2 * x) + cos (2 * y)) := by 
      rw [show 2 * x = (x + y) + (x - y) by ring, show 2 * y = (x + y) - (x - y) by ring, 
        Real.cos_add (x + y), Real.cos_sub (x + y), ← add_assoc, sub_add_eq_add_sub]
      ring
    -- Then, we rewrite the right hand side of the original inequality using the double angle formula for cosine.
    have eq3 : 4 * (cos x ^ 2 + cos y ^ 2) = 4 + 2 * (cos (2 * x) + cos (2 * y)) := by 
      rw [Real.cos_sq, Real.cos_sq]; ring
    -- Substitute these equalities into the original inequality.
    rw [eq1, eq2, eq3, add_assoc, add_comm 4]
    -- Simplify the expression, many terms cancel out.
    simp
    -- Rearrange the inequality to get the desired form.
    rw [div_lt_iff₀ (by norm_num), ← sub_lt_iff_lt_add, mul_comm]
    -- The final step is a numerical calculation.
    norm_num
  -- It now suffices to prove that there exist two distinct points x, y in s whose distance is less than π/6.
  suffices ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ |x - y| < π / 6 by
    -- Assume we have such x and y.
    rcases this with ⟨x, hx, y, hy, h_ne, h_dist⟩
    -- We use these x and y to prove the main goal.
    use x, hx, y, hy
    -- Use the equivalence we proved earlier.
    rw [inequality_iff]
    -- We need to show cos((x-y)^2) > 3/4. First, prove cos(x-y) is positive.
    have h_cos_pos : 0 < cos (x - y) := by
      -- Since x, y are in (0, π/2), their difference is in (-π/2, π/2).
      have h_abs : |x - y| < π / 2 := by
        have hx_bound := (h₁ x hx)
        have hy_bound := (h₁ y hy)
        -- We know |x - y| < π/6, and π/6 < π/2.
        trans π / 6
        exact h_dist
        rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
        refine (mul_lt_mul_left (by exact pi_pos)).mpr (by norm_num)
      -- Cosine is positive on (-π/2, π/2).
      apply cos_pos_of_mem_Ioo
      simp [abs_lt] at h_abs
      simp [h_abs]
    -- Rewrite 3/4 as (sqrt(3)/2)^2.
    have h1 : 3 / 4 = (√3 / 2) ^ 2 := by 
      rw [div_pow, sq_sqrt (by norm_num)]
      norm_num
    -- The inequality becomes cos(x-y) > sqrt(3)/2, since cos(x-y) is positive.
    simp [h1, sq_lt_sq, abs_of_pos h_cos_pos]
    -- A helper lemma for monotonicity.
    have h2 : π / 6 ≤ π := by
      rw [div_le_iff₀ (by norm_num)]
      nth_rw 1 [← mul_one π]
      refine (mul_le_mul_left (by exact pi_pos)).mpr (by norm_num)
    -- Since cos is strictly decreasing on [0, π] and |x-y| < π/6, we have cos(|x-y|) > cos(π/6).
    have h_cos_mono := Real.strictAntiOn_cos (a := |x - y|) (by simp; linarith) ⟨by positivity, h2⟩ h_dist
    -- Simplify and use the fact that cos(π/6) = sqrt(3)/2.
    simp at h_cos_mono
    -- Since cos is an even function, cos(x-y) = cos(|x-y|).
    rwa [abs_eq_self.mpr]
    -- We need to show that |x-y| is non-negative, which is true by definition.
    apply div_nonneg (sqrt_nonneg 3) (by norm_num)
  -- We now prove the 'suffices' statement using the Pigeonhole Principle.
  -- Define a function that maps x to the index of the interval [k*π/6, (k+1)*π/6) it belongs to.
  let f : ℝ → ℕ := fun x ↦ ⌊x / (π / 6)⌋₊
  -- Show that for any x in s, f(x) can only be 0, 1, or 2.
  have hf : ∀ x ∈ s, f x ∈ ({0, 1, 2} : Finset ℕ) := by  
    intro x hx_s
    -- Get the bounds for x from the hypothesis h₁.
    have hx_bounds := h₁ x hx_s
    -- Prepare for checking membership in {0, 1, 2}.
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    -- Show that x / (π/6) is between 0 and 3, since x is in (0, π/2).
    have : 0 < x / (π / 6) ∧ x / (π / 6) < 3 := by
      constructor
      · exact div_pos hx_bounds.1 (div_pos pi_pos (by norm_num))
      · apply lt_of_lt_of_le (b := (π / 2) / (π / 6))
        · apply div_lt_div_of_pos_right _ (by positivity)
          simp [hx_bounds.2]
        · field_simp
          rw [mul_comm, mul_div_mul_right _ _ (by positivity)]
          norm_num
    -- This implies that the floor of x / (π/6) is 0, 1, or 2.
    have : 0 ≤ f x ∧ f x < 3 := by 
      simp [f]
      suffices ⌊x / (π / 6)⌋₊ < (3 : ℝ) by norm_cast at this
      apply lt_of_le_of_lt (b := x / (π / 6)) 
      · refine Nat.floor_le (by linarith)
      · exact this.2
    -- The omega tactic solves this integer arithmetic goal.
    omega
  -- The image of s under f has at most 3 elements.
  have h_card_image : (s.image f).card ≤ 3 := by
    suffices s.image f ⊆ ({0, 1, 2} : Finset ℕ) by
      exact Finset.card_le_card this
    intro n hn
    rw [Finset.mem_image] at hn
    rcases hn with ⟨x, hx_s, rfl⟩
    exact hf x hx_s
  -- By PHP, since s has 4 elements and the image has at most 3, there must be two distinct elements in s with the same image under f.
  have h_pigeonhole : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
    apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := s) (t := {0, 1, 2})
    -- s is non-empty because its card is 4.
    · exact Finset.powersetCard_eq_empty.mp (by simp [h₀])
    -- The function f maps s to {0, 1, 2}.
    · exact fun a a_1 => hf a a_1
  -- Let x and y be these two elements.
  rcases h_pigeonhole with ⟨x, hx_s, y, hy_s, h_ne, h_f_eq⟩
  -- Use these x and y to prove our goal. We only need to show |x - y| < π/6.
  use x, hx_s, y, hy_s, h_ne
  -- If two numbers have the same floor, their difference is less than 1.
  have h_floor_prop : |x / (π / 6) - y / (π / 6)| < 1 := by
    refine Int.abs_sub_lt_one_of_floor_eq_floor ?_
    -- We have floor(x/(π/6)) = floor(y/(π/6)).
    simp [f] at h_f_eq
    have hx_bounds := (h₁ x hx_s)
    -- The argument x/(π/6) is positive.
    have : 0 < x / (π / 6) := by 
      exact div_pos hx_bounds.1 (div_pos pi_pos (by norm_num))
    have hy_bounds := (h₁ y hy_s)
    -- The argument y/(π/6) is positive.
    have : 0 < y / (π / 6) := by 
      exact div_pos hy_bounds.1 (div_pos pi_pos (by norm_num))
    -- The lemma requires Int.floor, but we have Nat.floor. They are equivalent for non-negative numbers.
    rw [← Int.natCast_floor_eq_floor (by linarith), ← Int.natCast_floor_eq_floor (by linarith)]
    -- Use the equality from the pigeonhole principle.
    simp [h_f_eq]
  -- Rewrite the expression inside the absolute value.
  rw [← sub_div, abs_div] at h_floor_prop
  -- The denominator is positive, so we can pull it out of the absolute value.
  rw [abs_of_pos (div_pos pi_pos (by norm_num))] at h_floor_prop
  -- The inequality |x-y|/(π/6) < 1 is equivalent to |x-y| < π/6.
  exact (div_lt_one (div_pos pi_pos (by norm_num))).mp h_floor_prop