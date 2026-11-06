import Mathlib

open Real Set
open scoped Real

/- 7. If $\alpha, \beta, \gamma$ are acute angles, and $\sin ^{2} \alpha+\sin ^{2} \beta+\sin ^{2} \gamma=1$, then the maximum value of $\frac{\sin \alpha+\sin \beta+\sin \gamma}{\cos \alpha+\cos \beta+\cos \gamma}$ is
$\qquad$ . -/
theorem algebra_135929
  : IsGreatest ((fun ⟨α, β, γ⟩ => (sin α + sin β + sin γ) / (cos α + cos β + cos γ))
      '' {(α, β, γ) : ℝ × ℝ × ℝ | α ∈ Ioo 0 (π / 2) ∧ β ∈ Ioo 0 (π / 2) ∧ γ ∈ Ioo 0 (π / 2)
        ∧ sin α ^ 2 + sin β ^ 2 + sin γ ^ 2 = 1}) (sqrt 2 / 2) := by

    -- consider the definition of "greatest number of set" and "upper bounds"
    unfold IsGreatest upperBounds

    -- we prove both parts separately
    split_ands

    -- first we we prove that √2 / 2 is achievable
    · norm_num
      -- it works with α = β = γ = arcsin (1 / √3)
      exists arcsin (1 / √3)
      exists arcsin (1 / √3)
      exists arcsin (1 / √3)

      -- simplify
      norm_num

      -- 1 / √3 is less than 1
      have lee : (√3)⁻¹ < 1 := by
        rw [←one_div, one_div_lt]
        norm_num
        refine lt_sqrt_of_sq_lt ?_
        norm_num
        · positivity
        · positivity

      -- 1 / √3 is at least -1
      have neg_one_le : -1 ≤ (√3)⁻¹ := by
        trans 0
        · norm_num
        positivity

      -- simplify arcsin expression
      rw [Real.sin_arcsin neg_one_le (le_of_lt lee), Real.cos_arcsin]

      -- simplify arithmetic
      iterate 2 field_simp; ring_nf

      -- clean up the rest and we're done
      norm_num [lee]

    -- then we'll prove that √2 / 2 is an upper bound
    -- simplify
    · simp only [mem_image, mem_setOf_eq, Prod.exists, forall_exists_index, and_imp]
      -- then we have the angles α β γ ∈ (0, π / 2)
      -- and sin α ^ 2 + sin β ^ 2 + sin γ ^ 2 = 1
      rintro _ α β γ h₀ h₁ h₂ h₃ rfl

      -- given non-negative a and b, we have
      -- a + b ≤ √2 * √(a ^ 2 + b ^ 2)
      have a_b : ∀ {a b}, 0 ≤ a → 0 ≤ b → a + b ≤ √2 * √(a ^ 2 + b ^ 2) := by
        intro a b ha hb
        -- we have that (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2)
        have simple_bound : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
          suffices : 2 * a * b ≤ a ^ 2 + b ^ 2
          · linarith
          exact two_mul_le_add_sq a b

        -- square both sides
        convert Real.le_sqrt_of_sq_le simple_bound using 1

        -- distribute sqaure roots
        exact (sqrt_mul (by linarith) _).symm

      -- note that pi is positive
      have pi_pos : 0 < π := by positivity

      -- (0, π / 2) is a subset of (-π / 2, π / 2)
      have subs : Ioo 0 (π / 2) ⊆ Ioo (-(π / 2)) (π / 2) := Ioo_subset_Ioo_left (by linarith)

      -- and (0, π / 2) is a subset of (0, π)
      have subs' : Ioo 0 (π / 2) ⊆ Ioo 0 π := Ioo_subset_Ioo_right (by linarith)

      -- so sin α, sin β, sin γ are all positive
      have sin_pos_0 : 0 < sin α := sin_pos_of_mem_Ioo <| subs' h₀
      have sin_pos_1 : 0 < sin β := sin_pos_of_mem_Ioo <| subs' h₁
      have sin_pos_2 : 0 < sin γ := sin_pos_of_mem_Ioo <| subs' h₂

      -- and cos α, cos β, cos γ are all positive
      have cos_pos_0 : 0 < cos α := cos_pos_of_mem_Ioo <| subs h₀
      have cos_pos_1 : 0 < cos β := cos_pos_of_mem_Ioo <| subs h₁
      have cos_pos_2 : 0 < cos γ := cos_pos_of_mem_Ioo <| subs h₂

      -- using sin α ^ 2 + sin β ^ 2 + sin γ ^ 2 = 1
      -- we have sin α ^ 2 + sin β ^ 2 = 1 - sin γ ^ 2
      have add_eq_0 : sin α ^ 2 + sin β ^ 2 = 1 - sin γ ^ 2 := by linarith

      -- and sin β ^ 2 + sin γ ^ 2 = 1 - sin α ^ 2
      have add_eq_1 : sin β ^ 2 + sin γ ^ 2 = 1 - sin α ^ 2 := by linarith

      -- and sin γ ^ 2 + sin α ^ 2 = 1 - sin β ^ 2
      have add_eq_2 : sin γ ^ 2 + sin α ^ 2 = 1 - sin β ^ 2 := by linarith

      -- so sin α + sin β ≤ √2 * cos γ
      have sin_add_sin_0 : sin α + sin β ≤ √2 * cos γ := by
        convert a_b (le_of_lt sin_pos_0) (le_of_lt sin_pos_1) using 2
        rw [add_eq_0, ←Real.cos_sq', sqrt_sq (le_of_lt cos_pos_2)]

      -- and sin β + sin γ ≤ √2 * cos α
      have sin_add_sin_1 : sin β + sin γ ≤ √2 * cos α := by
        convert a_b (le_of_lt sin_pos_1) (le_of_lt sin_pos_2) using 2
        rw [add_eq_1, ←Real.cos_sq', sqrt_sq (le_of_lt cos_pos_0)]

      -- and sin γ + sin α ≤ √2 * cos β
      have sin_add_sin_2 : sin γ + sin α ≤ √2 * cos β := by
        convert a_b (le_of_lt sin_pos_2) (le_of_lt sin_pos_0) using 2
        rw [add_eq_2, ←Real.cos_sq', sqrt_sq (le_of_lt cos_pos_1)]

      -- combining the three bound we have
      -- (sin α + sin β + sin γ) * 2 ≤ √2 * (cos α + cos β + cos γ)
      have combined_bound : (sin α + sin β + sin γ) * 2 ≤ √2 * (cos α + cos β + cos γ) := by linarith

      -- rearranging we have the final inequality
      exact (div_le_div_iff₀ (by positivity) (by linarith)).mpr combined_bound