import Mathlib
set_option maxHeartbeats 400000

open Real

/- Solve the following equation on the set of real numbers:


$$

\log _{19}(x-3)+\log _{93}(x-3)=3-\lg \left(x^{5}-24\right)

$$
 -/
theorem algebra_153900 {x : ℝ} (hx : (x : ℝ) > ( 3 : ℝ)) :
    logb 19 (x - 3) + logb 93 (x - 3) = 3 - logb 10 (x ^ 5 - 24) ↔ x = 4 := by

    have : x ∈ Set.Ioi (3 : ℝ) := by exact hx
    --First define the function f as follows.
    let f := fun (y:ℝ) ↦ logb 19 ((y : ℝ) - (3 : ℝ)) + logb 93 ((y : ℝ) - (3 : ℝ))
    --Next show that f is strictly increasing.
    have h1 : StrictMonoOn f (Set.Ioi (3 : ℝ)) := by
        intro a ha
        intro b hb
        intro h
        unfold f
        --Show logb 19 ((a : ℝ) - (3 : ℝ)) < logb 19 ((b : ℝ) - (3 : ℝ)).
        have h11 : logb 19 ((a : ℝ) - (3 : ℝ)) < logb 19 ((b : ℝ) - (3 : ℝ)) := by
            refine logb_lt_logb ?_ ?_ ?_
            norm_num
            exact sub_pos.mpr ha
            linarith
        --Show logb 93 ((a : ℝ) - (3 : ℝ)) < logb 93 ((b : ℝ) - (3 : ℝ))
        have h12 : logb 93 ((a : ℝ) - (3 : ℝ)) < logb 93 ((b : ℝ) - (3 : ℝ)) := by
            refine logb_lt_logb ?_ ?_ ?_
            norm_num
            exact sub_pos.mpr ha
            linarith
        --Combine the two inequalities.
        exact add_lt_add h11 h12

    --Now define the function g as follows.
    let g := fun (y:ℝ) ↦  (3 : ℝ) - logb 10 ((y : ℝ)^(5 : ℝ) - (24 : ℝ))
    --Then show that f is strictly decreasing.
    have h2 : StrictAntiOn g (Set.Ioi (3 : ℝ)) := by
        intro a ha
        intro b hb
        intro h
        unfold g
        --Show - logb 10 ((b : ℝ)^(5 : ℝ) - (24 : ℝ)) < - logb 10 ((a : ℝ)^(5 : ℝ) - (24 : ℝ)).
        have h21 : - logb 10 ((b : ℝ)^(5 : ℝ) - (24 : ℝ)) < - logb 10 ((a : ℝ)^(5 : ℝ) - (24 : ℝ)) := by
            refine neg_lt_neg_iff.mpr ?_
            refine logb_lt_logb ?_ ?_ ?_
            norm_num
            have : a > 3 := by exact ha
            have : a^5 > 3^5 := by
                refine (pow_lt_pow_iff_left₀ ?_ ?_ ?_).mpr ha
                linarith
                linarith
                linarith
            have : a^5 - 3^5 < a^5 - 24 := by
                linarith
            have : a^5 - 3^5 > 0 := by
                linarith
            have : 0 < a^5 - 24 := by linarith
            have nc : a ^ (5 : ℕ) = a ^ (5 : ℝ) := by norm_cast
            rw [nc] at this
            exact this
            have : a > 3 := by exact ha
            have : b > 3 := by exact hb
            refine sub_lt_sub_right ?_ 24
            refine (rpow_lt_rpow_iff ?_ ?_ ?_).mpr h
            linarith
            linarith
            norm_num

        --Then the inequality follows as 3 is positivie.
        have h22 : 3 - logb 10 ((b : ℝ)^(5 : ℝ) - (24 : ℝ)) < 3 - logb 10 ((a : ℝ)^(5 : ℝ) - (24 : ℝ)) := by
            linarith

        exact h22

    --This is the crux of the problem. Since f is increasing and g is decreasing they intersect at at most one point.
    have h3 : ∀ x y : Set.Ioi (3 : ℝ), f x = g x ∧ f y = g y → x = y := by
        --We prove this by way of contradiction. Two cases; both give contradictions.
        intro x y h
        by_contra h'
        have : x > y ∨ x < y := by exact lt_or_gt_of_ne fun a ↦ h' (id (Eq.symm a))
        rcases this with (hge|hle)
        have hcont1 : (x : ℝ) > (y : ℝ) := by exact hge
        have f_mono : f (x : ℝ) > f (y : ℝ) := by
            apply h1
            exact Subtype.coe_prop y
            exact Subtype.coe_prop x
            exact hge

        have g_anti : g (x : ℝ) < g (y : ℝ) := by
            apply h2
            exact Subtype.coe_prop y
            exact Subtype.coe_prop x
            exact hge

        have h31 : f (x : ℝ) = g (x : ℝ) := by exact h.1
        have h32 : f (y : ℝ) = g (y : ℝ) := by exact h.2
        linarith


        have f_mono : f (x : ℝ) < f (y : ℝ) := by
            apply h1
            exact Subtype.coe_prop x
            exact Subtype.coe_prop y
            exact hle

        have g_anti : g (x : ℝ) > g (y : ℝ) := by
            apply h2
            exact Subtype.coe_prop x
            exact Subtype.coe_prop y
            exact hle

        have h31 : f (x : ℝ) = g (x : ℝ) := by exact h.1
        have h32 : f (y : ℝ) = g (y : ℝ) := by exact h.2
        linarith


    --Then show there is a unique x > 3 such that f x = g x. This x is 4 it turns out.
    have h4 : ∃!x : Set.Ioi (3 : ℝ), f x = g x := by
        have h41 : f 4 = g 4 := by
            unfold f g
            norm_num
            have : 1000 = (10 : ℝ)^(3 : ℝ) := by norm_num
            rw [this]
            have : logb 10 (10 ^ (3 : ℝ)) = 3 := by
                calc
                    _ = (3 : ℝ) * logb 10 (10) := by
                        refine logb_rpow_eq_mul_logb_of_pos ?_
                        norm_num
                    _ = (3 : ℝ) * 1 := by
                        have : logb 10 (10) = 1 := by
                            refine logb_self_eq_one ?_
                            norm_num
                        rw [this]
                    _ = 3 := by ring
            rw [this]
            ring

        have h42 : 4 ∈ Set.Ioi (3 : ℝ) := by
            refine Set.mem_Ioi.mpr ?_
            norm_num

        use ⟨4, h42⟩
        constructor
        exact h41
        intro y
        intro h
        apply h3 y
        exact ⟨h, h41⟩

    --Then show f 4 = g 4.
    have h5 : f (4 : ℝ) = g (4 : ℝ) := by
        unfold f g
        norm_num
        have : 1000 = (10 : ℝ)^(3 : ℝ) := by norm_num
        rw [this]
        have : logb 10 (10 ^ (3 : ℝ)) = 3 := by
            calc
                _ = (3 : ℝ) * logb 10 (10) := by
                    refine logb_rpow_eq_mul_logb_of_pos ?_
                    norm_num
                _ = (3 : ℝ) * 1 := by
                    have : logb 10 (10) = 1 := by
                        refine logb_self_eq_one ?_
                        norm_num
                    rw [this]
                _ = 3 := by ring
        rw [this]
        ring


    constructor
    intro h

    have h6 : f x = g x := by
        unfold f g
        have :  logb 10 (x ^ (5 : ℕ) - 24) =  logb 10 (x ^ (5 : ℝ) - 24) := by
            norm_cast
        rw [this] at h
        exact h

    --Next we define another function h which is the difference of f and g.
    let h := fun y : ℝ ↦ f y - g y

    --By monotonicity of f and g, it follows that h is monotonic as well.
    have h7 : StrictMonoOn h (Set.Ioi (3 : ℝ)) := by
        intro a ha b hb hab
        have f_incr := h1 ha hb hab
        have g_decr := h2 ha hb hab
        exact sub_lt_sub (h1 ha hb hab) (h2 ha hb hab)

    --Clearly h 4 = 0.
    have h8 : h 4 = 0 := by
        calc
            _ = f 4 - g 4 := by exact rfl
            _ = 0 := by exact sub_eq_zero_of_eq h5

    --Clearly h x = 0.
    have h9 : h x = 0 := by
        calc
            _ = f x - g x := by exact rfl
            _ = 0 := by exact sub_eq_zero_of_eq h6

    --Since h is monotonic in (3 , ∞), it's injective in (3, ∞).
    have h10 : ∀ a b : Set.Ioi (3 : ℝ), h (a : ℝ) = h (b : ℝ) → (a : ℝ) = (b : ℝ) := by
        intro a b p
        have inj : Set.InjOn h (Set.Ioi 3) := h7.injOn
        exact inj a.property b.property p

    --Now we use injectivity of h to show that x = 4.
    have h₄ : (4 : ℝ) ∈ ↑(Set.Ioi (3 : ℝ)) := by norm_num
    have hx': (x : ℝ) ∈ ↑(Set.Ioi (3 : ℝ)) := by exact hx


    have h4x : h (4 : ℝ) = h (x : ℝ) := by rw [h8, h9]
    have h4_mem : (4 : ℝ) ∈ Set.Ioi 3 := h₄
    have x_mem : x ∈ Set.Ioi 3 := hx'
    have h4x_subtype : ↑(⟨4, h₄⟩ : ↑(Set.Ioi (3 : ℝ))) = ↑(⟨x, hx'⟩ : ↑(Set.Ioi (3 : ℝ))) := by
      exact SetCoe.ext (h10 ⟨4, h₄⟩ ⟨x, hx'⟩ h4x)

    cases h4x_subtype
    rfl

    --Conversely suppose x = 4. Then by log rules the result follows.
    intro h
    rw [h]
    norm_num
    have : 1000 = (10 : ℝ)^(3 : ℝ) := by norm_num
    rw [this]
    have : logb 10 (10 ^ (3 : ℝ)) = 3 := by
                calc
                    _ = (3 : ℝ) * logb 10 (10) := by
                        refine logb_rpow_eq_mul_logb_of_pos ?_
                        norm_num
                    _ = (3 : ℝ) * 1 := by
                        have : logb 10 (10) = 1 := by
                            refine logb_self_eq_one ?_
                            norm_num
                        rw [this]
                    _ = 3 := by ring
    rw [this]
    ring