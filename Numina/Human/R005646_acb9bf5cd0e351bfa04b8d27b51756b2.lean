import Mathlib

open Complex

/-Let $O_{1}$ and $O_{2}$ be concentric circles with radii 4 and 6 , respectively. A chord $A B$ is drawn in $O_{1}$ with length 2. Extend $A B$ to intersect $O_{2}$ in points $C$ and $D$. Find $C D$.-/
theorem geometry_609231 {A B C D : ℂ} (hO1 : A.abs = 4 ∧ B.abs = 4)
    (hAB : ∃ s : ℝ, 0 < s ∧ A = s + I ∧ B = s - I)
    (hO2 : C.abs = 6 ∧ D.abs = 6) (hext : C.re = A.re ∧ D.re = A.re)
    (hCD : ∃ t : ℝ, 0 < t ∧ C.im = t ∧ D.im = -t) : dist C D = 2 * √21 := by
-- Extend the all of the assumptions
  rcases hO1 with ⟨rA, rB⟩; rcases hO2 with ⟨rC, rD⟩
  rcases hAB with ⟨s, ⟨spos, hA, hB⟩⟩
  rcases hext with ⟨reC, reD⟩
  rcases hCD with ⟨t, ⟨tpos, hC, hD⟩⟩
-- Substitute $A$ in `rA` and solve for $s=√15$
  simp [hA] at reC reD rA
  simp [abs_eq_sqrt_sq_add_sq] at rA
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)] at rA
  rw [Real.sq_sqrt] at rA; replace rA : s ^ 2 = √15 ^ 2 := by
    norm_num; linarith only [rA]
  rw [pow_left_inj₀] at rA; simp [rA] at *
-- Substitute $C$ in `rC` and solve for $t=√21$
  simp [abs_eq_sqrt_sq_add_sq, reC, hC] at rC
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)] at rC
  rw [Real.sq_sqrt] at rC; replace rC : t ^ 2 = √21 ^ 2 := by
    norm_num; linarith only [rC]
  rw [pow_left_inj₀] at rC; simp [rC] at *
-- Put together what we have to compute the final result
  simp [dist_eq, abs_eq_sqrt_sq_add_sq, reC, reD, hC, hD]
  ring; all_goals positivity