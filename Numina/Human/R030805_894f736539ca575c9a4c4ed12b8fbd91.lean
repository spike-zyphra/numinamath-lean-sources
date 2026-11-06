import Mathlib

open Real Polynomial

/-Find the minimum distance from the point $(0,5 / 2)$ to the graph of $y=x^{4} / 8$.-/
theorem calculus_611098 : let f : ℝ → (Fin 2 → ℝ) := fun x => ![x, x ^ 4 / 8];
    IsLeast {d : ℝ | ∃ P ∈ f '' Set.univ, d =
    dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm (![0, 5 / 2])) ((EuclideanSpace.equiv (Fin 2) ℝ).symm P)} (√17 / 2) := by
-- Simplify `IsLeast` to an existential goal and a lower bound goal, simplify the distance functions in the goals
  simp [IsLeast, lowerBounds, EuclideanSpace.dist_eq, Real.dist_eq]
  constructor
  -- Fulfill the existential goal with $2$ and check the equality holds true
  · use 2; norm_num; congr
    symm; rw [Real.sqrt_eq_iff_eq_sq]
    all_goals norm_num
-- To show the lower bound goal, we first define a function $g$ and study its minimum when $x≥0$
  intro x; rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
  rw [div_pow, sq_sqrt, sq_sqrt, ← sub_nonneg]; ring_nf
  let g : ℝ → ℝ := fun z => 2 + z + z ^ 2 * (-5 / 8) + z ^ 4 * (1 / 64)
-- Prove some basic properties about $g$
  have gcont : Continuous g := by dsimp [g]; continuity
  have gdiff : Differentiable ℝ g := by
    dsimp [g]; have : (fun z : ℝ => 2 + z + z ^ 2 * (-5 / 8) + z ^ 4 * (1 / 64)) =
    (fun z => Polynomial.eval z (C 2 + X + X ^ 2 * C (-5 / 8) + X ^ 4 * C (1 / 64))) := by
      rw [funext_iff]; intro z; simp; ring
    rw [this]; apply Polynomial.differentiable
  have gder : ∀ z, deriv g z = 16⁻¹ * (z - 4) * (z + 2 + 2 * √2) * (z + 2 - 2 * √2) := by
    intro z; rw [mul_assoc, ← sq_sub_sq, mul_pow]
    norm_num; dsimp [g]; repeat rw [deriv_add]
    simp; ring; any_goals simp
    apply DifferentiableAt.add; any_goals simp
    apply Differentiable.differentiableAt
    have : (fun z : ℝ => 2 + z + z ^ 2 * (-5 / 8)) =
    (fun z => Polynomial.eval z (C 2 + X + X ^ 2 * C (-5 / 8))) := by
      rw [funext_iff]; intro z; simp; ring
    rw [this]; apply Polynomial.differentiable
-- Prove that $g$ is decreasing on $[-2+2√2, 4]$
  have ganti : AntitoneOn g (Set.Icc (-2 + 2 * √2) 4) := by
    apply antitoneOn_of_deriv_nonpos
    · apply convex_Icc
    · exact gcont.continuousOn
    · exact gdiff.differentiableOn
    simp; intro z zgt zlt; rw [gder]
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonpos_of_nonneg
      apply mul_nonpos_of_nonneg_of_nonpos; positivity
      linarith only [zlt]
      apply add_nonneg; suffices : 0 < 2 * √2
      · linarith only [this, zgt]
      all_goals positivity
    linarith only [zgt]
-- Prove that $g$ is increasing on $[0, -2 + 2 * √2]$
  have gmono1 : MonotoneOn g (Set.Icc 0 (-2 + 2 * √2)) := by
    apply monotoneOn_of_deriv_nonneg
    · apply convex_Icc
    · exact gcont.continuousOn
    · exact gdiff.differentiableOn
    simp; intro z zgt zlt; rw [gder]
    apply mul_nonneg_of_nonpos_of_nonpos
    · apply mul_nonpos_of_nonpos_of_nonneg
      apply mul_nonpos_of_nonneg_of_nonpos; positivity
      suffices : -2 + 2 * √2 < 4
      · linarith only [this, zlt]
      rw [← lt_sub_iff_add_lt']; norm_num
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [mul_pow]; all_goals norm_num
      positivity
    linarith only [zlt]
-- Prove that $g$ is increasing when $x≥4$
  have gmono2 : MonotoneOn g (Set.Ici 4) := by
    apply monotoneOn_of_deriv_nonneg
    · apply convex_Ici
    · exact gcont.continuousOn
    · exact gdiff.differentiableOn
    simp; intro z zgt; rw [gder]
    repeat apply mul_nonneg
    any_goals positivity
    linarith only [zgt]
    suffices : -2 + 2 * √2 < 4
    · linarith only [this, zgt]
    rw [← lt_sub_iff_add_lt']; norm_num
    rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    rw [mul_pow]; all_goals norm_num
-- Prove that $g$ is always nonnegative when $x$ is nonnegative
  have gmin : ∀ z ≥ 0, 0 ≤ g z := by
    intro z zpos; rcases le_or_gt z (-2+2*√2) with h|h
    · calc
        _ ≤ g 0 := by simp [g]
        _ ≤ _ := by
          apply gmono1; any_goals simp
          exact ⟨zpos, (by linarith only [h])⟩
          exact zpos
    rcases le_or_gt z 4 with h'|h'
    · calc
        _ ≤ g 4 := by simp [g]; norm_num
        _ ≤ _ := by
          apply ganti; any_goals simp
          · exact ⟨by linarith only [h], h'⟩
          norm_num; rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
          rw [mul_pow]; any_goals norm_num
          exact h'
    calc
      _ ≤ g 4 :=  by simp [g]; norm_num
      _ ≤ _ := by
        apply gmono2; any_goals simp
        all_goals linarith only [h']
-- Specialize `gmin` at $x^2$, the goal follows
  specialize gmin (x ^ 2) (by positivity)
  dsimp [g] at gmin; ring_nf at gmin; exact gmin
  all_goals positivity
