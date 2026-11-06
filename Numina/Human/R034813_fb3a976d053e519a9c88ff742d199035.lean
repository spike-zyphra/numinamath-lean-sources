import Mathlib

open Real Set
open scoped Real

/- 【Example 5】Prove: When $\alpha$ is in the first or third quadrant,
$$
\left|\sin \left(\alpha+\frac{\pi}{4}\right)\right|>\frac{\sqrt{2}}{2} .
$$ -/
theorem inequalities_191587 (α : ℝ) (hα : α ∈ Ioo 0 (π / 2) ∪ Ioo π (3 * π / 2)) :
    |sin (α + π / 4)| > sqrt 2 / 2 := by
  let z:=α + π / 4
  have hz : z = α + π / 4 := rfl
  rw [←hz , GT.gt , ←sin_pi_div_four ]
  have h1 : -(π / 2) ≤ π / 4 := by
    linarith [Real.pi_pos]
  have h2 :- π / 4 ≤ π / 2 := by
    linarith [Real.pi_pos]
  have h_shared1 (a: ℝ): ∀ (h3:a ∈ Ioo (π/4) (π/2)), sin (π/4) < sin a := by-- z ∈ (π/4, π/2)
    intro h3
    exact sin_lt_sin_of_lt_of_le_pi_div_two h1 h3.2.le h3.1
  have h_shared2 (a: ℝ): ∀ (h4:a ∈ Ico (π/2) (3*π/4)), sin (π/4) < sin a := by-- z ∈ [π/2, 3π/4)
    intro h4
    rw [← Real.sin_pi_sub ,show π - π / 4 =3 * π / 4 by ring]
    have ha1_1  :sin a > sin (3 * π / 4) := by
      let a1:=a-π
      have h_a1: a1= a-π := by rfl
      have ha1_2 :a1 ∈ Ico (-(π / 2)) (- π / 4) := by
        rw[h_a1]
        constructor 
        · linarith [h4.1]
        · linarith [h4.2]
      have ha1_3 : sin a1 < sin (- π / 4) := by
        exact sin_lt_sin_of_lt_of_le_pi_div_two ha1_2.1 h2 ha1_2.2
      rw [h_a1 ,show (-π/4) =3*π/4 -π by ring ,Real.sin_sub_pi ,Real.sin_sub_pi] at ha1_3
      simp at ha1_3
      rw[GT.gt]
      exact ha1_3
    exact ha1_1
  cases' hα with hα_neg hα_pos
  · have hz1 : z ∈ Ioo (π/4) (3*π/4) := by--α∈ Ioo 0 (π / 2),z∈ Ioo (π/4) (3*π/4)
      constructor
      · linarith [hα_neg.1]
      · linarith [hα_neg.2]
    have h_split : z ∈ Ioo (π/4) (π/2) ∨ z ∈ Set.Ico (π/2) (3*π/4) := by
      rcases lt_or_le z (π / 2) with hz_left | hz_right
      · left; exact ⟨hz1.1, hz_left⟩
      · right; exact ⟨hz_right, hz1.2⟩
    rw[lt_abs]
    left
    cases' h_split with hz_left hz_right
    · -- z ∈ (π/4, π/2)
      exact h_shared1 (z: ℝ) hz_left
    · -- z ∈ [π/2, 3π/4)
      exact h_shared2 (z: ℝ) hz_right
  · have hz2 : z ∈ Ioo (5*π/4) (7*π/4) := by--α∈ Ioo π (3*π/2),z∈ Ioo (5*π/4) (7*π/4)
      constructor
      · linarith [hα_pos.1]
      · linarith [hα_pos.2]
    have h_split : z ∈ Ioo (5*π / 4) (3*π / 2) ∨ z ∈ Set.Ico (3*π/2) (7*π/4) := by
      rcases lt_or_le z (3*π / 2) with hz_left | hz_right
      · left; exact ⟨hz2.1, hz_left⟩
      · right; exact ⟨hz_right, hz2.2⟩
    rw[lt_abs]
    right
    cases' h_split with hz_left hz_right
    · -- z ∈ (5π/4, 3π/2) → z2 ∈ (π/4, π/2)
      let z2:= z-π
      have h_z2: z2= z-π := by rfl
      have hz2_1 :z2 ∈ Ioo (π / 4) (π / 2) := by
        rw[h_z2]
        constructor 
        · linarith [hz_left.1]
        · linarith [hz_left.2]
      have hz2_2 : sin (π / 4) < sin z2  := by
        exact h_shared1 (z2: ℝ) hz2_1
      rw [h_z2 ,Real.sin_sub_pi] at hz2_2
      exact hz2_2
    · -- z ∈ [3π/2, 7π/4) → z3 ∈ [π/2, 3π/4)
      let z3:=z-π
      have h_z3: z3= z-π :=by rfl
      have hz3_1 :z3 ∈ Ico (π / 2) (3*π / 4) := by
        rw[h_z3]
        constructor 
        · linarith [hz_right.1]
        · linarith [hz_right.2]
      have hz3_2 : sin (π / 4) < sin z3 := by
        exact h_shared2 (z3: ℝ) hz3_1
      rw [h_z3 ,Real.sin_sub_pi ] at hz3_2
      exact hz3_2