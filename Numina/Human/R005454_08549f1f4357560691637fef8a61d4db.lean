import Mathlib

open Real

/- How many values of $x,-19<x<98$, satisfy

$$
\cos ^{2} x+2 \sin ^{2} x=1 ?
$$-/
theorem algebra_608375 :
    {x : ℝ | -19 < x ∧ x < 98 ∧ cos x ^ 2 + 2 * sin x ^ 2 = 1}.ncard = 38 := by
  -- Rewrite the expression
  have g : {x | -19 < x ∧ x < 98 ∧ cos x ^ 2 + 2 * sin x ^ 2 = 1} = {x : ℝ | -19 < x ∧ x < 98 ∧ ∃ n : ℤ, n * π = x} := by
    conv =>
      congr
      . ext x
        congr
        ext x
        rw [two_mul, <-add_assoc, cos_sq_add_sin_sq]
        simp
        rw [sin_eq_zero_iff]
      . ext x
        congr
        ext x
  -- Create a bijection between a set of integers.
  let φ : {n : ℤ | -6 ≤ n ∧ n ≤ 31} → {x : ℝ | -19 < x ∧ x < 98 ∧ ∃ n : ℤ, n * π = x} := fun n ↦ ⟨n * π, ?_⟩
  pick_goal 2
  -- Show that n * π belongs to the set on the right if n belongs to the set on the left, so that φ is a function.
  obtain ⟨n, h₀, h₁⟩ := n
  simp
  refine ⟨?_, ?_⟩
  -- We have -19 < n * π.
  calc
    -19 < -6 * 3.15 := by norm_num
    _ < -6 * π := by linarith only [Real.pi_lt_d2]
    _ ≤ n * π := by rw [mul_le_mul_iff_of_pos_right]; norm_cast; exact pi_pos
  -- We have n * π < 98.
  calc
    n * π ≤ 31 * π := by rw [mul_le_mul_iff_of_pos_right]; norm_cast; exact pi_pos
    _ < 31 * 3.15 := by linarith only [Real.pi_lt_d2]
    _ < 98 := by norm_num
  -- With bijection φ, the two sets have the same cardinality.
  have h₀ : {x : ℝ | -19 < x ∧ x < 98 ∧ ∃ n : ℤ, n * π = x}.encard = {n : ℤ | -6 ≤ n ∧ n ≤ 31}.encard := by
    refine (Set.encard_congr (Equiv.ofBijective φ ⟨fun a b heq ↦ ?_, fun ⟨x, h₀, h₁, n, h₂⟩ ↦ ?_⟩)).symm
    . -- Show that φ is injective.
      obtain ⟨a, h₀, h₁⟩ := a
      obtain ⟨b, h₂, h₃⟩ := b
      simp [φ] at heq
      congr
      obtain heq | nsense := heq
      tauto
      linarith only [pi_pos, nsense]
    . -- Show that φ is surjective.
      simp [φ]
      use n
      -- We have -6 ≤ n, otherwise contradiction.
      have h₃ : -6 ≤ n := by
        by_contra!
        have weq : x ≤ -19 := by
          calc
            x = n * π := by rw [h₂]
            _ ≤ -7 * π := by rw [mul_le_mul_iff_of_pos_right]; rw [show (-7 : ℝ) = (-7 : ℤ) by norm_cast, Int.cast_le]; omega; exact pi_pos
            _ ≤ -7 * 3.14 := by linarith only [Real.pi_gt_d2]
            _ ≤ -19 := by norm_num
        linarith only [h₀, weq]
      -- We have n ≤ 31, otherwise contradiction.
      have h₃ : n ≤ 31 := by
        by_contra!
        have weq : 98 ≤ x := by
          calc
            98 ≤ 32 * 3.14 := by norm_num
            _ ≤ 32 * π := by linarith only [Real.pi_gt_d2]
            _ ≤ n * π := by rw [mul_le_mul_iff_of_pos_right]; rw [show (32 : ℝ) = (32 : ℤ) by norm_cast, Int.cast_le]; omega; exact pi_pos
            _ = x := by rw [h₂]
        linarith only [h₁, weq]
      tauto
  rw [g.symm] at h₀
  clear g
  have h₁ : {n : ℤ | -6 ≤ n ∧ n ≤ 31}.ncard = 38 := by
    calc
      {n : ℤ | -6 ≤ n ∧ n ≤ 31}.ncard = (Set.Icc (-6) 31).ncard := by simp [Set.Icc]
      _ = (Finset.Icc (-6) 31).card := by rw [<-Finset.coe_Icc, Set.ncard_coe_Finset]
      _ = 38 := by apply Int.card_Icc
  have h₂ : {n : ℤ | -6 ≤ n ∧ n ≤ 31}.Finite := by
    apply Set.finite_of_ncard_pos
    rw [h₁]
    norm_num
  replace h₁ : {n : ℤ | -6 ≤ n ∧ n ≤ 31}.encard = 38 := by
    rw [Set.Finite.encard_eq_coe, <-Set.ncard_def, h₁]
    norm_num
    exact h₂
  rw [h₁] at h₀
  rw [Set.Finite.encard_eq_coe, <-Set.ncard_def] at h₀
  norm_cast at h₀ ⊢
  apply Set.finite_of_encard_eq_coe h₀
