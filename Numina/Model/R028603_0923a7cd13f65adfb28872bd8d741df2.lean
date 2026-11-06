import Mathlib

noncomputable def cbrt (x : ℝ) : ℝ :=
  if x ≥ 0 then x ^ (1 / 3 : ℝ) else -(-x) ^ (1 / 3 : ℝ)

theorem algebra_11096 (k : ℝ) (S : Set (ℝ × ℝ)) (h : ∀ y z, (y, z) ∈ S ↔ y^3 * cbrt z = k) (h1 : (2, 1) ∈ S) :
    {z | (4, z) ∈ S} = {1 / 512} := by
  have h1' : (2 : ℝ) ^ 3 * cbrt 1 = k := by
    have h21_in : (2,1) ∈ S := h1 
    rw [h] at h21_in 
    linarith
  have h2 : (cbrt 1 : ℝ) = 1 := by
    unfold cbrt 
    norm_num
  have hk : k = 8 := by
    rw [h2] at h1'
    nlinarith
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (4, z) ∈ S, prove z = 1 / 512
    intro h2_in
    -- From hypothesis `h : \forall y z, (y , z ) : s \in \iff ...`. For y=4, z=z, hypothesis to be converted is `4^3 * cbrt z =k`.
    have h3 : (4 : ℝ) ^3 * cbrt z = k := by 
      have h4 : (4, z) ∈ S := by 
        simpa using h2_in 
      rw [h] at h4 
      linarith
    -- Now to solve the value of `z`. Substituting `k=8` gives `64 * cbrt z =8`, resulting in `cbrt z = 1/8`.
    rw [hk] at h3 
    -- positivity check
    have h4 : z ≥ (0 : ℝ) := by 
      by_contra h6 
      push_neg at h6 
      have h7 : cbrt z < 0 := by 
        have h8 : z < (0 : ℝ) := by 
          linarith 
        unfold cbrt 
        rw [if_neg (show z ≥ (0 : ℝ) → False by 
          intro h10 
          nlinarith 
        )] 
        have h9 : -z > (0 : ℝ) := by 
          linarith 
        have h10 : (-z : ℝ) ^ (1 / 3 : ℝ) > 0 := by 
          apply Real.rpow_pos_of_pos 
          all_goals linarith 
        nlinarith 
      nlinarith [h7, h3]
    -- Now calculation complete
    have h5 : cbrt z = (1 / 8 : ℝ) := by 
      nlinarith 
    -- Now, to get the value of z from cbrt z
    have h10 : (z : ℝ) = (1 / 512 : ℝ) := by
      have h11 : z ≥ (0 : ℝ) := h4 
      have h12 : cbrt z = z ^ (1 / 3 : ℝ) := by
        unfold cbrt 
        rw [if_pos (show z ≥ (0 : ℝ) by linarith)]
      have h13 : z ^ (1 / 3 : ℝ) = (1 / 8 : ℝ) := by
        linarith [h5, h12]
      -- Now take both sides ^3
      have h15 : z = (z ^ (1 / 3 : ℝ) ) ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        field_simp
        all_goals linarith
      rw [h13] at h15
      nlinarith 
    linarith 
  · -- Assume z = 1 / 512, prove (4, z) ∈ S
    intro hz
    -- Now prove from z=1/512
    rw [hz]
    -- From hypothesis `h : \forall y z, (y , z ) : s \in \iff ...`. For y=4, z=z, hypothesis to be converted is `4^3 * cbrt z =k`.
    have h5 : (4 : ℝ) ^3 * cbrt (1 / 512 : ℝ) = k := by
      rw [hk]
      have h6 : cbrt (1 / 512 : ℝ) = (1 / 8 : ℝ) := by
        unfold cbrt 
        rw [if_pos (show (1 / 512 : ℝ) ≥ 0 by norm_num)]
        have h7 : (1 / 512 : ℝ) ^ (1 / 3 : ℝ) = (1 / 8 : ℝ) := by
          rw [show (1 / 512 : ℝ) = (1 / 8 : ℝ) ^ (3 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num 
          all_goals norm_num 
        linarith 
      rw [h6]
      all_goals norm_num 
    -- Now to complete the reasoning, by proving that `(4,1/512)` is in S.
    have h4in : (4, (1 / 512 : ℝ)) ∈ S := by 
      rw [h]
      linarith [h5] 
    exact h4in