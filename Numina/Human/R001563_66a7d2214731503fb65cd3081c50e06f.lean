import Mathlib

open Real


/- If X, Y are in AB, Z is in XY, and |YZ| = 3|XZ|, we prove that |AZ|=(3|AX|+|AY|)/4 -/
lemma dist_of_ratio_of_mem_segment {A B X Y Z : EuclideanSpace ℝ (Fin d)} (hX : X ∈ segment ℝ A B) (hY : Y ∈ segment ℝ A B)
    (hZ : Z ∈ segment ℝ X Y) (hXY : dist Y Z = 3 * dist X Z) :
    dist A Z = (3 * dist A X + dist A Y) / 4 := by
  -- We can express X, Y, Z in terms of A and B.
  -- Assume Z = aX+bY, where a, b ≥ 0 and a + b ≤ 1.
  obtain ⟨a, b, ha, hb, hab, hZ⟩ := hZ
  have hab : a = 1 - b := by rw [←hab]; ring
  -- Since |YZ| = 3|XZ|, we have a|XY|=3b|XY|
  have hXZ : X - Z = (1 - a) • (X - Y) := by
    rw [←hZ, smul_sub]
    rw [hab]
    module
  have hYZ : Y - Z = a • (Y - X) := by
    rw [←hZ, smul_sub]
    rw [hab]
    module
  rw [dist_eq_norm, dist_eq_norm, hXZ, hYZ, norm_smul, norm_smul, norm_sub_rev] at hXY
  apply sub_eq_zero.mpr at hXY
  simp [←mul_assoc, ←sub_mul] at hXY
  rcases hXY with hXY | hXY
  · -- If |XY| ≠ 0, we have a = 3b= 3(1-a) → a = 3 / 4, b = 1 / 4.
    -- Therefore, Z = (3 / 4) • X + (1 / 4) • Y.
    rw [abs_of_nonneg ha, abs_of_nonneg (by rw [hab]; simp [hb])] at hXY
    have ha : a = 3 / 4 := by linarith only [hXY]
    have hb : b = 1 / 4 := by
      rw [hab] at ha
      linarith only [ha]
    simp [ha, hb] at hZ
    -- Assme that X = aA + bB, Y = a'A + b'B, where a', b' ≥ 0 and a' + b' ≤ 1.
    obtain ⟨a, b, ha, hb, hab, hX⟩ := hX
    have hAX : A - X = (1 - a) • (A - B) := by
      rw [←hX, smul_sub]
      nth_rw 2 [←hab]
      module
    rw [←hX] at hZ
    obtain ⟨a', b', ha', hb', hab', hY⟩ := hY
    have hAY : A - Y = (1 - a') • (A - B) := by
      rw [←hY, smul_sub]
      nth_rw 2 [←hab']
      module
    rw [←hY] at hZ
    have hZ : Z = (3 / 4 * a + 1 / 4 * a') • A + (3 / 4 * b + 1 / 4 * b') • B := by
      rw [←hZ]
      module
    have hAZ : A - Z = (1 - (3 / 4 * a + 1 / 4 * a')) • (A - B) := by
      have ha : a = 1 - b := by
        rw [←hab]; ring
      have ha' : a' = 1 - b' := by
        rw [←hab']; ring
      rw [hZ, smul_sub, ha, ha']
      module
    -- It suffices to show that (1 - (3 / 4 * a + 1 / 4 * a')) |AB|= 3 / 4 * (1 - a) |AB| + 1 / 4 * (1 - a') |AB|, which holds trivially.
    simp [dist_eq_norm, hAX, hAY, hAZ, norm_smul]
    rw [←mul_assoc, ←add_mul, mul_div_right_comm]
    congr
    rw [abs_of_nonneg, abs_of_nonneg, abs_of_nonneg]
    · ring_nf
    · rw [←hab']
      simp [hb']
    · rw [←hab]
      simp [hb]
    · simp
      trans 3 / 4 * 1 + 4⁻¹ * 1
      · gcongr
        · rw [←hab]
          simp [hb]
        · rw [←hab']
          simp [hb']
      · norm_num
  · -- If X = Y, then the result holds trivially.
    apply sub_eq_zero.mp at hXY
    simp [hXY] at hZ ⊢
    simp [←hZ, ←add_smul, hab]
    ring

/- If n ≤ 1 ∧ |AZ| = 3k/4^(n+1) ∨ (3k-2)/4^(n + 1) for some k, we prove that Z can be obtained by the iterating step.  -/
lemma subset_of_n_le_1 {d : ℕ} {A B : EuclideanSpace ℝ (Fin d)} (hAB : dist A B = 1)
    {iter : Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d))}
    (hiter : iter = fun M => {Z | ∃ X ∈ M, ∃ Y ∈ M, Z ∈ segment ℝ X Y ∧ dist Y Z = 3 * dist X Z}) (hn : n ≤ 1) :
    {X | X ∈ segment ℝ A B ∧ ∃ k : ℕ, dist A X = 3 * ↑k / 4 ^ (n + 1) ∨ dist A X = (3 * ↑k - 2) / 4 ^ (n + 1)} ⊆ iter {X | X ∈ segment ℝ A B ∧ ∃ k : ℕ, dist A X = 3 * ↑k / 4 ^ n ∨ dist A X = (3 * ↑k - 2) / 4 ^ n} := by

  have distAB {a b c d : ℝ} (hab : a + b = 1) (hcd : c + d = 1) :
      dist (a • A + b • B) (c • A + d • B) = |a - c| := by
    have : a • A + b • B - (c • A + d • B) = (a - c) • (A - B) := by
      have ha : a = 1 - b := by
        rw [←hab]; ring
      have hc : c = 1 - d := by
        rw [←hcd]; ring
      rw [ha, hc]
      module
    rw [dist_eq_norm, this, norm_smul, norm_eq_abs]
    simp [←dist_eq_norm, hAB]

  have distA {c d : ℝ} (hcd : c + d = 1) :
      dist A (c • A + d • B) = |1 - c| := by
    have : A = (1 : ℝ) • A + (0 : ℝ) • B := by module
    nth_rw 1 [this, distAB ?_ hcd]
    simp

  have distB {c d : ℝ} (hcd : c + d = 1) :
      dist B (c • A + d • B) = |c| := by
    have : B = (0 : ℝ) • A + (1 : ℝ) • B := by module
    nth_rw 1 [this, distAB ?_ hcd]
    simp
    simp

  intro Z hZ
  simp [hiter]
  obtain ⟨hZ_mem, k, hdistZ⟩ := hZ
  obtain ⟨a, b, ha, hb, hab, hZ⟩ := hZ_mem
  have hab : a = 1 - b := by
    rw [←hab]; ring
  have : dist A Z = b := by
    have hZ : A - Z = b • (A - B) := by
      rw [←hZ, smul_sub]
      rw [hab]
      module
    rw [dist_eq_norm, hZ, norm_smul]
    simp [abs_of_nonneg hb]
    rw [dist_eq_norm] at hAB
    simp [hAB]
  rw [this] at hdistZ
  rcases hdistZ with hdistZ | hdistZ
  · interval_cases n
    · -- If n = 0, then |AZ| = 3k/4, we have k ≤ 1
      simp at hdistZ ⊢
      have hk : k ≤ 1 := by
        have hb : b ≤ 1 := by
          rename_i h
          rw [←h]
          simp
          exact ha
        simp [hdistZ] at hb
        apply div_le_iff₀ (by simp) |>.mp at hb
        simp at hb
        norm_cast at hb
        trans 4 / 3
        · apply Nat.le_div_iff_mul_le (by simp) |>.mpr
          rw [mul_comm]
          exact hb
        · simp
      interval_cases k
      · -- k = 1, X = Y = A works.
        simp at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        simp [←hZ]
        use A, ?_, A, ?_
        · simp
        · simp
          exact left_mem_segment ℝ A B
        · simp
          exact left_mem_segment ℝ A B
      · -- k = 2, X = B, Y = A works.
        simp at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use B, ?_, A, ?_
        constructor
        · use 3 / 4, 1 / 4
          norm_num
          module
        · have : A - ((1 / 4 : ℝ) • A + (3 / 4 : ℝ) • B) = (3 / 4 : ℝ) • (A - B) := by module
          rw [dist_eq_norm, this, norm_smul]
          have : B - ((1 / 4 : ℝ) • A + (3 / 4 : ℝ) • B) = (-1 / 4 : ℝ) • (A - B) := by module
          rw [dist_eq_norm, this, norm_smul]
          norm_num
          simp [←dist_eq_norm, hAB]
          norm_num
        · constructor
          · exact right_mem_segment ℝ A B
          · use 1
            right
            simp [hAB]
            norm_num
        · constructor
          · exact left_mem_segment ℝ A B
          · simp
    · -- If n = 1, then |AZ| = 3k/16, we have k ≤ 5
      simp at hdistZ ⊢
      have hk : k ≤ 5 := by
        have hb : b ≤ 1 := by
          rename_i h
          rw [←h]
          simp
          exact ha
        simp [hdistZ] at hb
        apply div_le_iff₀ (by simp) |>.mp at hb
        simp at hb
        norm_cast at hb
        rw [mul_comm] at hb
        apply Nat.le_div_iff_mul_le (by simp) |>.mpr at hb
        simp at hb
        exact hb
      interval_cases k
      · -- If k = 0, then X = Y =A.
        simp at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        rw [←hZ]
        use A, ?_, A, ?_
        · simp
        · constructor
          · exact left_mem_segment ℝ A B
          · use 0
            simp
        · constructor
          · exact left_mem_segment ℝ A B
          · use 0
            simp
      · -- If k = 1, then X = A, Y = 1/4A+3/4B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use A, ?_, (1 / 4 : ℝ) • A + (3 / 4 : ℝ) • B, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
            module
          · rw [distAB, distA]
            norm_num
            rw [abs_div, abs_div]
            all_goals norm_num
        · constructor
          · exact left_mem_segment ℝ A B
          · use 0
            simp
        · constructor
          · use 1 / 4, 3 / 4
            norm_num
          · use 1
            left
            rw [distA]
            all_goals norm_num
      · -- If k = 2, then X = 3/4A+1/4B, Y = 1/4A+3/4B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use (3 / 4 : ℝ) • A + (1 / 4 : ℝ) • B, ?_, (1 / 4 : ℝ) • A + (3 / 4 : ℝ) • B, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
            module
          · rw [distAB, distAB]
            norm_num
            rw [abs_div, abs_div]
            all_goals norm_num
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
          · use 1
            right
            rw [distA]
            all_goals norm_num
        · constructor
          · use 1 / 4, 3 / 4
            norm_num
          · use 1
            left
            rw [distA]
            all_goals norm_num
      · -- If k = 3, then X = 1/4A+3/4B, Y = A
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use (1 / 4 : ℝ) • A + (3 / 4 : ℝ) • B, ?_, A, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
            module
          · rw [distAB, distA]
            all_goals norm_num
            rw [abs_div, abs_div]
            norm_num
        · constructor
          · use 1 / 4, 3 / 4
            norm_num
          · use 1
            left
            rw [distA]
            all_goals norm_num
        · constructor
          · exact left_mem_segment ℝ A B
          · use 0
            simp
      · -- If k =4, then X = B, Y = A.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use B, ?_, A, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
            module
          · rw [distA, distB]
            all_goals norm_num
            rw [abs_div, abs_div]
            norm_num
        · constructor
          · exact right_mem_segment ℝ A B
          · use 2
            right
            simp [hAB]
            norm_num
        · constructor
          · exact left_mem_segment ℝ A B
          · use 0
            simp
      · -- If k = 5, then X = B, Y = 1/4A+3/4B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use B, ?_, (1 / 4 : ℝ) • A + (3 / 4 : ℝ) • B, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
            module
          · rw [distAB, distB]
            all_goals norm_num
            rw [abs_div, abs_div]
            norm_num
        · constructor
          · exact right_mem_segment ℝ A B
          · use 2
            right
            simp [hAB]
            norm_num
        · constructor
          · use 1 / 4, 3 / 4
            norm_num
          · use 1
            left
            rw [distA]
            all_goals norm_num
  · -- If |AZ| = (3k - 2)/4^(n + 1), we still perform the same analysis.
    interval_cases n
    · -- If n = 0, then |AZ| = (3k - 2)/4, we have k ≤ 2
      simp at hdistZ ⊢
      have hk : k ≤ 2 := by
        have hb : b ≤ 1 := by
          rename_i h
          rw [←h]
          simp
          exact ha
        simp [hdistZ] at hb
        apply div_le_iff₀ (by simp) |>.mp at hb
        simp at hb
        norm_num at hb
        norm_cast at hb
        trans 6 / 3
        · apply Nat.le_div_iff_mul_le (by simp) |>.mpr
          rw [mul_comm]
          exact hb
        · simp
      interval_cases k
      · -- If k = 0, then |AZ| = -2/4, which is impossible.
        norm_num at hdistZ
        simp [hdistZ] at hb
        norm_num at hb
      · -- If k = 1, then X = A, Y = B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        norm_num at hab
        simp [←hZ, hdistZ, hab]
        use A, ?_, B, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
          · have : B - ((3 / 4 : ℝ) • A + (4⁻¹ : ℝ) • B) = (-3 / 4 : ℝ) • (A - B) := by
              module
            rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
            have : A - ((3 / 4 : ℝ) • A + (4⁻¹ : ℝ) • B) = (1 / 4 : ℝ) • (A - B) := by
              module
            rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one, abs_div, abs_div]
            norm_num
        · constructor
          · exact left_mem_segment ℝ A B
          · simp
        · constructor
          · exact right_mem_segment ℝ A B
          · use 1
            right
            simp [hAB]
            norm_num
      · -- If k = 2, then X= Y = B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        simp [←hZ]
        use B, ?_, B, ?_
        · simp
        · constructor
          · exact right_mem_segment ℝ A B
          · use 1
            right
            simp [hAB]
            norm_num
        · constructor
          · exact right_mem_segment ℝ A B
          · use 1
            right
            simp [hAB]
            norm_num
    · -- If n = 1, then |AZ| = (3k - 2)/16, we have k ≤ 6
      have hk : k ≤ 6 := by
        have hb : b ≤ 1 := by
          rename_i h
          rw [←h]
          simp
          exact ha
        simp [hdistZ] at hb
        apply div_le_iff₀ (by simp) |>.mp at hb
        simp at hb
        norm_num at hb
        norm_cast at hb
        trans 18 / 3
        · apply Nat.le_div_iff_mul_le (by simp) |>.mpr
          rw [mul_comm]
          exact hb
        · simp
      interval_cases k
      · -- If k = 0, then |AZ| = -2/16, which is impossible.
        norm_num at hdistZ
        simp [hdistZ] at hb
        norm_num at hb
      · -- If k = 1, X =A, Y = 3/4A+1/4B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use A, ?_, (3 / 4 : ℝ) • A + (1 / 4 : ℝ) • B, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
            module
          · rw [distA, distAB]
            all_goals norm_num
            rw [abs_div, abs_div]
            norm_num
        · constructor
          · exact left_mem_segment ℝ A B
          · use 0
            simp
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
          · use 1
            right
            rw [distA]
            all_goals norm_num
      · -- If k = 2, X =A ,Y =B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use A, ?_, B, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
          · rw [distA, distB]
            all_goals norm_num
            rw [abs_div, abs_div]
            norm_num
        · constructor
          · exact left_mem_segment ℝ A B
          · use 0
            simp
        · constructor
          · exact right_mem_segment ℝ A B
          · use 2
            right
            simp [hAB]
            norm_num
      · -- If k = 3, X = 3/4A+1/4B, Y = B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use (3 / 4 : ℝ) • A + (1 / 4 : ℝ) • B, ?_, B, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
            module
          · rw [distAB, distB]
            all_goals norm_num
            rw [abs_div, abs_div]
            norm_num
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
          · use 1
            right
            rw [distA]
            all_goals norm_num
        · constructor
          · exact right_mem_segment ℝ A B
          · use 2
            right
            simp [hAB]
            norm_num
      · -- If k = 4, X = 1/4A+3/4B, Y = 3/4A+1/4B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use (1 / 4 : ℝ) • A + (3 / 4 : ℝ) • B, ?_, (3 / 4 : ℝ) • A + (1 / 4 : ℝ) • B, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
            module
          · rw [distAB, distAB]
            all_goals norm_num
            rw [abs_div, abs_div]
            norm_num
        · constructor
          · use 1 / 4, 3 / 4
            norm_num
          · use 1
            left
            rw [distA]
            all_goals norm_num
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
          · use 1
            right
            rw [distA]
            all_goals norm_num
      · -- If k = 5, X = B, Y = 3/4A+1/4B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        norm_num at hZ
        rw [←hZ]
        use B, ?_, (3 / 4 : ℝ) • A + (1 / 4 : ℝ) • B, ?_
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
            module
          · rw [distAB, distB]
            all_goals norm_num
            rw [abs_div, abs_div]
            norm_num
        · constructor
          · exact right_mem_segment ℝ A B
          · use 2
            right
            simp [hAB]
            norm_num
        · constructor
          · use 3 / 4, 1 / 4
            norm_num
          · use 1
            right
            rw [distA]
            all_goals norm_num
      · -- If k = 6, X=Y=B.
        norm_num at hdistZ
        simp [hdistZ] at hab
        simp [hab, hdistZ] at hZ
        rw [←hZ]
        use B, ?_, B, ?_
        · simp
        · constructor
          · exact right_mem_segment ℝ A B
          · use 2
            right
            simp [hAB]
            norm_num
        · constructor
          · exact right_mem_segment ℝ A B
          · use 2
            right
            simp [hAB]
            norm_num

/- We show that if n ≥ 2 ∧ k < 4 ^ n and |AZ| = 3k/4^(n + 1), then Z can be obtained by one iteration. -/
lemma subset_of_k_lt_pow_n {d : ℕ} {A B Z : EuclideanSpace ℝ (Fin d)} (hAB : dist A B = 1)
    (hZ_mem : Z ∈ segment ℝ A B) {k : ℕ} (hk : k < 4 ^ n) (hdistZ : dist A Z = 3 * k / 4 ^ (n + 1))
    {iter : Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d))}
    (hiter : iter = fun M => {Z | ∃ X ∈ M, ∃ Y ∈ M, Z ∈ segment ℝ X Y ∧ dist Y Z = 3 * dist X Z}) (hn : n ≥ 2) :
    Z ∈ iter {X | X ∈ segment ℝ A B ∧ ∃ k : ℕ, dist A X = 3 * ↑k / 4 ^ n ∨ dist A X = (3 * ↑k - 2) / 4 ^ n} := by
  simp [hiter]
  obtain ⟨a, b, ha, hb, hab, hZ⟩ := hZ_mem
  have hab : a = 1 - b := by
    rw [←hab]; ring
  have : dist A Z = b := by
    have hZ : A - Z = b • (A - B) := by
      rw [←hZ, smul_sub]
      rw [hab]
      module
    rw [dist_eq_norm, hZ, norm_smul]
    simp [abs_of_nonneg hb]
    rw [dist_eq_norm] at hAB
    simp [hAB]
  rw [this] at hdistZ
  -- let b₁ := 3 * (k / 3 : ℕ) / 4 ^ n
  -- let b₂ := 3 * (k % 3 : ℕ) / 4 ^ n
  let b₁ : ℝ := 3 * (k / 3: ℕ) / 4 ^ n
  let b₂ : ℝ := 3 * (k % 3 : ℕ) / 4 ^ n
  have hb₁b₂ : b = 3 / 4 * b₁ + 1 / 4 * b₂ := by
    rw [hdistZ]
    simp [b₁, b₂]
    field_simp
    congr 1
    · rw [←mul_add]
      congr
      norm_cast
      exact Eq.symm (Nat.div_add_mod k 3)
    · ring
  -- let X = (1 - b₁) • A + b₁ • B
  -- let Y = (1 - b₂) • A + b₂ • B
  -- We verify that Z = (3 / 4) • X + (1 / 4) • Y.
  use (1 - b₁) • A + b₁ • B, ?_, (1 - b₂) • A + b₂ • B, ?_
  · constructor
    · use 3 / 4, 1 / 4
      norm_num
      rw [←hZ, hab]
      rw [hb₁b₂]
      module
    · have : ((1 - b₂) • A + b₂ • B - Z) = (b - b₂) • (A - B) := by
        rw [←hZ, hab]
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      have : ((1 - b₁) • A + b₁ • B - Z) = (b - b₁) • (A - B) := by
        rw [←hZ, hab]
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [hb₁b₂]
      trans |(3 / 4) * (b₁ - b₂)|
      · congr 1
        ring_nf
      trans 3 * |(1 / 4) * (b₂ - b₁)|
      · rw [abs_mul, abs_mul, ←mul_assoc]
        congr 1
        · rw [abs_of_nonneg, abs_of_nonneg]
          all_goals norm_num
        · rw [abs_sub_comm]
      · congr
        ring_nf
  · -- Note that 0 ≤ b₁, b₂ ≤ 1, therefore X, Y ∈ segment ℝ A B.
    constructor
    · use (1 - b₁), b₁
      split_ands
      · simp
        field_simp [b₁]
        trans k / 4 ^ n
        · gcongr
          norm_cast
          exact Nat.mul_div_le k 3
        · trans 4 ^ n / 4 ^ n
          · gcongr
            norm_cast
            apply le_of_lt hk
          · simp
      · positivity
      · ring
      · rfl
    · use k / 3
      left
      have : A - ((1 - b₁) • A + b₁ • B) = b₁ • (A - B) := by
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [abs_of_nonneg]
      positivity
  · constructor
    · use 1 - b₂, b₂
      split_ands
      · simp
        simp [b₂]
        trans 3 * 2 / 4 ^ n
        · gcongr
          norm_cast
          apply Nat.le_of_lt_succ
          apply Nat.mod_lt
          simp
        · trans 4 ^ n / 4 ^ n
          · gcongr
            norm_cast
            trans 4 ^ 2
            · simp
            · gcongr
              simp
          · simp
      · positivity
      · ring
      · rfl
    · use k % 3
      left
      have : A - ((1 - b₂) • A + b₂ • B) = b₂ • (A - B) := by
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [abs_of_nonneg]
      positivity

/-- We show that if n ≥ 2 ∧ k < 4 ^ n + 3 and |AZ| = (3 * k - 2) / 4 ^ (n + 1), then Z can be obtained by one iteration. -/
lemma subset_of_k_lt_pow_n' {d : ℕ} {A B Z : EuclideanSpace ℝ (Fin d)} (hAB : dist A B = 1)
    (hZ_mem : Z ∈ segment ℝ A B) {k : ℕ} (hdistZ : dist A Z = (3 * k - 2) / 4 ^ (n + 1)) (hk_le : k ≤ 4 ^ n + 3) (hk_ge : k ≥ 3)
    {iter : Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d))}
    (hiter : iter = fun M => {Z | ∃ X ∈ M, ∃ Y ∈ M, Z ∈ segment ℝ X Y ∧ dist Y Z = 3 * dist X Z}) (hn : n ≥ 2) :
    Z ∈ iter {X | X ∈ segment ℝ A B ∧ ∃ k : ℕ, dist A X = 3 * ↑k / 4 ^ n ∨ dist A X = (3 * ↑k - 2) / 4 ^ n} := by
  simp [hiter]
  obtain ⟨a, b, ha, hb, hab, hZ⟩ := hZ_mem
  have hab : a = 1 - b := by
    rw [←hab]; ring
  have : dist A Z = b := by
    have hZ : A - Z = b • (A - B) := by
      rw [←hZ, smul_sub]
      rw [hab]
      module
    rw [dist_eq_norm, hZ, norm_smul]
    simp [abs_of_nonneg hb]
    rw [dist_eq_norm] at hAB
    simp [hAB]
  rw [this] at hdistZ
  have hk_ge : k / 3 ≥ 1 := by
    trans 3 / 3
    · gcongr
    · norm_num
  -- let b₁ := (3 * (k / 3 - 1 : ℕ)) / 4 ^ n
  -- let b₂ := (3 * (k % 3 + 3 : ℕ) - 2) / 4 ^ n
  let b₁ : ℝ := (3 * (k / 3 - 1 : ℕ)) / 4 ^ n
  let b₂ : ℝ := (3 * (k % 3 + 3 : ℕ) - 2) / 4 ^ n
  have hb₁b₂ : b = 3 / 4 * b₁ + 1 / 4 * b₂ := by
    rw [hdistZ]
    simp [b₁, b₂]
    field_simp
    congr 1
    · have : k = k / 3 * 3 + k % 3 := by
        exact Eq.symm (Nat.div_add_mod' k 3)
      nth_rw 1 [this]
      simp
      apply sub_eq_zero.mp
      ring_nf
    · ring
  -- Set X = (1 - b₁) • A + b₁ • B
  -- Set Y = (1 - b₂) • A + b₂ • B
  -- We verify that Z = (3 / 4) • X + (1 / 4) • Y.
  use (1 - b₁) • A + b₁ • B, ?_, (1 - b₂) • A + b₂ • B, ?_
  · constructor
    · use 3 / 4, 1 / 4
      norm_num
      rw [←hZ, hab]
      rw [hb₁b₂]
      module
    · have : ((1 - b₂) • A + b₂ • B - Z) = (b - b₂) • (A - B) := by
        rw [←hZ, hab]
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      have : ((1 - b₁) • A + b₁ • B - Z) = (b - b₁) • (A - B) := by
        rw [←hZ, hab]
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [hb₁b₂]
      trans |(3 / 4) * (b₁ - b₂)|
      · congr 1
        ring_nf
      trans 3 * |(1 / 4) * (b₂ - b₁)|
      · rw [abs_mul, abs_mul, ←mul_assoc]
        congr 1
        · rw [abs_of_nonneg, abs_of_nonneg]
          all_goals norm_num
        · rw [abs_sub_comm]
      · congr
        ring_nf
  · -- Note that 0 ≤ b₁, b₂ ≤ 1, therefore X, Y ∈ segment ℝ A B.
    constructor
    · use (1 - b₁), b₁
      split_ands
      · simp
        field_simp [b₁]
        rw [mul_sub]
        trans (k - 3 * 1) / 4 ^ n
        · gcongr
          norm_cast
          exact Nat.mul_div_le k 3
        · trans 4 ^ n / 4 ^ n
          · gcongr
            simp
            apply sub_nonneg.mp
            ring_nf
            trans 3 - (4 ^ n + 3) + 4 ^ n
            · apply le_of_eq
              ring
            · gcongr
              norm_cast
          · simp
      · apply div_nonneg
        · field_simp
          exact hk_ge
        · positivity
      · ring
      · rfl
    · use k / 3 - 1
      left
      have : A - ((1 - b₁) • A + b₁ • B) = b₁ • (A - B) := by
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [abs_of_nonneg]
      simp [b₁]
      apply div_nonneg
      · field_simp
        assumption
      · positivity
  · constructor
    · use 1 - b₂, b₂
      split_ands
      · simp
        simp [b₂]
        trans (3 * (2 + 3) - 2) / 4 ^ n
        · gcongr
          norm_cast
          apply Nat.le_of_lt_succ
          apply Nat.mod_lt
          simp
        · trans 4 ^ n / 4 ^ n
          · gcongr
            norm_num
            norm_cast
            trans 4 ^ 2
            · simp
            · gcongr
              simp
          · simp
      · simp [b₂]
        apply div_nonneg
        · simp
          trans 3 * 3
          · norm_num
          · gcongr
            norm_cast
            simp
        · positivity
      · ring
      · rfl
    · use k % 3 + 3
      right
      have : A - ((1 - b₂) • A + b₂ • B) = b₂ • (A - B) := by
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [abs_of_nonneg]
      simp [b₂]
      apply div_nonneg
      · simp
        trans 3 * 3
        · norm_num
        · gcongr
          norm_cast
          simp
      · positivity

/- We show that if n ≥ 2 ∧ k ≥ 4 ^ n and |AZ| = 3k/4^(n + 1), then Z can be obtained by one iteration. -/
lemma subset_of_k_ge_pow_n {d : ℕ} {A B Z : EuclideanSpace ℝ (Fin d)} (hAB : dist A B = 1)
    (hZ_mem : Z ∈ segment ℝ A B) {k : ℕ} (hk : k ≥ 4 ^ n) (hdistZ : dist A Z = 3 * k / 4 ^ (n + 1))
    {iter : Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d))}
    (hiter : iter = fun M => {Z | ∃ X ∈ M, ∃ Y ∈ M, Z ∈ segment ℝ X Y ∧ dist Y Z = 3 * dist X Z}) :
    Z ∈ iter {X | X ∈ segment ℝ A B ∧ ∃ k : ℕ, dist A X = 3 * ↑k / 4 ^ n ∨ dist A X = (3 * ↑k - 2) / 4 ^ n} := by
  simp [hiter]
  obtain ⟨a, b, ha, hb, hab, hZ⟩ := hZ_mem
  have hab : a = 1 - b := by
    rw [←hab]; ring
  have : dist A Z = b := by
    have hZ : A - Z = b • (A - B) := by
      rw [←hZ, smul_sub]
      rw [hab]
      module
    rw [dist_eq_norm, hZ, norm_smul]
    simp [abs_of_nonneg hb]
    rw [dist_eq_norm] at hAB
    simp [hAB]
  rw [this] at hdistZ
  have hle : 4 * b ≥ (3 : ℝ) := by
    simp [hdistZ, pow_add]
    trans 4 * (3 * 4 ^ n / (4 ^ n * 4))
    · apply le_of_eq
      field_simp
      ring
    · gcongr
      norm_cast
  have hmul_le : 4 * a ≤ 1 := by
    simp [hab]
    linarith only [hle]
  -- let X := B
  -- let Y := (4 * a) • A + (1 - 4 * a) • B
  -- We verify that Z = (3 / 4) • X + (1 / 4) • Y.
  use B, ?_, (4 * a) • A + (1 - 4 * a) • B, ?_
  · constructor
    · use 3 / 4, 1 / 4
      norm_num
      rw [←hZ, hab]
      module
    · have : (4 * a) • A + (1 - 4 * a) • B - Z = (3 * a) • (A - B) := by
        rw [←hZ, hab]
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, abs_mul]
      simp [abs_of_nonneg ha, dist_eq_norm]
      have : B - Z = (b - 1) • (A - B) := by
        rw [←hZ, hab]
        module
      rw [this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one, abs_sub_comm, abs_of_nonneg, hab]
      rw [←hab]
      exact ha
  · -- Note that 0 ≤ 4 * a ≤ 1, therefore X, Y ∈ segment ℝ A B.
    constructor
    · exact right_mem_segment ℝ A B
    · use (4 ^ n + 2) / 3
      right
      field_simp [hAB]
      apply eq_sub_of_add_eq
      norm_cast
      rw [Nat.mul_div_cancel']
      have : (4 ^ n + 2) % 3 = 0 := by
        rw [Nat.add_mod, Nat.pow_mod]
        norm_num
      exact Nat.dvd_of_mod_eq_zero this
  · constructor
    · use 4 * a, 1 - 4 * a
      split_ands
      · positivity
      · simp [hmul_le]
      · ring
      · module
    · use k - 4 ^ n
      left
      have : A - ((4 * a) • A + (1 - 4 * a) • B) = (4 * b - 3) • (A - B) := by
        rw [hab]
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [abs_of_nonneg]
      · simp [hdistZ, pow_add]
        field_simp
        ring
      · exact sub_nonneg_of_le hle

/- We show that if n ≥ 2 ∧ k ≥ 4 ^ n + 3 and |AZ| = (3 * k - 2) / 4 ^ (n + 1), then Z can be obtained by one iteration. -/
lemma subset_of_k_ge_pow_n' {d : ℕ} {A B Z : EuclideanSpace ℝ (Fin d)} (hAB : dist A B = 1)
    (hZ_mem : Z ∈ segment ℝ A B) {k : ℕ} (hk : k ≥ 4 ^ n + 3) (hdistZ : dist A Z = (3 * k - 2) / 4 ^ (n + 1))
    {iter : Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d))}
    (hiter : iter = fun M => {Z | ∃ X ∈ M, ∃ Y ∈ M, Z ∈ segment ℝ X Y ∧ dist Y Z = 3 * dist X Z}) :
    Z ∈ iter {X | X ∈ segment ℝ A B ∧ ∃ k : ℕ, dist A X = 3 * ↑k / 4 ^ n ∨ dist A X = (3 * ↑k - 2) / 4 ^ n} := by
  simp [hiter]
  obtain ⟨a, b, ha, hb, hab, hZ⟩ := hZ_mem
  have hab : a = 1 - b := by
    rw [←hab]; ring
  have : dist A Z = b := by
    have hZ : A - Z = b • (A - B) := by
      rw [←hZ, smul_sub]
      rw [hab]
      module
    rw [dist_eq_norm, hZ, norm_smul]
    simp [abs_of_nonneg hb]
    rw [dist_eq_norm] at hAB
    simp [hAB]
  rw [this] at hdistZ
  have hle : 4 * b ≥ (3 : ℝ) := by
    simp [hdistZ, pow_add]
    trans 4 * (3 * 4 ^ n / (4 ^ n * 4))
    · apply le_of_eq
      field_simp
      ring
    · gcongr
      trans 3 * (4 ^ n + 3) - 2
      · apply sub_nonneg.mp
        ring_nf
        simp
      · gcongr
        norm_cast
  have hmul_le : 4 * a ≤ 1 := by
    simp [hab]
    linarith only [hle]
  -- let X := B
  -- let Y := (4 * a) • A + (1 - 4 * a) • B
  -- We verify that Z = (3 / 4) • X + (1 / 4) • Y.
  use B, ?_, (4 * a) • A + (1 - 4 * a) • B, ?_
  · constructor
    · use 3 / 4, 1 / 4
      norm_num
      rw [←hZ, hab]
      module
    · have : (4 * a) • A + (1 - 4 * a) • B - Z = (3 * a) • (A - B) := by
        rw [←hZ, hab]
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, abs_mul]
      simp [abs_of_nonneg ha, dist_eq_norm]
      have : B - Z = (b - 1) • (A - B) := by
        rw [←hZ, hab]
        module
      rw [this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one, abs_sub_comm, abs_of_nonneg, hab]
      rw [←hab]
      exact ha
  · -- Note that 0 ≤ 4 * a ≤ 1, therefore X, Y ∈ segment ℝ A B.
    constructor
    · exact right_mem_segment ℝ A B
    · use (4 ^ n + 2) / 3
      right
      field_simp [hAB]
      apply eq_sub_of_add_eq
      norm_cast
      rw [Nat.mul_div_cancel']
      have : (4 ^ n + 2) % 3 = 0 := by
        rw [Nat.add_mod, Nat.pow_mod]
        norm_num
      exact Nat.dvd_of_mod_eq_zero this
  · constructor
    · use 4 * a, 1 - 4 * a
      split_ands
      · positivity
      · simp [hmul_le]
      · ring
      · module
    · use k - 4 ^ n
      right
      have : A - ((4 * a) • A + (1 - 4 * a) • B) = (4 * b - 3) • (A - B) := by
        rw [hab]
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [abs_of_nonneg]
      · simp [hdistZ, pow_add]
        have : k ≥ 4 ^ n := by
          trans 4 ^ n + 3
          . exact hk
          · simp
        field_simp
        ring
      · exact sub_nonneg_of_le hle

/- We show that if n ≥ 2 ∧ k ≤ 2 and |AZ| = (3 * k - 2) / 4 ^ (n + 1), then Z can be obtained by one iteration. -/
lemma subset_of_k_le_2 {d : ℕ} {A B Z : EuclideanSpace ℝ (Fin d)} (hAB : dist A B = 1)
    (hZ_mem : Z ∈ segment ℝ A B) {k : ℕ} (hk : k ≤ 2) (hdistZ : dist A Z = (3 * k - 2) / 4 ^ (n + 1))
    {iter : Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d))}
    (hiter : iter = fun M => {Z | ∃ X ∈ M, ∃ Y ∈ M, Z ∈ segment ℝ X Y ∧ dist Y Z = 3 * dist X Z}) (hn : n ≥ 2) :
    Z ∈ iter {X | X ∈ segment ℝ A B ∧ ∃ k : ℕ, dist A X = 3 * ↑k / 4 ^ n ∨ dist A X = (3 * ↑k - 2) / 4 ^ n} := by
  simp [hiter]
  obtain ⟨a, b, ha, hb, hab, hZ⟩ := hZ_mem
  have hab : a = 1 - b := by
    rw [←hab]; ring
  have : dist A Z = b := by
    have hZ : A - Z = b • (A - B) := by
      rw [←hZ, smul_sub]
      rw [hab]
      module
    rw [dist_eq_norm, hZ, norm_smul]
    simp [abs_of_nonneg hb]
    rw [dist_eq_norm] at hAB
    simp [hAB]
  rw [this] at hdistZ
  -- Let X := A
  -- Let Y := (1 - 4b) • A + 4b • B
  -- We verify that Z = (3 / 4) • X + (1 / 4) • Y.
  use A, ?_, (1 - 4 * b) • A + (4 * b) • B, ?_
  · constructor
    · use 3 / 4, 1 / 4
      norm_num
      rw [←hZ, hab]
      module
    · have : (1 - 4 * b) • A + (4 * b) • B - Z = (-3 * b) • (A - B) := by
        rw [←hZ, hab]
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, abs_mul]
      simp [abs_of_nonneg hb, dist_eq_norm]
      have : A - Z = b • (A - B) := by
        rw [←hZ, hab]
        module
      rw [this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [abs_of_nonneg]
      exact hb
  · -- Note that 0 ≤ 1 - 4 * b ≤ 1, therefore X, Y ∈ segment ℝ A B.
    constructor
    · exact left_mem_segment ℝ A B
    · use 1 / 4
      simp
  · constructor
    · use 1 - 4 * b, 4 * b
      split_ands
      · simp
        rw [hdistZ]
        field_simp
        trans 4 * 4 / 4 ^ (n + 1)
        · gcongr
          · simp
            norm_cast
            norm_num
            trans 3 * 2
            · gcongr
            · simp
        · rw [←sq]
          trans 4 ^ 2 / 4 ^ (2 + 1)
          · gcongr
            · simp
          · norm_num
      · simp [hab]
        linarith only [hb]
      · ring
      · module
    · use k
      right
      have : A - ((1 - 4 * b) • A + (4 * b) • B) = (4 * b) • (A - B) := by
        module
      rw [dist_eq_norm, this, norm_smul, norm_eq_abs, ←dist_eq_norm, hAB, mul_one]
      rw [abs_of_nonneg]
      simp [hdistZ, pow_add]
      field_simp
      ring
      simp [hb]

/- We explicitly express the set after nth iterating the producure given as Mₙ = {X | X ∈ AB ∧ (|AX| = 3k/4^n ∨ |AX| = (3k-2)/4^n)}. -/
lemma repeated_nth {d : ℕ} {A B : EuclideanSpace ℝ (Fin d)} (hAB : dist A B = 1)
    {iter : Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d))}
    (hiter : iter = fun M => {Z | ∃ X ∈ M, ∃ Y ∈ M, Z ∈ segment ℝ X Y ∧ dist Y Z = 3 * dist X Z}) {n : ℕ}:
    Nat.repeat iter n {A, B} = {X ∈ segment ℝ A B | ∃ k : ℕ, dist A X = 3 * k / 4 ^ n ∨ dist A X = (3 * k - 2) / 4 ^ n} := by
  -- prove by induction on n
  induction n with
  | zero =>
    -- If n = 0, we need to show that {A, B} = {X ∈ segment ℝ A B | ∃ k : ℕ, dist A X = 3 * k ∨ dist A X = (3 * k - 2)}
    simp [Nat.repeat]
    ext X
    simp
    constructor
    · -- Obviously, A and B are in the segment AB and satisfy the distance conditions witnessed by k = 0 and 1, respectively.
      intro h
      rcases h with h | h
      · simp [h]
        exact left_mem_segment ℝ A B
      · simp [h]
        constructor
        · exact right_mem_segment ℝ A B
        · use 1
          right
          norm_num
          exact hAB
    · -- Conversely, if X is in the segment and satisfies the distance conditions, then ∃ a b ≥ 0 and a + b ≤ 1 such that X=aA+bB.
      intro ⟨⟨a, b, ha, hb, hab, hX⟩, k, h₂⟩
      have hdiff : A - X = (1 - a) • (A - B) := by
        rw [←hX, smul_sub]
        nth_rw 2 [←hab]
        module
      -- Therefore, |AX| = b
      have hdist : dist A X = b := by
        rw [dist_eq_norm, hdiff, norm_smul]
        simp
        rw [←dist_eq_norm, hAB, mul_one]
        rw [←hab]
        simp
        exact hb
      rw [hdist] at h₂
      have hb' : b ≤ 1 := by
        rw [←hab]
        simp
        exact ha
      rcases h₂ with h₂ | h₂
      · -- If b = |AX| = 3k, then 3 k ≤ 1 ∧ k = 0, which implies X = A.
        rw [h₂] at hb'
        norm_cast at hb'
        have hk : k ≤ 1 / 3 := by
          apply Nat.le_div_iff_mul_le (by simp) |>.mpr
          rw [mul_comm]
          exact hb'
        simp at hk
        rw [hk] at h₂
        simp [h₂] at hab hX
        simp [hab] at hX
        simp [hX]
      · -- If b = |AX|=3k-2, then 0≤ 3k-2≤ 1, which implies k = 1 ∧ X = B.
        rw [h₂] at hb' hb
        simp at hb hb'
        norm_cast at hb hb'
        norm_num at hb'
        interval_cases k
        · simp at hb
        · norm_num at h₂
          simp [h₂] at hab hX
          simp [hab] at hX
          simp [hX]
  | succ n ih =>
    -- Induction step: assume the property holds for n, and show it holds for n + 1.
    -- Directly apply the I.H..
    simp [Nat.repeat, ih]
    simp [hiter]
    ext Z
    simp
    constructor <;> intro hZ
    · -- If Z is obtained from M_n by the iteration rule, then there exist X, Y in M_n such that dist Y Z = 3 * dist X Z.
      -- According the I.H., X and Y are in the segment AB and satisfy the distance conditions.
      -- i.e., ∃ kX, kY such that dist A X = 3 * kX / 4 ^ n ∨ dist A X = (3 * kX - 2) / 4 ^ n ∧ dist A Y = 3 * kY / 4 ^ n ∨ dist A Y = (3 * kY - 2) / 4 ^ n.
      obtain ⟨X, ⟨hX_mem, kX, hdistX⟩, Y, ⟨hY_mem, kY, hdistY⟩, hZ_mem, hdistZ⟩ := hZ
      constructor
      · obtain ⟨a, b, ha, hb, hab, hX⟩ := hX_mem
        obtain ⟨a', b', ha', hb', hab', hY⟩ := hY_mem
        obtain ⟨a'', b'', ha'', hb'', hab'', hZ⟩ := hZ_mem
        rw [←hX, ←hY] at hZ
        use a'' * a + b'' * a', a'' * b + b'' * b'
        split_ands
        · positivity
        · positivity
        · rw [←mul_one 1]
          nth_rw 1 [←hab'', add_mul, ←hab, ←hab']
          ring
        · rw [←hZ]
          module
      · -- Apply the lemma dist_of_ratio_of_mem_segment to obtain the distance from A to Z.
        -- We have dist A Z = (3 * dist A X + dist A Y) / 4.
        rw [pow_add, pow_one]
        rcases hdistX with hdistX | hdistX
        · -- If dist A X = 3 * kX / 4 ^ n and dist A Y = 3 * kY / 4 ^ n, then use 3 * kX + kY
          rcases hdistY with hdistY | hdistY
          · obtain h := dist_of_ratio_of_mem_segment hX_mem hY_mem hZ_mem hdistZ
            rw [h, hdistX, hdistY]
            use 3 * kX + kY
            left
            field_simp
            ring
          · -- if dist A Y = (3 * kY - 2) / 4 ^ n, then use 3 * kX + kY
            obtain h := dist_of_ratio_of_mem_segment hX_mem hY_mem hZ_mem hdistZ
            rw [h, hdistX, hdistY]
            use 3 * kX + kY
            right
            field_simp
            ring
        · -- If dist A X = (3 * kX - 2) / 4 ^ n,
          have hpos : 3 * kX ≥ 2 := by
            have : 3 * kX - 2 ≥ (0 : ℝ) := by
              have h : dist A X ≥ 0 := by exact dist_nonneg
              simp [hdistX] at h
              trans (3 * kX - 2) / 4 ^ n * 4 ^ n
              · field_simp
              · apply mul_nonneg h
                positivity
            simp at this
            norm_cast at this
          rcases hdistY with hdistY | hdistY
          · -- and dist A Y = 3 * kY / 4 ^ n, then use 3 * kX -2 + kY
            obtain h := dist_of_ratio_of_mem_segment hX_mem hY_mem hZ_mem hdistZ
            rw [h, hdistX, hdistY]
            use 3 * kX - 2 + kY
            left
            field_simp
            ring
          · -- If dist A Y = (3 * kY - 2) / 4 ^ n, then use 3 * kX - 2 + kY
            obtain h := dist_of_ratio_of_mem_segment hX_mem hY_mem hZ_mem hdistZ
            rw [h, hdistX, hdistY]
            use 3 * kX - 2 + kY
            right
            field_simp
            ring
    · -- Conversely, if Z is in the segment AB and satisfies the distance conditions, then we need to show that it can be obtained from M_n by the iteration rule.
      obtain ⟨hZ_mem, k, hdistZ⟩ := hZ
      by_cases hn : n ≤ 1
      · -- If n ≤ 1, we apply the lemma subset_of_n_le_1.
        obtain h := subset_of_n_le_1 hAB hiter hn
        simp [hiter] at h
        obtain h := h Z hZ_mem k hdistZ
        exact h
      · simp at hn
        -- Otherwise, we divide the proof into two cases based on the distance from A to Z.
        rcases hdistZ with hdistZ | hdistZ
        · by_cases hb_le : k < 4 ^ n
          · -- If |AZ| = 3 * k / 4 ^ n and k < 4 ^ n, we apply the lemma subset_of_k_lt_pow_n.
            obtain h := subset_of_k_lt_pow_n hAB hZ_mem hb_le hdistZ hiter hn
            simp [hiter] at h
            exact h
          · -- Otherwise, we have k ≥ 4 ^ n.
            -- In this case, we apply the lemma subset_of_k_ge_pow_n.
            simp at hb_le
            obtain h := subset_of_k_ge_pow_n hAB hZ_mem hb_le hdistZ hiter
            simp [hiter] at h
            exact h
        · -- If |AZ| = (3 * k - 2) / 4 ^ n, we need to consider three cases based on the value of k.
          by_cases hk : k ≤ 2
          · -- If k ≤ 2, we apply the lemma subset_of_k_le_2.
            obtain h := subset_of_k_le_2 hAB hZ_mem hk hdistZ hiter hn
            simp [hiter] at h
            exact h
          · -- Otherwise, if 2 < k ≤ 4 ^ n + 3,
            -- we apply the lemma subset_of_k_ge_pow_n'. 
            simp at hk
            by_cases hb_le : k ≤ 4 ^ n + 3
            · obtain h := subset_of_k_lt_pow_n' hAB hZ_mem hdistZ hb_le hk hiter hn
              simp [hiter] at h
              exact h
            · -- Finally, if k > 4 ^ n + 3,
              -- we apply the lemma subset_of_k_ge_pow_n'.
              simp at hb_le
              obtain h := subset_of_k_ge_pow_n' hAB hZ_mem (le_of_lt hb_le) hdistZ hiter
              simp [hiter] at h
              exact h

/- 12. (CZS 6) Given a segment $A B$ of the length 1, define the set $M$ of points in the following way:
it contains the two points $A, B$, and also all points obtained from $A, B$ by iterating the following rule:
$(*)$ for every pair of points $X, Y$ in $M$, the set $M$ also contains the point $Z$ of the segment $X Y$ for which $Y Z=3 X Z$.
 (a) Prove that the set $M$ consists of points $X$ from the segment $A B$ for which the distance from the point $A$ is either
 $$ A X=\frac{3 k}{4^{n}} \quad \text { or } \quad A X=\frac{3 k-2}{4^{n}} $$  where $n, k$ are nonnegative integers.
 (b) Prove that the point $X_{0}$ for which $A X_{0}=1 / 2=X_{0} B$ does not belong to the set $M$. -/
theorem number_theory_24612 {d : ℕ} {A B : EuclideanSpace ℝ (Fin d)} (hAB : dist A B = 1)
    {iter : Set (EuclideanSpace ℝ (Fin d)) → Set (EuclideanSpace ℝ (Fin d))}
    (hiter : iter = fun M => {Z | ∃ X ∈ M, ∃ Y ∈ M, Z ∈ segment ℝ X Y ∧ dist Y Z = 3 * dist X Z}) {M : Set (EuclideanSpace ℝ (Fin d))} (hM : M = ⋃ n : ℕ, Nat.repeat iter n {A, B}):
    M = {X ∈  segment ℝ A B | ∃ n k : ℕ, dist A X = 3 * k / 4 ^ n ∨ dist A X = (3 * k - 2) / 4 ^ n} ∧
    ∀ X₀, dist A X₀ = 1 / 2 → dist X₀ B = 1 / 2 → X₀ ∉ M := by
  -- Since we have proved that M_n = {X ∈ segment ℝ A B | ∃ k : ℕ, dist A X = 3 * k / 4 ^ n ∨ dist A X = (3 * k - 2) / 4 ^ n} for all n,
  -- The first part of the theorem follows from the fact that M is the union of all M_n.
  simp [repeated_nth hAB hiter] at hM
  have hM : M = {X ∈  segment ℝ A B | ∃ n k : ℕ, dist A X = 3 * k / 4 ^ n ∨ dist A X = (3 * k - 2) / 4 ^ n} := by
    rw [hM]
    ext X
    simp

  constructor
  · exact hM
  · -- Assume that X₀ is in M, i.e., X₀ ∈ M_n for some n and dist A X₀ = 1 / 2.
    intro X₀ h₁ h₂
    by_contra h
    simp [hM] at h
    -- According to the first part of the theorem, there exist n, k such that dist A X₀ = 3 * k / 4 ^ n or dist A X₀ = (3 * k - 2) / 4 ^ n.
    obtain ⟨n, k, h⟩ := h.2
    rcases h with h | h
    · -- If 3 * k / 4 ^ n = 1 / 2, then we have 3 * k  *2 = 4 ^ n.
      -- Therefore , 3 ∣ 4, which is a contradiction.
      rw [h] at h₁
      field_simp at h₁
      norm_cast at h₁
      have : 3 ∣ 4 ^ n := by
        use k * 2
        rw [←h₁]
        ring
      have : 3 ∣ 4 := by
        apply Nat.Prime.dvd_of_dvd_pow ?_ this
        norm_num
      norm_num at this
    · -- If (3 * k - 2) / 4 ^ n = 1 / 2, then we have 3 * k  * 2 = 4 ^ n + 4.
      rw [h] at h₁
      field_simp at h₁
      rw [sub_mul] at h₁
      apply eq_add_of_sub_eq at h₁
      norm_cast at h₁
      have : 3 ∣ 4 ^ n + 4 := by
        use k * 2
        rw [←h₁]
        ring
      -- Therefore, (4 ^ n + 4) % 3 = 0.
      have : (4 ^ n + 4) % 3 = 0 := by exact Nat.dvd_iff_mod_eq_zero.mp this
      -- However, (4 ^ n + 4) % 3 = 1 + 1 = 2, which is a contradiction.
      rw [Nat.add_mod, Nat.pow_mod] at this
      norm_num at this
