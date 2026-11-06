import Mathlib

/-A student at Harvard named Kevin
Was counting his stones by 11 He messed up n times And instead counted 9s And wound up at 2007.
How many values of n could make this limerick true?-/
theorem number_theory_608193: {n: ℕ | ∃ k: ℕ, 9 * n + 11 * k = 2007}.encard = 21:= by

-- we directly show that n is just 11m+3
  have h_eq: {n: ℕ | ∃ k: ℕ, 9 * n + 11 * k = 2007} =
   (Finset.range 21).map ⟨fun k => 11 * k + 3, by intros a b h; linarith⟩ := by
    ext n
    constructor
    -- the forward direction
    . intro h
      simp at h
      obtain ⟨k, h⟩:= h
      simp
      have hn: 3 ≤ n := by
        by_contra! no
        interval_cases n
        all_goals omega
      rw [show 9 * n = 9 * (n - 3) + 27 by zify; omega] at h
      replace h: 9 * (n - 3) + 11 * k = 1980 := by
        zify
        zify at h
        omega
      have dvd1: 11 ∣ 9 * (n - 3) + 11 * k := by
        rw [h]
        omega
      have dvd2: 11 ∣ 11 * k := by omega
      have dvd3: 11 ∣ 9 * (n - 3) := by
        rw [show 9 * (n - 3) = 9 * (n - 3) + 11 * k - 11 * k by zify; omega]
        apply Nat.dvd_sub
        zify
        omega
        omega
        omega
      replace dvd3: 11 ∣ n - 3 := by omega
      apply exists_eq_mul_right_of_dvd at dvd3
      obtain ⟨m, h⟩ := dvd3
      replace h: n = 3 + 11 * m := by
        zify
        omega
      use m
      constructor
      . by_contra! hm
        omega
      . omega
    -- the backward direction
    . intro h
      simp at h
      simp
      obtain ⟨m, h⟩ := h
      rcases h with ⟨hm, h⟩
      use (180 - 9 * m)
      rw [← h]
      zify
      omega

  -- now use h_eq to simplify
  rw [h_eq]
  simp [Set.encard]
  rw [Finset.card_image_of_injective]
  simp
  intro x y h
  simp at h
  omega
