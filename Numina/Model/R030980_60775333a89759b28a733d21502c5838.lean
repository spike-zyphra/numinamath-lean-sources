import Mathlib



theorem number_theory_95900 :
    Set.ncard {r : ℚ | 0 < r ∧ r < 1 ∧ r.num + r.den = 1000} = 200 := by
  let f1 : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have f1_inj : Function.Injective f1 := by
    intro r1 r2
    simp [f1]
    exact Rat.ext
  have f1_image : f1 '' {r : ℚ | 0 < r ∧ r < 1 ∧ r.num + r.den = 1000} = {(x, y) : ℤ × ℕ | 0 < x ∧ x < y ∧ x + y = 1000 ∧ Nat.Coprime (Int.natAbs x) y} := by
    ext ⟨n, d⟩
    simp
    constructor
    .
      rintro ⟨r, ⟨h1, h2, h3⟩, h4⟩
      simp [f1] at h4
      obtain ⟨hr1, hr2⟩ := h4
      rw [← hr1, ← hr2]
      and_intros
      any_goals simpa
      .
        qify
        rw [← div_lt_one (by simp [Rat.den_pos])]
        simpa [Rat.num_div_den r]
      .
        exact Rat.reduced r
    .
      rintro ⟨h1, h2, h3, h4⟩
      use Rat.mk' n d (by linarith) h4
      simp [f1, h3]
      and_intros
      .
        rw [← Rat.num_pos]
        simpa
      .
        rw [Rat.mk_eq_mkRat, Rat.mkRat_eq_div, div_lt_one (by norm_cast; linarith)]
        norm_cast
  rw [← Set.ncard_image_of_injective _ f1_inj, f1_image]
  let f2 : ℕ → ℤ × ℕ := fun x => (x, 1000 - x)
  have f2_inj : Function.Injective f2 := by
    rintro x1 x2
    simp [f2]
    intro h _
    exact h
  have f2_image : f2 '' ↑{x ∈ Finset.Ioo 0 500 | Nat.Coprime x 1000} = {(x, y) : ℤ × ℕ | 0 < x ∧ x < y ∧ x + y = 1000 ∧ Nat.Coprime (Int.natAbs x) y} := by
    ext ⟨x, y⟩
    simp [f2]
    constructor
    .
      rintro ⟨x', ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩⟩
      rw [← h4, ← h5, Int.ofNat_sub (show x' ≤ 1000 by linarith)]
      simp
      zify at h1 h2
      and_intros
      .
        linarith
      .
        rw [lt_tsub_iff_right]
        linarith
      .
        rw [Nat.Coprime, Nat.gcd_sub_self_right (show x' ≤ 1000 by linarith), h3]
    .
      rintro ⟨h1, h2, h3, h4⟩
      have : 0 ≤ x := by linarith
      use Int.natAbs x
      and_intros
      all_goals zify
      .
        rw [abs_of_pos h1]
        exact h1
      .
        rw [abs_of_pos h1]
        linarith
      .
        rw [show 1000 = Int.natAbs x + y by zify; rw [abs_of_pos h1, h3]]
        simpa
      .
        exact abs_of_pos h1
      .
        rw [Int.ofNat_sub (show (Int.natAbs x) ≤ 1000 by zify; rw [abs_of_pos h1]; linarith)]
        simp
        rw [abs_of_pos h1]
        linarith
  rw [← f2_image, Set.ncard_image_of_injective _ f2_inj, Set.ncard_coe_Finset]
  native_decide