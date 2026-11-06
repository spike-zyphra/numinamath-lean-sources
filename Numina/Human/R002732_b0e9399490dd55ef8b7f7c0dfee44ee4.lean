import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology Pointwise

/- $2 \cdot 8$ set $A=\left\{z \mid z^{18}=1\right\}, B=\left\{w \mid w^{48}=1\right\}$ are both sets of complex roots of unity, $C=\{z w \mid z \in A, w \in B\}$ is also a set of complex roots of unity, how many elements does set $C$ contain? -/
theorem number_theory_105342 {A B : Set ℂ}
    (hA : A = {z | z^18 = 1}) (hB : B = {w | w^48 = 1})
    (C : Set ℂ) (hC : C = {x | ∃ z ∈ A, ∃ w ∈ B, x = z * w}) :
    C.ncard = 144 := by

  -- To begin, we prove that C is precisely the set of 144-th roots of unity.
  have hC' : C = {z | z^144 = 1} := by
    ext z
    simp only [hC, hA, hB, Set.mem_setOf_eq]
    constructor <;> intro hz
    · -- First note that C = A * B is a subset of 144-th roots of unity, since
      -- for elements a and b such that a^18 = b^48 = 1, we have
      -- (a*b)^144 = a^144 * b^144 = (a^18)^8 * (b^48)^3 = 1
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      apply_fun (· ^ 8) at ha
      apply_fun (· ^ 3) at hb
      simp [← pow_mul] at ha hb
      rw [mul_pow, ha, hb, mul_one]
    · -- For the other direction, first note that the 144-th roots of unity is a cyclic subgroup of
      -- ℂˣ, meaning all elements are in the form of ζ^i for some i, with ζ^144 = 1
      have hζ := Complex.isPrimitiveRoot_exp 144 (by decide)
      set ζ := cexp (2 * Real.pi * I / (144 : ℕ)) with hζ_eq
      have := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ hz
      obtain ⟨i, _, hiz⟩ := this

      -- Next, by Bezout's lemma, there exists b, c such that i = 8b + 3c
      obtain ⟨b, c, hbc⟩ : ∃ b c : ℤ, i = 8 * b + 3 * c := by
        obtain ⟨b, c, h⟩ := (@Int.gcd_dvd_iff 8 3 1).mp (by decide)
        rw [Nat.cast_one] at h
        use b * i, c * i
        rw [← mul_assoc, ← mul_assoc, ← add_mul, ← h, one_mul]

      replace hiz : ζ ^ (i : ℤ) = z := by
        rw [← hiz]
        norm_cast

      -- Hence, ζ^i = ζ^(8b + 3c) = ζ^(8b) * ζ^(3c), with ζ^(8b) ∈ A and ζ^(3c) ∈ B.
      rw [hbc, zpow_add₀ (by simp [hζ_eq])] at hiz
      use ζ ^ (8 * b), ?_, ζ ^ (3 * c), ?_, hiz.symm
      all_goals
        rw [← zpow_natCast, ← zpow_mul, mul_right_comm]
        simp only [Nat.cast_ofNat, Int.reduceMul]
        exact (hζ.zpow_eq_one_iff_dvd _).mpr (Int.dvd_mul_right ..)

  -- We rephrase this in another way, that C is the 144 roots of unity viewed as a subgroup of ℂˣ
  have hC_eq : C = Units.val '' rootsOfUnity 144 ℂ := by
    ext w
    rw [hC']
    constructor <;> intro hw
    · simp at hw ⊢
      obtain ⟨w', hw'⟩ : IsUnit w := isUnit_iff_ne_zero.mpr (fun hw ↦ by subst hw; simp at hw)
      use w', ?_, hw'
      rw [← hw'] at hw
      ext
      exact hw
    · simp at hw ⊢
      obtain ⟨x, hx, rfl⟩ := hw
      rw [Units.ext_iff] at hx
      exact hx

  rw [hC_eq, Set.ncard_image_of_injective _ Units.ext, Set.ncard, Set.encard, SetLike.coe_sort_coe,
    ENat.card_eq_coe_fintype_card]
  simp only [ENat.toNat_coe]
  -- And of course the 144-th roots of unity have 144 elements in ℂ
  exact Complex.card_rootsOfUnity 144