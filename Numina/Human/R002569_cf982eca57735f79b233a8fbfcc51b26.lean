import Mathlib

open Pointwise

/-- The sets $A = \{z : z^{18} = 1\}$ and $B = \{w : w^{48} = 1\}$ are both sets of complex roots
of unity. The set $C = \{zw : z \in A ~ \mbox{and} ~ w \in B\}$ is also a set of complex roots of
unity. How many distinct elements are in $C_{}^{}$? -/
theorem number_theory_95575 {A B : Set ℂ} (hA : A = {z | z^18 = 1}) (hB : B = {w | w^48 = 1})
    {C : Set ℂ} (hC : C = A * B) : C.ncard = 144 := by

  -- $A$ is the set of 18th roots of unity.
  replace hA : A = (Units.coeHom ℂ) '' rootsOfUnity 18 ℂ := by
    ext z
    constructor <;> simp [hA]
    · intro hz
      refine ⟨?_, ?_⟩
      · exact Units.mk z (z^17) (by convert hz; ring) (by convert hz)
      · simp
        have : Function.Injective (Units.coeHom ℂ) := by
          intro x y h
          simp at h
          norm_cast at h
        apply this
        simp
        exact hz
    · intro x hx1 hx2
      rw [←hx2]
      norm_cast
      rw [hx1]
      rfl

  -- $B$ is the set of 48th roots of unity.
  replace hB : B = (Units.coeHom ℂ) '' rootsOfUnity 48 ℂ := by
    ext w
    constructor <;> simp [hB]
    · intro hw
      refine ⟨?_, ?_⟩
      · exact Units.mk w (w^47) (by convert hw; ring) (by convert hw)
      · simp
        have : Function.Injective (Units.coeHom ℂ) := by
          intro x y h
          simp at h
          norm_cast at h
        apply this
        simp
        exact hw
    · intro x hx1 hx2
      rw [←hx2]
      norm_cast
      rw [hx1]
      rfl

  -- We claim that the number of elements of $C$ is 144.
  -- It is enough to show that $C$ is the set of 144th roots of unity where 144 is the least common
  -- multiple of 18 and 48.
  suffices C = (Units.coeHom ℂ) '' rootsOfUnity 144 ℂ from ?_
  · rw [this, Set.ncard_image_of_injective]
    · convert Complex.card_rootsOfUnity 144
      rw [←Cardinal.mk_toNat_eq_card]
      unfold Set.ncard Set.encard ENat.card
      rw [Cardinal.toNat_toENat]
      rfl
    · intro x y h
      simp at h
      norm_cast at h

  -- To that end, it is enough to show that the set of pairwise products of 18th roots of unity
  -- and 48th roots of unity is precisely the set of 144th roots of unity.
  suffices C = (Units.coeHom ℂ) '' ((rootsOfUnity 18 ℂ) * (rootsOfUnity 48 ℂ)) from ?_
  · rw [this]
    apply congrArg
    ext z
    constructor <;> simp [Set.mem_mul]
    -- Let $z = x y$ where $x$ is an 18th root of unity and $y$ is a 48th root of unity.
    · intro x hx y hy hz

      -- $z$ is also a 144th root of unity. This is because $18 | 144$ and $48 | 144$.
      calc _ = x^144 * y^144 := by rw [←hz, mul_pow]
           _ = (x^18)^8 * (y^48)^3 := by rw [←pow_mul, ←pow_mul]
           _ = 1 := by rw [hx, hy]; simp

    -- For the converse, let $z$ be a 144th root of unity.
    · intro hz
      -- Let $x = z^40$. The order of $x$ is $144 / \operatorname{gcd}(40, 144) = 144 / 8 = 18$.
      refine ⟨z^40, ?_, z^105, ?_, ?_⟩
      · calc _ = z^(40 * 18) := by rw [pow_mul]
             _ = z^(144 * 5) := by rfl
             _ = _ := by rw [pow_mul, hz, one_pow]
      -- Let $y = z^{105}$. The order of $y$ is $144 / \operatorname{gcd}(105, 144) = 144 / 3 = 48$.
      · calc _ = z^(105 * 48) := by rw [pow_mul]
             _ = z^(144 * 35) := by rfl
             _ = _ := by rw [pow_mul, hz, one_pow]
      -- Then, $x y = z^145 = z$.
      · calc _ = z^(144 + 1) := by rw [←pow_add]
             _ = z := by rw [pow_add, pow_one, hz, one_mul]

  rw [hC, hA, hB, Set.image_mul]