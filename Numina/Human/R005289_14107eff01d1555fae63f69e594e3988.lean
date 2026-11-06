import Mathlib

/- Soit $n \geqslant 2$. Montrer qu'il existe des entiers $a, b$ tels que, pour tout entier $m$, le nombre $m^{3}+a m+b$ ne soit pas un multiple de $n$. -/
theorem number_theory_607430 (n : ℤ) (hn : n ≥ 2) :
    ∃ a b, ∀ m, ¬(n ∣ m^3 + a * m + b) := by 
  -- Convert the integer n to a natural number since we'll work in ZMod n
  let n_nat : ℕ := n.toNat
  have h_eq : (n_nat : ℤ) = n := by
    rw [Int.toNat_of_nonneg]
    linarith
  have hn_nat : n_nat ≥ 2 := by
    have h_ge : (n_nat : ℤ) ≥ 2 := by rwa [h_eq]
    exact_mod_cast h_ge
    
  -- Define the function f(m) = m^3 - m in the ring of integers modulo n
  let f : ZMod n_nat → ZMod n_nat := fun m => m^3 - m
  have h_nezero: NeZero n_nat := NeZero.of_gt hn_nat
  
  -- Prove that f is not injective by showing f(0) = f(1)
  have h_not_inj : ¬Function.Injective f := by
    unfold Function.Injective
    push_neg
    use 0, 1
    constructor
    · ring
    · by_contra w
      have r6: 0%n_nat = 1%n_nat := by 
        apply (ZMod.natCast_eq_natCast_iff' 0 1 n_nat).mp
        norm_num
        exact w
      simp at r6
      omega
      
  -- For finite sets, a function that is not injective cannot be surjective
  have h_not_surj : ¬Function.Surjective f := by
    by_contra w
    have h_ZMod_finite: Finite (ZMod n_nat) := by
      exact Fintype.finite (show Fintype (ZMod n_nat) by apply ZMod.fintype)
    apply Finite.injective_iff_surjective.mpr at w
    exact h_not_inj w
    
  -- Since f is not surjective, there exists an element a' that is not in the image of f
  obtain ⟨a', h_a'⟩ := Classical.not_forall.mp h_not_surj
  have h_a'_not_image : ∀ m : ZMod n_nat, f m ≠ a' := by
    intro m
    by_contra h_eq
    have h_in_range : a' ∈ Set.range f := by
      apply Set.mem_range.mpr
      use m
    exact h_a' h_in_range
    
  -- Use the value of a' as our desired a in the theorem statement
  let a := a'.val
  exists (-1)
  use a
  intro m
  by_contra h_divides
  let r := m^3 - m + a
  
  -- Derive a contradiction by showing that a' must be in the image of f
  have r1: r = m^3 - m + a := by rfl
  have h_eq_zmod : (m : ZMod n_nat)^3 - (m : ZMod n_nat) + a' = 0 := by
    have h1 : a' = (a : ZMod n_nat) := by 
      rw[show a = a'.val by rfl,← ZMod.cast_eq_val]
      exact Eq.symm (ZMod.cast_id n_nat a')
    rw [h1]
    have h2 : ((0:ℤ) : ZMod n_nat)=r := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub 0 r n_nat).mpr
      simp[r1,h_eq]
      simp at h_divides 
      exact h_divides 
    simp[r1] at h2
    rw[h2]
    
  -- Complete the contradiction by showing that f(-m) = a', contrary to our earlier finding
  have h_eq_neg : f (m : ZMod n_nat) = -a' := by
    exact Eq.symm (neg_eq_of_add_eq_zero_left h_eq_zmod)
  have h_contradiction : ∃ m' : ZMod n_nat, f m' = a' := by
    use (-m : ZMod n_nat)
    calc f (-m) = -f (m) := by ring
           _ = a' := by simp[h_eq_neg]
  exact h_a' h_contradiction