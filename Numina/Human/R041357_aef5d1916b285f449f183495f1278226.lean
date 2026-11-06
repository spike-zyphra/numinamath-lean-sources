import Mathlib

/- Find all functions $f$ from the reals into the reals such that \[ f(ab) = f(a+b) \] for all irrational $a, b$. -/
theorem other_65668 (f : ℝ → ℝ) :
    (∀ a b : ℝ, Irrational a → Irrational b → f (a * b) = f (a + b)) ↔
    ∃ c, ∀ x, f x = c := by
    constructor
    -- Prove the necessity, that is, to find a function f that satisfies the conditions based on its properties
    intro hf --Obtain the properties of f
    have sqrt_irr : ∀x:ℝ,Irrational x → x>0 → Irrational √x := by -- Lemma: The square root of a positive irrational number must be an irrational number (there seems to be no ready-made theorem for this in mathlib)
      intro x hx1 hx2
      by_contra h
      unfold Irrational at h
      simp at h
      match h with
      |⟨xx,hxx⟩ => -- xx is a rational number, hxx : ↑xx = √x
      have hxx : x = xx^2 := by
        rw [hxx]
        exact (Real.sq_sqrt (show 0≤x by linarith)).symm
      rw [show (↑xx)^2 = (↑(xx^2):ℝ) by simp] at hxx
      unfold Irrational at hx1
      rw [hxx] at hx1
      simp at hx1
      have := hx1 (xx^2)
      simp at this
    have h1: ∀x:ℝ,Irrational x → x < 0 → f x = f 0 := by
      intro x hx1 hx2
      have hx3 : Irrational √(-x) := sqrt_irr (-x) (irrational_neg_iff.2 hx1) (show -x>0 by linarith)
      have hx4 : Irrational (-√(-x)) := irrational_neg_iff.2 hx3
      have hf1 := hf √(-x) (-√(-x)) hx3 hx4
      simp at hf1
      rw [show √(-x) * √(-x) = -x from Real.mul_self_sqrt (show 0≤-x by linarith)] at hf1
      simp at hf1
      exact hf1
    have h2: ∀x:ℝ,Irrational x → x > 0 → f x = f 0 := by
      intro x hx1 hx2
      have hx3 :Irrational √x := sqrt_irr x hx1 hx2
      have hx4 : Irrational (-√x) := irrational_neg_iff.2 hx3
      have hf1 := hf (-√x) (-√x) hx4 hx4
      have hh1 : (-√x) * (-√x) = x := by
        simp
        exact Real.mul_self_sqrt (show 0≤x by linarith)
      have hh2 : f ((-√x)+(-√x)) = f 0 := by
        rw [show (-√x)+(-√x) = -2*√x by linarith]
        have hh3 : Irrational ((-2:ℚ)*√x) :=
          irrational_rat_mul_iff.2 (And.intro (show (-2:ℚ)≠0 by norm_num) hx3)
        rw [show ↑(-2:ℚ)=(-2:ℝ) by simp] at hh3
        have hh4 : -2*√x < 0 := by
          have := Real.sqrt_pos.mpr hx2
          linarith
        exact h1 (-2*√x) hh3 hh4
      rw [hh1,hh2] at hf1
      exact hf1
    have h3: ∀ x : ℝ, Irrational x → f x = f 0 := by -- Obtain h3 from h1 and h2
      intro x hx
      if hx1 : x > 0 then
        exact h2 x hx hx1
      else if hx2 : x = 0 then
        rw [hx2] at hx
        norm_num at hx
      else
        have hx3 : x<0 := by
          simp at hx1
          exact lt_of_le_of_ne hx1 hx2
        exact h1 x hx hx3
    have h4: ∀l:ℚ, l≠0 → ∃a b:ℝ, Irrational a ∧ Irrational b ∧ a+b=l ∧ Irrational (a*b) := by
      intro l hl
      use (Real.sqrt 2), (l - Real.sqrt 2)
      constructor
      -- ⊢ Irrational √2
      exact irrational_sqrt_two
      constructor
      -- ⊢ Irrational (↑l - √2)
      exact irrational_rat_sub_iff.2 irrational_sqrt_two
      constructor
      -- ⊢ √2 + (↑l - √2) = ↑l
      linarith
      -- ⊢ Irrational (√2 * (↑l - √2))
      rw [show √2 * (↑l - √2) = √2*↑l-2 by ring_nf; simp; linarith]
      exact irrational_sub_rat_iff.2 (irrational_mul_rat_iff.2 ⟨hl,irrational_sqrt_two⟩)
    have h5: ∀l:ℚ, f l = f 0 := by
      intro l
      if hl : l ≠ 0 then
        match h4 l hl with
        |⟨a,b,ha,hb,hl,hab⟩ =>
        rw [←hl,←h3 (a*b) hab]
        exact (hf a b ha hb).symm
      else
        simp at hl
        rw [hl]
        simp
    have h6: ∀x:ℝ, f x = f 0 := by
      intro x
      if hx : Irrational x then
        exact h3 x hx
      else
        unfold Irrational at hx
        simp at hx
        match hx with
        |⟨xx,hxx⟩ => -- xx is a rational number, hxx:↑xx=x
        rw [←hxx]
        exact h5 xx
    exact Exists.intro (f 0) h6
    -- Prove sufficiency, that is, verify that the constant function satisfies the property
    intro hf
    match hf with
    |⟨c,hf⟩ =>
    intro a b ha hb
    rw [hf (a*b),hf (a+b)]
