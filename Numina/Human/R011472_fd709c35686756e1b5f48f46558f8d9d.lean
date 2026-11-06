import Mathlib

/- $6 \cdot 44$ Let $f(x)$ be a continuous function defined on $0 \leqslant x \leqslant 1$, with $f(0)=0, f(1)=1$. Also, for any $x, 0 < x < 1$, there exists $h$ such that when $0 \leqslant x-h< x+h \leqslant 1$,

$$

f(x)=\frac{f(x-h)+f(x+h)}{2} .

$$


Prove: For $0 \leqslant x \leqslant 1, f(x)=x$. -/

theorem algebra_254058 (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (h₀ : f 0 = 0) (h₁ : f 1 = 1)
    (h₂ : ∀ x ∈ Set.Ioo 0 1, ∃ h, 0 ≤ x - h ∧ x - h < x + h ∧ x + h ≤ 1 ∧
      f x = (f (x - h) + f (x + h)) / 2) :
    ∀ x ∈ Set.Icc 0 1, f x = x := by
  -- first we'll convert the problem to f (x) - x, then it's easier to do some generalization
  let g (x : ℝ) := f x - x
  -- define g(x) = f(x) - x, then g(0) = g(1) = 1, g is continuous on (0, 1) and same condition of f applies to g
  replace h₀ : g 0 = 0 := by
    simp [g, h₀]
  replace h₁ : g 1 = 0 := by
    simp [g, h₁]
  replace hf : ContinuousOn g (Set.Icc 0 1) := by
    simp [g]
    fun_prop
  replace h₂ (x : ℝ) (hx : x ∈ Set.Ioo 0 1) : ∃ h, 0 ≤ x - h ∧ x - h < x + h ∧ x + h ≤ 1 ∧ g x = (g (x - h) + g (x + h)) / 2 := by
    obtain ⟨h, hxh1, hxh2, hxh3, hf⟩ := h₂ x hx
    use h
    simp [hxh1, hxh2, hxh3, g]
    linarith
  -- f(x) = x iff g (x) - 0
  have (x : ℝ) : f x = x ↔ g x = 0 := by
    simp [g]
    rw [sub_eq_zero]
  simp_rw [this]
  clear this
  -- now we proof generalizing g to F
  generalize g = F at h₀ h₁ h₂ hf
  -- assume there is a x that has nonzero value, we'll prove contradiction
  by_contra h
  push_neg at h
  obtain ⟨x, hx, hF⟩ := h
  -- wlog 0 < F x, if not then F x < 0 and we can use the same proof for G = -F
  wlog hx' : 0 < F x generalizing F
  . let G := -F
    replace h₂ (x : ℝ) (hx : x ∈ Set.Ioo 0 1) : ∃ h, 0 ≤ x - h ∧ x - h < x + h ∧ x + h ≤ 1 ∧ G x = (G (x - h) + G (x + h)) / 2 := by
      convert h₂ x hx using 5
      simp [G]
      constructor <;> rintro h <;> linarith
    push_neg at hx'
    specialize this G (by simp [G, h₀]) (by simp [G, h₁]) h₂ (by simpa [G]) (by simpa [G]) (by simp [G]; exact lt_of_le_of_ne hx' hF)
    assumption
  -- now there is a maximizer on [0, 1] as f is continuous there
  obtain ⟨m, hm, hm', hm''⟩  := IsCompact.exists_sSup_image_eq_and_ge (s := Set.Icc (0 : ℝ) 1) (f := F)
      (CompactIccSpace.isCompact_Icc) (by simp) hf
  -- we'll prove F(m) ≤ 0, this proves contradiction
  suffices F m ≤ 0 by
    specialize hm'' x hx
    linarith
  clear hF hx' hx x
  -- we'll prove 0 < F(m) proves contradiction
  apply le_of_not_lt
  rintro h
  -- consider set {x : ℝ | x ∈ Set.Icc 0 1 ∧ F x = F m}, this is nonempty, bounded below, name it's infimum x
  have h_nonempty : {x : ℝ | x ∈ Set.Icc 0 1 ∧ F x = F m}.Nonempty := by
    use m
    simp [hm.1, hm.2]
  have h_bdd : BddBelow {x : ℝ | x ∈ Set.Icc 0 1 ∧ F x = F m} := by
    use 0
    rintro x
    simp
    tauto
  let x := sInf {x : ℝ | x ∈ Set.Icc 0 1 ∧ F x = F m}
  -- x belongs to the set as it's restricted preimage of {F (m)} and F is continuos there
  have hx : x ∈ {x : ℝ | x ∈ Set.Icc 0 1 ∧ F x = F m} := by
    refine IsClosed.csInf_mem ?_ h_nonempty h_bdd
    convert_to IsClosed (Set.Icc 0 1 ∩ F ⁻¹' {F m})
    refine ContinuousOn.preimage_isClosed_of_isClosed hf ?_ ?_
    . exact isClosed_Icc
    . exact isClosed_singleton
  simp at hx
  -- x actually belongs to (0, 1) as it can't be 0 or 1 as it's value is not 0 there
  have hx'' : x ∈ Set.Ioo 0 1 := by
    simp
    and_intros
    . apply lt_of_le_of_ne hx.left.left
      by_contra h
      have hx := hx.right
      rw [← h, h₀] at hx
      linarith
    . apply lt_of_le_of_ne hx.left.right
      by_contra h
      have hx := hx.right
      rw [h, h₁] at hx
      linarith
  -- so by last fact F x = (F (x - e) + F (x + e)) / 2
  specialize h₂ x hx''
  obtain ⟨e, hxe1, hxe2, hxe3, he⟩ := h₂
  -- but F (x - e) < F m, for it can't be equal to F m as  it's below the infimum
  have : F (x - e) < F m := by
    have : 0 < e := by linarith
    apply lt_of_le_of_ne (hm'' (x-e) (by simp; and_intros <;> linarith))
    by_contra h
    suffices x ≤ x - e by linarith
    change sInf {x : ℝ | x ∈ Set.Icc 0 1 ∧ F x = F m} ≤ x - e
    have : x - e ∈ {x : ℝ | x ∈ Set.Icc 0 1 ∧ F x = F m} := by
      simp; and_intros <;> linarith
    exact ConditionallyCompleteLattice.csInf_le {x | x ∈ Set.Icc 0 1 ∧ F x = F m} (x - e) h_bdd this
  -- and F(x + e) ≤ F m due to maximum value F m
  have : F (x + e) ≤ F m := by
    specialize hm'' (x + e) (by simp; and_intros <;> linarith)
    assumption
  -- from the two inequalities we get contradiction
  linarith