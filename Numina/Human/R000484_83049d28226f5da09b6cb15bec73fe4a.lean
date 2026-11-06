import Mathlib

/-The graphs of a function $f(x)=3x+b$ and its inverse function $f^{-1}(x)$ intersect at the point $(-3,a)$. Given that $b$ and $a$ are both integers, what is the value of $a$?-/
theorem algebra_11227 {f g : ℝ → ℝ} {b : ℝ} (hf : f = fun x => 3 * x + b)
    (hg : g = Function.invFun f) (a : ℝ) (ha : f (-3) = a) (ha' : g (-3) = a) :
    a = -3 := by
  -- Since the graph of $f$ contains the point $(-3,a)$, we know that \[a=f(-3)=3(-3)+b=b-9.\]
  rw [hf] at ha
  field_simp at ha
  have hg: g = fun x => (x - b) / 3 := by
    have f_bijective : Function.Bijective f := by
      apply (Function.bijective_iff_existsUnique f).mpr
      rw [hf]
      intro x
      simp
      use (x - b) / 3
      simp
      constructor
      · linarith
      · intro y hy
        linarith
    rw [hg]
    unfold Function.invFun
    ext x
    split
    · rename_i h
      by_contra!
      have eq₁: f h.choose = x := by
        exact h.choose_spec
      have eq₂: f ((x - b) / 3) = x := by
        rw [hf]
        ring_nf
      have eq₃: h.choose = (x - b) / 3 := by
        apply f_bijective.1
        rw [eq₁, eq₂]
      exact absurd eq₃ this
    · rename_i h
      rw [hf] at h
      simp at h
      specialize h ((x - b) / 3)
      absurd h
      ring_nf

  -- Since the graph of $f^{-1}$ also contains this point we know that $f^{-1}(-3)=a$ or $-3=f(a)$. Therefore \[-3=f(a)=3a+b.\]
  rw [hg] at ha'
  field_simp at ha'
  -- Substitution for $a$ gives \[-3=3(b-9)+b=4b-27.\]
  rw [ha.symm] at ha'
  -- Therefore $b=\frac14(27-3)=6$.
  have hb : b = 6 := by linarith
  -- This forces \[a=b-9=6-9=\boxed{-3}.\]
  have ha : a = -3 := by linarith
  use ha
