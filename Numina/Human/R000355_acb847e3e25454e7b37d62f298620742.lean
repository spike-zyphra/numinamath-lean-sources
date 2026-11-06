import Mathlib

/-Given that for any real number $x$, we have $f(-x) = -f(x)$, $g(-x) = g(x)$, and when $x > 0$, $f'(x) > 0$, $g'(x) > 0$, then for $x < 0$, we should have $f'(x) \quad 0$, $g'(x) \quad 0$.-/
theorem algebra_9098 {f g : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (hg : ∀ x, g (-x) = g x)
    (hfd : ∀ y : ℝ, DifferentiableAt ℝ f y) (hgd : ∀ y : ℝ, DifferentiableAt ℝ g y)
    (hpos : ∀ x > 0, deriv f x > 0 ∧ deriv g x > 0) :
    ∀ x < 0, deriv f x > 0 ∧ deriv g x < 0 := by
  intro x hx
  -- Suppose $x > 0$
  obtain ⟨fpos, gpos⟩ := hpos (-x) (Left.neg_pos_iff.mpr hx)
  -- Since -x > 0, we know that f'(-x) > 0 and g'(-x) > 0 by the assumption for positive x.
  constructor
  -- Step 1: Analyze f'(x) when x < 0
  · have hdf : deriv f x = deriv f (-x) := by
    -- We prove $f ' (x) = f ' (-x).$ firstly.
      let u := fun (y : ℝ) => (f ∘ (fun (y : ℝ) => -y)) y
      let v := fun (y : ℝ) => - (f y)
    -- let $u(x) = f(-x)$, and $v(x) = - f (x).$
      have hduv : deriv u x = deriv v x := by
          congr
          ext x
          exact hf x
    -- By assumption, $u(x) = v (x) \Rightarrow u' (x) = v' (x).$
      have h1 : deriv v x = - deriv f x := by simp only [deriv.neg', v]
    -- $v'(x) = - f '(x)$
      have h2 : deriv u x = - deriv f (-x) := by
          have hf1 : DifferentiableAt ℝ f (-x) := hfd (-x)
          have hf2 : DifferentiableAt ℝ (fun (y : ℝ) => -y) x := Differentiable.differentiableAt differentiable_neg
          have := deriv.comp (𝕜 := ℝ) (𝕜' := ℝ) (h := fun (y : ℝ) => -y) (h₂ := f) x hf1 hf2
          -- Applying compostion derivative rule to get $u'(x) = f ' (-x) \cdot -1.$
          simp only [deriv_neg'', mul_neg, mul_one] at this
          exact this
          -- Then $u'(x) = - f '(x)$
      simp_all only [neg_inj]
      --Hence $- f' (x) = -f ' (-x)$
    rwa [hdf]
    --Now $f'(x) = f ' (-x) > 0$

  -- Step 2: Analyze g'(x) when x < 0
  · have gdf : deriv g x = - deriv g (-x) := by
      let u := fun (y : ℝ) => (g ∘ (fun (y : ℝ) => -y)) y
      have hdug : deriv u x = deriv g x := by
          congr
          ext x
          exact hg x
      have h : deriv u x = - deriv g (-x) := by
          have hg1 : DifferentiableAt ℝ g (-x) := hgd (-x)
          have hg2 : DifferentiableAt ℝ (fun (y : ℝ) => -y) x := Differentiable.differentiableAt differentiable_neg
          have := deriv.comp (𝕜 := ℝ) (𝕜' := ℝ) (h := fun (y : ℝ) => -y) (h₂ := g) x hg1 hg2
          simp only [deriv_neg'', mul_neg, mul_one] at this
          exact this
      simp_all only [gt_iff_lt, Left.neg_pos_iff]
    --By the similiar arguement to the previous, $g ' (x) = -g '(-x)$
    rw [gdf]
    --Now $g ' (x) = - g '(-x)$
    simp only [Left.neg_neg_iff, gpos]
    --Hence $g' (x) < 0$
