import Mathlib
lemma jjj {G : Type} [inst : Group G] (f g : G →* G) (hf : ∀ (x : G), f x = x ^ 3)
  (hg : ∀ (x : G), g x = x ^ 6) (lv : ∀ (a b : G), f a * f b = f b * f a) (x y : G) :
  g x * g y = g y * g x := by
  -- As shown earlier, $\\text{Im}(f)$ is abelian, so $uv = vu$. That is, $x^3y^3 = y^3x^3$.
  have uu := lv x y
  simp [hf] at uu
  simp [hg]
  -- now we expose the inner part
  rw [(by group : x^6 * y^6 = x^3 * (x^3 * y^3) * y^3), (by group : y^6 * x^6 = y^3 * (y^3 * x^3) * x^3), uu]
  group
  simp [mul_assoc]
  norm_cast
  simp [uu, ← mul_assoc]
  group
  norm_cast
  -- expose further
  rw [(by group : y ^ 3 * x ^ 3 * y ^ 3 * x ^ 3 = y ^ 3 * (x ^ 3 * y ^ 3) * x ^ 3), uu]
  group

/-- ## Subject III

Let $(G, \cdot)$ be a group and $f, g: G \rightarrow G, f(x)=x^{3}, g(x)=x^{6}$. Show that if $f$ and $g$ are homomorphisms and at least one of them is surjective, then $(G, \cdot)$ is an abelian group.

Cătălin Zîrnă -/
theorem algebra_118901 {G : Type} [Group G] (f g : G →* G) (hf : ∀ x, f x = x^3) (hg : ∀ x, g x = x^6) (hi : Function.Surjective f ∨ Function.Surjective g) (a b : G) : a * b = b * a := by
  have i1 := (MonoidHom.range f).inv_mem' (x := f a) (by simp)
  have i2 := (MonoidHom.range f).inv_mem' (x := f b) (by simp)
  -- We can notice that $g(x)=x^6=(x^3)^2=(f(x))^2$. This relationship is key.
  have db : ∀ x, g x = (f x)^2 := by
    intro i
    simp [hf, hg]; group
  have lv (a b : G) : f a * f b = f b * f a := by
    -- Since $g$ is a homomorphism, we have $g(xy)=g(x)g(y)$.\
    -- Using the relationship $g(x)=(f(x))^2$, we can rewrite this as:\
    -- $(f(xy))^2 = (f(x))^2 (f(y))^2$.
    have jc := g.map_mul a b
    simp [db] at jc
    /- Left multiply by $u^{-1}$ (which exists because $\\text{Im}(f)$ is a subgroup, or $u^{-1}=(f(x))^{-1}=(x^3)^{-1}=(x^{-1})^3=f(x^{-1})\\in\\text{Im}(f)$):\
    $vuv = uvv$. -/
    apply_fun (fun x => (f a)⁻¹ * x * (f b)⁻¹) at jc
    conv at jc => left; simp [pow_two, ← mul_assoc]
    conv at jc => right; simp [pow_two, ← mul_assoc]
    rw [jc]
  cases' hi with hi hi
  -- supply inverse function
  · have cn := lv (Function.invFun f a) (Function.invFun f b)
    have ri := Function.rightInverse_invFun hi
    simp [ri a, ri b] at cn
    exact cn
  -- now g is surjective, we prove g x * g y = g y * g x
  · have vv (x y : G) : g x * g y = g y * g x := by
      apply jjj <;> assumption
    have cn := vv (Function.invFun g a) (Function.invFun g b)
    have ri := Function.rightInverse_invFun hi
    simp [ri a, ri b] at cn
    exact cn
