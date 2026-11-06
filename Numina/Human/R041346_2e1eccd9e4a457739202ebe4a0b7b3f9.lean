import Mathlib

/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ that satisfy the conditions  $$ f(1+x y)-f(x+y)=f(x) f(y) \quad \text { for all } x, y \in \mathbb{R} $$  and $f(-1) \neq 0$.-/
theorem imo_a5 (f : ℝ → ℝ) :
    let property (f : ℝ → ℝ) : Prop := (∀ x y, f (1 + x * y) - f (x + y) = f x * f y) ∧ f (-1) ≠ 0
    property f ↔ ∀ x, f x = x - 1 := by
  have hquadratic_ne_zero_iff' {a b c : ℝ} (ha : a ≠ 0) :
    (∀ x, a * x ^ 2 + b * x + c ≠ 0) ↔ discrim a b c < 0 := by
    simp only [pow_two]
    constructor
    . intro h
      contrapose! h
      let d := Real.sqrt <| discrim a b c
      have : ∃ s, discrim a b c = s * s := ⟨d, Eq.symm <| Real.mul_self_sqrt h⟩
      exact exists_quadratic_eq_zero ha this
    intro h
    have : ∀ y, discrim a b c ≠ y ^ 2 := by
      intro y hy
      linarith [hy ▸ sq_nonneg y]
    exact quadratic_ne_zero_of_discrim_ne_sq this
  intro property
  dsimp [property]
  constructor
  swap
  -- Verify that $f(x)=x-1$ is a solution.
  . intro hfx
    constructor
    . intros
      simpa [hfx] using by ring
    norm_num [hfx]
  rintro ⟨hf, hfneg1⟩
  -- Let g(x)=f(x)+1.
  let g : ℝ → ℝ := fun x => f x + 1
  -- Suffices to show that g(x)=x.
  suffices ∀ x, g x = x by
    intro x
    linear_combination this x
  -- Convert hypothesis of f(x) to g(x).
  have hg x y : g (1 + x * y) - g (x + y) = (g x - 1) * (g y - 1) := by aesop
  have hgneg1 : g (-1) ≠ 1 := by aesop
  clear hf hfneg1
  -- Let C=g(-1)-1.
  set C : ℝ := g (-1) - 1 with hc
  -- It's clear that C≠0.
  have _ : C ≠ 0 := by aesop
  -- Susbstitute y=-1 to hg to get g(1-x)-g(x-1)=C(g(x)-1).
  have h1 x : g (1 - x) - g (x - 1) = C * (g x - 1) := by
    specialize hg x (-1)
    rw [← hc] at hg
    convert hg using 1
    . congr; ring
    . rw [mul_comm]
  -- Substitute x=1 to h1, we have g(1)=1.
  have hg1 : g 1 = 1 := by
    specialize h1 1
    aesop
  -- -- Substitute x=0 to h1, we have g(0)=0.
  have hg0 : g 0 = 0 := by
    specialize h1 0
    norm_num at h1
    rw [hg1, show 1 - g (-1) = -C by ring] at h1
    replace h1 : C * g 0 = 0 := by linear_combination -h1
    aesop
  -- Substitute x=2 to h1, we have g(2)=2.
  have hg2 : g 2 = 2 := by
    specialize h1 2
    norm_num at h1
    rw [hg1, ← hc] at h1
    replace h1 : C * (g 2 - 2) = 0 := by linear_combination -h1
    rw [← sub_eq_zero]
    aesop
  -- Substitute x=1-t to h1, we have g(t)-g(-t)=C*(g(1-t)-1).
  have h2 t : g t - g (-t) = C * (g (1 - t) - 1) := by
    specialize h1 (1 - t)
    norm_num at h1
    exact h1
  -- Substitute t=-t to h2, we have g(-t)-g(t)=C*(g(1+t)-1).
  have h2' t : g (-t) - g t = C * (g (1 + t) - 1) := by
    specialize h2 (-t)
    norm_num at h2
    exact h2
  -- Combine above equation, we have g(1+t)+g(1-t)=2.
  have h3 t : g (1 + t) + g (1 - t) = 2 := by
    specialize h2 t
    specialize h2' t
    have : C * (g (1 + t) + g (1 - t) - 2) = 0 := by linear_combination -h2 - h2'
    have : g (1 + t) + g (1 - t) - 2 = 0 := by aesop
    linear_combination this
  -- If u+v=1, then g(1+uv)-g(1)=(g(u)-1)(g(v)-1).
  have h4 {u v} (huv : u + v = 1) : g (1 + u * v) - g 1 = (g u - 1) * (g v - 1) := by
    specialize hg u v
    rwa [huv] at hg
  -- Similiarly, we have g(3+uv)-g(3)=(g(2-u)-1)(g(2-v)=1).
  have h4' {u v} (huv : u + v = 1) : g (3 + u * v) -g 3 = (g (2 - u) - 1) * (g (2 - v) - 1) := by
    specialize hg (2 - u) (2 - v)
    convert hg using 1
    congr 1
    . congr  1
      rw [show (2 - u) * (2 - v) = 4 - 2 * (u + v) + u * v by ring, huv]
      ring
    congr 1
    rw [show 2 - u + (2 - v) = 4 - (u + v) by ring, huv]
    norm_num
  -- Notice that from h3 we have g(1+t)+g(1-t)=2, hence g(2-u)=2-g(u).
  have h5 u : g (2 - u) = 2 - g u := by
    specialize h3 (1 - u)
    norm_num at h3
    rw [show 1 + (1 - u) = 2 - u by ring] at h3
    linear_combination h3
  -- Combine above equation, we have g(3+uv)-g(1+uv)=g(3)-g(1).
  have h6 {u v} (huv : u + v = 1) : g (3 + u * v) - g (1 + u * v) = g 3 - g 1 := by
    specialize h4 huv
    specialize h4' huv
    rw [h5 u, h5 v] at h4'
    linear_combination h4' - h4
  -- Notice that if x≤5/4 then we can write x=uv+1 where u+v=1.
  -- Hence for all x≤5/4, we have g(x+2)-g(x)=g(3)-g(1).
  have h7 {x} (hx : x ≤ 5 / 4) : g (x + 2) - g x = g 3 - g 1 := by
    have ⟨y, hy⟩ : ∃ y, y * y - 1 * y + (x - 1) = 0 := by
      by_contra h
      push_neg at h
      have : ∀ y, 1 * y ^ 2 + (-1) * y + (x - 1) ≠ 0 := by
        intro y
        convert h y using 1
        ring
      rw [hquadratic_ne_zero_iff' (by norm_num), discrim] at this
      linarith
    have ⟨z, _, hyzadd, hyzmul⟩ := vieta_formula_quadratic hy
    specialize h6 hyzadd
    rw [hyzmul] at h6
    convert h6 using 1
    congr 1
    . congr 1; ring
    . congr; ring
  -- Substitute x=0 to h7, we have g(3)=3.
  have hg3 : g 3 = 3 := by
    specialize @h7 0 (by norm_num)
    norm_num at h7
    rw [hg0, hg1, hg2] at h7
    linear_combination -h7
  -- Hence we can rewrite h7 as g(x+2)-g(x)=2.
  replace h7 {x} (hx : x ≤ 5 / 4) : g (x + 2) - g x = 2 := by
    specialize h7 hx
    norm_num [hg3, hg1] at h7
    exact h7
  -- If x>5/4, notice that g(x)+g(x-2)=2, we can also deduce that g(x+2)-g(x)=2.
  have h7' {x} (hx : 5 / 4 < x) : g (x + 2) - g x = 2 := by
    have hnegx : -x ≤ 5 / 4 := by linarith
    specialize h7 hnegx
    rw [show -x + 2 = 2 - x by ring] at h7
    have H1 : g x + g (2 - x) = 2 := by
      convert h3 (1 - x) using 1
      rw [add_comm]
      congr
      . ring
      . ring
    have H2 : g (x + 2) + g (-x) = 2 := by
      convert h3 (1 + x) using 1
      congr 1
      . congr 1
        ring
      . congr
        ring
    linear_combination H2 - H1 + h7
  -- Combine above results, we have g(x+2)-g(x)=2 for all real number x.
  replace h7 x : g (x + 2) - g x = 2 := by
    rcases le_or_lt x (5 / 4) with hx | hx
    . exact h7 hx
    . exact h7' hx
  -- We can deduce g(-x)=-g(x).
  have hgodd x : g (-x) = - g x := by
    specialize h7 x
    specialize h3 (1 + x)
    norm_num at h3
    rw [show 1 + (1 + x) = 2 + x by ring, add_comm 2 x] at h3
    linear_combination h3 - h7
  -- Substitute y=-y to hg, we have g(1-xy)-g(x-y)=(1-g(x))(1+g(y)).
  have h8 x y : g (1 - x * y) - g (x - y) = (1 - g x) * (1 + g y) := by
    specialize hg x (-y)
    rw [hgodd] at hg
    convert hg using 1
    . congr 1
      congr
      ring
    ring
  -- Similiarly, substitute x=-x to hg we have g(1-xy)+g(x-y)=(1+g(x))(1-g(y)).
  have h8' x y : g (1 - x * y) + g (x - y) = (1 + g x) * (1 - g y) := by
    specialize hg (-x) y
    rw [hgodd, show -x + y = - (x - y) by ring, hgodd, sub_eq_add_neg, neg_neg] at hg
    convert hg using 1
    . congr
      ring
    ring
  -- Combine above equation, we have g(1-xy)=1-g(x)g(y).
  replace h8 x y : g (1 - x * y) = 1 - g x * g y := by
    specialize h8 x y
    specialize h8' x y
    have : 2 * g (1 - x * y) = 2 * (1 - g x * g y) := by linear_combination h8 + h8'
    aesop
  -- Notice that g(1+xy)=1+g(x)g(y).
  have h9 x y : g (1 + x * y) = 1 + g x * g y := by
    specialize h3 (x * y)
    specialize h8 x y
    linear_combination h3 - h8
  -- We can deduce g(x+y)=g(x)+g(y)
  have hgadd x y : g (x + y) = g x + g y := by
    specialize hg x y
    specialize h9 x y
    linear_combination h9 - hg
  -- Similiarly, we can deduce g(xy)=g(x)g(y).
  have hgmul x y : g (x * y) = g x * g y := by
    specialize h9 x y
    rw [hgadd, hg1] at h9
    linear_combination h9
  -- Since g(x) is multiplicative, g(x) is nonneg for all nonneg real number x.
  have hg_nonneg_of_nonneg : ∀ x ≥ 0, g x ≥ 0 := by
    intro x hx
    rw [← Real.mul_self_sqrt hx, hgmul, ← pow_two]
    positivity
  -- Since g(x) is additivie and g(x) is nonneg for all nonneg real number, it is linear.
  -- It's clear that for all natural number n, we have g(n)=n.
  have is_linear_nat (n : ℕ) : g n = n := by
    induction' n with n ih
    . exact_mod_cast hg0
    push_cast
    rw [hgadd, ih, hg1]
  have is_linear_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : g n = n := by
    lift n to ℕ using hn
    norm_cast
    exact is_linear_nat _
  -- Similiarly, we can prove that for all integer n, we have g(n)=n.
  have is_linear_int (n : ℤ) : g n = n := by
    rcases le_or_lt 0 n with h | h
    . exact is_linear_int_of_nonneg h
    rw [show (n : ℝ) = (- (-n : ℤ) : ℝ) by norm_cast; ring, hgodd]
    rw [is_linear_int_of_nonneg]
    linarith
  -- For all integer n and real number x, we have g(nx)=ng(x).
  have gnx (n : ℕ) (x : ℝ) : g (n * x) = n * g x := by
    induction' n with n ih
    . simpa
    push_cast
    rw [add_mul, hgadd, ih, one_mul]
    ring
  -- It's obvious that g(x) is montone since g(x) is additive and 0≤g(x) for all 0≤x.
  have gmono : Monotone g := by
    intro a b hab
    suffices 0 ≤ g (b - a) by
      rw [sub_eq_add_neg, hgadd, hgodd] at this
      linarith
    apply hg_nonneg_of_nonneg
    linarith
  -- Suffices to show that for all nonneg real number x we have g(x)=x.
  suffices ∀ x, 0 ≤ x → g x = x by
    intro x
    rcases le_or_lt 0 x with h | h
    . exact this _ h
    specialize this (-x) (by linarith)
    rw [hgodd] at this
    linear_combination -this
  intro x _
  -- We split into three cases.
  rcases lt_trichotomy (g x) x with h | h | h
  swap
  -- Case(1):g(x) = x. This case is trivial.
  . exact h
  -- Case(2):g(x) < x. Since real number is archimedean, we can deduce a contradiciont from g(x) < x.
  . set d : ℝ := x - g x with hd
    have dpos : 0 < d := by rw [hd]; linarith
    have ⟨n, hn⟩ := Archimedean.arch 1 dpos
    have := gmono (show ⌊n * x⌋ ≤ n * x from Int.floor_le _)
    rw [gnx, is_linear_int] at this
    suffices n • d < 1 by linarith
    rw [nsmul_eq_mul, hd]
    suffices n * x < n * g x + 1 by linarith
    apply lt_of_lt_of_le (show n * x < ⌊n * x⌋ + 1 from Int.lt_floor_add_one _)
    simpa
  -- Case(3):x < g(x). Similiarly we can deduce a contradiction.
  set d : ℝ := g x - x with hd
  have dpos : 0 < d := by rw [hd]; linarith
  have ⟨n, hn⟩ := Archimedean.arch 1 dpos
  have := gmono (show n * x ≤ ⌈n * x⌉ from Int.le_ceil _)
  rw [gnx, is_linear_int] at this
  suffices n • d < 1 by linarith
  rw [nsmul_eq_mul, hd]
  suffices n * g x < n * x + 1 by linarith
  apply lt_of_le_of_lt this
  exact Int.ceil_lt_add_one _
